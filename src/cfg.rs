//! Control-flow graph (CFG) abstractions and utilities.

use crate::{
    spv, AttrSet, Const, ConstDef, ConstKind, Context, ControlNode, ControlNodeDef,
    ControlNodeKind, ControlNodeOutputDecl, ControlRegion, ControlRegionDef, EntityList,
    EntityOrientedDenseMap, FuncDefBody, FxIndexMap, FxIndexSet, SelectionKind, Type, TypeKind,
    Value,
};
use itertools::{Either, Itertools};
use smallvec::SmallVec;
use std::mem;
use std::rc::Rc;

/// The control-flow graph (CFG) of a function, as control-flow instructions
/// ([`ControlInst`]s) attached to [`ControlRegion`]s, as an "action on exit", i.e.
/// "terminator" (while intra-region control-flow is strictly structured).
#[derive(Clone, Default)]
pub struct ControlFlowGraph {
    pub control_inst_on_exit_from: EntityOrientedDenseMap<ControlRegion, ControlInst>,

    // HACK(eddyb) this currently only comes from `OpLoopMerge`, and cannot be
    // inferred (because implies too strong of an ownership/uniqueness notion).
    pub loop_merge_to_loop_header: FxIndexMap<ControlRegion, ControlRegion>,
}

#[derive(Clone)]
pub struct ControlInst {
    pub attrs: AttrSet,

    pub kind: ControlInstKind,

    pub inputs: SmallVec<[Value; 2]>,

    // FIXME(eddyb) change the inline size of this to fit most instructions.
    pub targets: SmallVec<[ControlRegion; 4]>,

    /// `target_inputs[region][input_idx]` is the [`Value`] that
    /// `Value::ControlRegionInput { region, input_idx }` will get on entry,
    /// where `region` must be appear at least once in `targets` - this is a
    /// separate map instead of being part of `targets` because it reflects the
    /// limitations of φ ("phi") nodes, which (unlike "basic block arguments")
    /// cannot tell apart multiple edges with the same source and destination.
    pub target_inputs: FxIndexMap<ControlRegion, SmallVec<[Value; 2]>>,
}

#[derive(Clone)]
pub enum ControlInstKind {
    /// Reaching this point in the control-flow is undefined behavior, e.g.:
    /// * a `SelectBranch` case that's known to be impossible
    /// * after a function call, where the function never returns
    ///
    /// Optimizations can take advantage of this information, to assume that any
    /// necessary preconditions for reaching this point, are never met.
    Unreachable,

    /// Leave the current function, optionally returning a value.
    Return,

    /// Leave the current invocation, similar to returning from every function
    /// call in the stack (up to and including the entry-point), but potentially
    /// indicating a fatal error as well.
    ExitInvocation(ExitInvocationKind),

    /// Unconditional branch to a single target.
    Branch,

    /// Branch to one of several targets, chosen by a single value input.
    SelectBranch(SelectionKind),
}

#[derive(Clone)]
pub enum ExitInvocationKind {
    SpvInst(spv::Inst),
}

impl ControlFlowGraph {
    /// Iterate over all [`ControlRegion`]s making up `func_def_body`'s CFG, in
    /// reverse post-order (RPO).
    ///
    /// RPO iteration over a CFG provides certain guarantees, most importantly
    /// that SSA definitions are visited before any of their uses.
    pub fn rev_post_order(
        &self,
        func_def_body: &FuncDefBody,
    ) -> impl DoubleEndedIterator<Item = ControlRegion> {
        let mut post_order = SmallVec::<[_; 8]>::new();
        self.traverse_whole_func(
            func_def_body,
            &mut TraversalState {
                incoming_edge_counts: EntityOrientedDenseMap::new(),

                pre_order_visit: |_| {},
                post_order_visit: |region| post_order.push(region),

                // NOTE(eddyb) this doesn't impact semantics, but combined with
                // the final reversal, it should keep targets in the original
                // order in the cases when they didn't get deduplicated.
                reverse_targets: true,
            },
        );
        post_order.into_iter().rev()
    }
}

// HACK(eddyb) this only serves to disallow accessing `private_count` field of
// `IncomingEdgeCount`.
mod sealed {
    /// Opaque newtype for the count of incoming edges (into a [`ControlRegion`](crate::ControlRegion)).
    ///
    /// The private field prevents direct mutation or construction, forcing the
    /// use of [`IncomingEdgeCount::ONE`] and addition operations to produce some
    /// specific count (which would require explicit workarounds for misuse).
    #[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
    pub(super) struct IncomingEdgeCount(usize);

    impl IncomingEdgeCount {
        pub(super) const ONE: Self = Self(1);
    }

    impl std::ops::Add for IncomingEdgeCount {
        type Output = Self;
        fn add(self, other: Self) -> Self {
            Self(self.0 + other.0)
        }
    }

    impl std::ops::AddAssign for IncomingEdgeCount {
        fn add_assign(&mut self, other: Self) {
            *self = *self + other;
        }
    }
}
use sealed::IncomingEdgeCount;

struct TraversalState<PreVisit: FnMut(ControlRegion), PostVisit: FnMut(ControlRegion)> {
    incoming_edge_counts: EntityOrientedDenseMap<ControlRegion, IncomingEdgeCount>,
    pre_order_visit: PreVisit,
    post_order_visit: PostVisit,

    // FIXME(eddyb) should this be a generic parameter for "targets iterator"?
    reverse_targets: bool,
}

impl ControlFlowGraph {
    fn traverse_whole_func(
        &self,
        func_def_body: &FuncDefBody,
        state: &mut TraversalState<impl FnMut(ControlRegion), impl FnMut(ControlRegion)>,
    ) {
        let func_at_body = func_def_body.at_body();

        // Quick sanity check that this is the right CFG for `func_def_body`.
        assert!(std::ptr::eq(func_def_body.unstructured_cfg.as_ref().unwrap(), self));
        assert!(func_at_body.def().outputs.is_empty());

        self.traverse(func_def_body.body, state);
    }

    fn traverse(
        &self,
        region: ControlRegion,
        state: &mut TraversalState<impl FnMut(ControlRegion), impl FnMut(ControlRegion)>,
    ) {
        // FIXME(eddyb) `EntityOrientedDenseMap` should have an `entry` API.
        if let Some(existing_count) = state.incoming_edge_counts.get_mut(region) {
            *existing_count += IncomingEdgeCount::ONE;
            return;
        }
        state.incoming_edge_counts.insert(region, IncomingEdgeCount::ONE);

        (state.pre_order_visit)(region);

        let control_inst = self
            .control_inst_on_exit_from
            .get(region)
            .expect("cfg: missing `ControlInst`, despite having left structured control-flow");

        let targets = control_inst.targets.iter().copied();
        let targets = if state.reverse_targets {
            Either::Left(targets.rev())
        } else {
            Either::Right(targets)
        };
        for target in targets {
            self.traverse(target, state);
        }

        (state.post_order_visit)(region);
    }
}

/// Minimal loop analysis, based on Tarjan's SCC (strongly connected components)
/// algorithm, applied recursively (for every level of loop nesting).
///
/// Here "minimal" means that each loops is the smallest CFG subgraph possible
/// (excluding any control-flow paths that cannot reach a backedge and cycle),
/// i.e. each loop is a CFG SCC (strongly connected component).
///
/// These "minimal loops" contrast with the "maximal loops" that the greedy
/// architecture of the structurizer would naively produce, with the main impact
/// of the difference being where loop exits (`break`s) "merge" (or "reconverge"),
/// which SPIR-V encodes via `OpLoopMerge`, and is significant for almost anything
/// where shared memory and/or subgroup ops can allow observing when invocations
/// "wait for others in the subgroup to exit the loop" (or when they fail to wait).
///
/// This analysis was added to because of two observations wrt "reconvergence":
/// 1. syntactic loops (from some high-level language), when truly structured
///    (i.e. only using `while`/`do`-`while` exit conditions, not `break` etc.),
///    *always* map to "minimal loops" on a CFG, as the only loop exit edge is
///    built-in, and no part of the syntactic "loop body" can be its successor
/// 2. more pragmatically, compiling shader languages to SPIR-V seems to (almost?)
///    always *either* fully preserve syntactic loops (via SPIR-V `OpLoopMerge`),
///    *or* structurize CFGs in a way that produces "minimal loops", which can
///    be misleading with explicit `break`s (moving user code from just before
///    the `break` to after the loop), but is less impactful than "maximal loops"
struct LoopFinder<'a> {
    cfg: &'a ControlFlowGraph,

    // FIXME(eddyb) this feels a bit inefficient (are many-exit loops rare?).
    loop_header_to_exit_targets: FxIndexMap<ControlRegion, FxIndexSet<ControlRegion>>,

    /// SCC accumulation stack, where CFG nodes collect during the depth-first
    /// traversal, and are only popped when their "SCC root" (loop header) is
    /// (note that multiple SCCs on the stack does *not* indicate SCC nesting,
    /// but rather a path between two SCCs, i.e. a loop *following* another).
    scc_stack: Vec<ControlRegion>,
    /// Per-CFG-node traversal state (often just pointing to a `scc_stack` slot).
    scc_state: EntityOrientedDenseMap<ControlRegion, SccState>,
}

// FIXME(eddyb) make `Option<Option<SccStackIdx>>` the same size somehow.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct SccStackIdx(u32);

#[derive(PartialEq, Eq)]
enum SccState {
    /// CFG node has been reached and ended up somewhere on the `scc_stack`,
    /// where it will remain after the SCC it's part of will be completed.
    Pending(SccStackIdx),

    /// CFG node had been reached once, but is no longer on the `scc_stack`, its
    /// parent SCC having been completed (or it wasn't in an SCC to begin with).
    Complete,
}

impl<'a> LoopFinder<'a> {
    fn new(cfg: &'a ControlFlowGraph) -> Self {
        Self {
            cfg,
            loop_header_to_exit_targets: FxIndexMap::default(),
            scc_stack: vec![],
            scc_state: EntityOrientedDenseMap::new(),
        }
    }

    /// Tarjan's SCC algorithm works by computing the "earliest" reachable node,
    /// from every node (often using the name `lowlink`), which will be equal
    /// to the origin node itself iff that node is an "SCC root" (loop header),
    /// and always point to an "earlier" node if a cycle (via loop backedge) was
    /// found from somewhere else in the SCC (i.e. from inside the loop body).
    ///
    /// Here we track stack indices (as the stack order is the traversal order),
    /// and distinguish the acyclic case to avoid treating most nodes as self-loops.
    fn find_earliest_scc_root_of(&mut self, node: ControlRegion) -> Option<SccStackIdx> {
        let state_entry = self.scc_state.entry(node);
        if let Some(state) = &state_entry {
            return match *state {
                SccState::Pending(scc_stack_idx) => Some(scc_stack_idx),
                SccState::Complete => None,
            };
        }
        let scc_stack_idx = SccStackIdx(self.scc_stack.len().try_into().unwrap());
        self.scc_stack.push(node);
        *state_entry = Some(SccState::Pending(scc_stack_idx));

        let control_inst = self
            .cfg
            .control_inst_on_exit_from
            .get(node)
            .expect("cfg: missing `ControlInst`, despite having left structured control-flow");

        let earliest_scc_root = control_inst
            .targets
            .iter()
            .flat_map(|&target| {
                // HACK(eddyb) if one of the edges is already known to be a loop exit
                // (from `OpLoopMerge` specifically), treat it almost like a backedge,
                // but with the additional requirement that the loop header is already
                // on the stack (i.e. this `node` is reachable from that loop header).
                let root_candidate_from_loop_merge =
                    self.cfg.loop_merge_to_loop_header.get(&target).and_then(|&loop_header| {
                        match self.scc_state.get(loop_header) {
                            Some(&SccState::Pending(scc_stack_idx)) => Some(scc_stack_idx),
                            _ => None,
                        }
                    });

                self.find_earliest_scc_root_of(target)
                    .into_iter()
                    .chain(root_candidate_from_loop_merge)
            })
            .min();

        // If this node has been chosen as the root of an SCC, complete that SCC.
        if earliest_scc_root == Some(scc_stack_idx) {
            let scc_start = scc_stack_idx.0 as usize;

            // It's now possible to find all the loop exits: they're all the
            // edges from nodes of this SCC (loop) to nodes not in the SCC.
            let target_in_scc = |target| match self.scc_state.get(target) {
                Some(&SccState::Pending(i)) => i >= scc_stack_idx,
                _ => false,
            };
            self.loop_header_to_exit_targets.insert(
                node,
                self.scc_stack[scc_start..]
                    .iter()
                    .flat_map(|&scc_node| {
                        self.cfg.control_inst_on_exit_from[scc_node]
                            .targets
                            .iter()
                            .copied()
                            .filter(|&target| !target_in_scc(target))
                    })
                    .collect(),
            );

            // Find nested loops by marking *only* the loop header as complete,
            // clearing loop body nodes' state, and recursing on them: all the
            // nodes outside the loop (otherwise reachable from within), and the
            // loop header itself, are already marked as complete, meaning that
            // all exits and backedges will be ignored, and the recursion will
            // only find more SCCs within the loop body (i.e. nested loops).
            self.scc_state[node] = SccState::Complete;
            let loop_body_range = scc_start + 1..self.scc_stack.len();
            for &scc_node in &self.scc_stack[loop_body_range.clone()] {
                self.scc_state.remove(scc_node);
            }
            for i in loop_body_range.clone() {
                self.find_earliest_scc_root_of(self.scc_stack[i]);
            }
            assert_eq!(self.scc_stack.len(), loop_body_range.end);

            // Remove the entire SCC from the accumulation stack all at once.
            self.scc_stack.truncate(scc_start);

            return None;
        }

        // Not actually in an SCC at all, just some node outside any CFG cycles.
        if earliest_scc_root.is_none() {
            assert!(self.scc_stack.pop() == Some(node));
            self.scc_state[node] = SccState::Complete;
        }

        earliest_scc_root
    }
}

#[allow(rustdoc::private_intra_doc_links)]
/// Control-flow "structurizer", which attempts to convert as much of the CFG
/// as possible into structural control-flow (regions).
///
/// See [`StructurizeRegionState`]'s docs for more details on the algorithm.
//
// FIXME(eddyb) document this (instead of having it on `StructurizeRegionState`).
//
// NOTE(eddyb) CFG structurizer has these stages (per-region):
//   1. absorb any deferred exits that finally have 100% refcount
//   2. absorb a single backedge deferred exit to the same region
//
//   What we could add is a third step, to handle irreducible controlflow:
//   3. check for groups of exits that have fully satisfied refcounts iff the
//     rest of the exits in the group are all added together - if so, the group
//     is *irreducible* and a single "loop header" can be created, that gets
//     the group of deferred exits, and any other occurrence of the deferred
//     exits (in either the original region, or amongst themselves) can be
//     replaced with the "loop header" with appropriate selector inputs
//
//   Sadly 3. requires a bunch of tests that are hard to craft (can rustc MIR
//   even end up in the right shape?).
//   OpenCL has `goto` so maybe it can also be used for this worse-than-diamond
//   example: `entry -> a,b,d` `a,b -> c` `a,b,c -> d` `a,b,c,d <-> a,b,c,d`
//   (the goal is avoiding a "flat group", i.e. where there is only one step
//   between every exit in the group and another exit)
pub struct Structurizer<'a> {
    cx: &'a Context,

    /// Scrutinee type for [`SelectionKind::BoolCond`].
    type_bool: Type,

    /// Scrutinee value for [`SelectionKind::BoolCond`], for the "then" case.
    const_true: Const,

    /// Scrutinee value for [`SelectionKind::BoolCond`], for the "else" case.
    const_false: Const,

    func_def_body: &'a mut FuncDefBody,

    // FIXME(eddyb) this feels a bit inefficient (are many-exit loops rare?).
    loop_header_to_exit_targets: FxIndexMap<ControlRegion, FxIndexSet<ControlRegion>>,

    // HACK(eddyb) this also tracks all of `loop_header_to_exit_targets`, as
    // "false edges" from every loop header to each exit target of that loop,
    // which structurizing that loop consumes to "unlock" its own exits.
    incoming_edge_counts_including_loop_exits:
        EntityOrientedDenseMap<ControlRegion, IncomingEdgeCount>,

    /// Keyed by the input to `structurize_region_from` (the start [`ControlRegion`]),
    /// and describing the state of that partial structurization step.
    ///
    /// See also [`StructurizeRegionState`]'s docs.
    //
    // FIXME(eddyb) use `EntityOrientedDenseMap` (which lacks iteration by design).
    structurize_region_state: FxIndexMap<ControlRegion, StructurizeRegionState>,

    /// Accumulated replacements (caused by `target_inputs`s), i.e.:
    /// `Value::ControlRegionInput { region, input_idx }` must be replaced
    /// with `control_region_input_replacements[region][input_idx]`, as
    /// the original `region` cannot have be directly reused.
    control_region_input_replacements: EntityOrientedDenseMap<ControlRegion, SmallVec<[Value; 2]>>,
}

/// The state of one `structurize_region_from` invocation (keyed on its start
/// [`ControlRegion`] in [`Structurizer`]) and its [`PartialControlRegion`] output.
///
/// There is a fourth (or 0th) implicit state, which is where nothing has yet
/// observed some region, and [`Structurizer`] isn't tracking it at all.
//
// FIXME(eddyb) make the 0th state explicit and move `incoming_edge_counts` to it.
enum StructurizeRegionState {
    /// Structurization is still running, and observing this is a cycle.
    InProgress,

    /// Structurization completed, and this region can now be claimed.
    Ready {
        /// If this region had backedges (targeting its start [`ControlRegion`]),
        /// their bundle is taken from the region's [`DeferredEdgeBundleSet`],
        /// and kept in this field instead (for simpler/faster access).
        ///
        /// Claiming a region with backedges can combine them with the bundled
        /// edges coming into the CFG cycle from outside, and instead of failing
        /// due to the latter not being enough to claim the region on their own,
        /// actually perform loop structurization.
        backedge: Option<DeferredEdgeBundle<()>>,

        region: PartialControlRegion,
    },

    /// Region was claimed (by an [`IncomingEdgeBundle`], with the appropriate
    /// total [`IncomingEdgeCount`], minus any `consumed_backedges`), and has
    /// since likely been incorporated as part of some larger region.
    Claimed,
}

/// An "(incoming) edge bundle" is a subset of the edges into a single `target`.
///
/// When `accumulated_count` reaches the total [`IncomingEdgeCount`] for `target`,
/// that [`IncomingEdgeBundle`] is said to "effectively own" its `target` (akin to
/// the more commonly used CFG domination relation, but more "incremental").
///
/// **Note**: `target` has a generic type `T` to reduce redundancy when it's
/// already implied (e.g. by the key in [`DeferredEdgeBundleSet`]'s map).
struct IncomingEdgeBundle<T> {
    target: T,
    accumulated_count: IncomingEdgeCount,

    /// The [`Value`]s that `Value::ControlRegionInput { region, .. }` will get
    /// on entry into `region`, through this "edge bundle".
    target_inputs: SmallVec<[Value; 2]>,
}

/// A "deferred (incoming) edge bundle" is an [`IncomingEdgeBundle`] that cannot
/// be structurized immediately, but instead waits for its `accumulated_count`
/// to reach the full count of its `target`, before it can grafted into some
/// structured control-flow region.
///
/// While in the "deferred" state, its can accumulate a non-trivial `condition`,
/// every time it's propagated to an "outer" region, e.g. for this pseudocode:
/// ```text
/// if a {
///     branch => label1
/// } else {
///     if b {
///         branch => label1
///     }
/// }
/// ```
/// the deferral of branches to `label1` will result in:
/// ```text
/// label1_condition = if a {
///     true
/// } else {
///     if b {
///         true
///     } else {
///         false
///     }
/// }
/// if label1_condition {
///     branch => label1
/// }
/// ```
/// which could theoretically be simplified (after the [`Structurizer`]) to:
/// ```text
/// label1_condition = a | b
/// if label1_condition {
///     branch => label1
/// }
/// ```
///
/// **Note**: `edge_bundle.target` has a generic type `T` to reduce redundancy
/// when it's already implied (e.g. by the key in [`DeferredEdgeBundleSet`]'s map).
struct DeferredEdgeBundle<T> {
    condition: LazyCond,
    edge_bundle: IncomingEdgeBundle<T>,
}

impl<T> DeferredEdgeBundle<T> {
    fn into_target_keyed_kv_pair(self) -> (T, DeferredEdgeBundle<()>) {
        let DeferredEdgeBundle {
            condition,
            edge_bundle: IncomingEdgeBundle { target, accumulated_count, target_inputs },
        } = self;
        (
            target,
            DeferredEdgeBundle {
                condition,
                edge_bundle: IncomingEdgeBundle { target: (), accumulated_count, target_inputs },
            },
        )
    }
}

/// A recipe for computing a control-flow-sensitive (boolean) condition [`Value`],
/// potentially requiring merging through an arbitrary number of `Select`s
/// (via per-case outputs and [`Value::ControlNodeOutput`], for each `Select`).
///
/// This should largely be equivalent to eagerly generating all region outputs
/// that might be needed, and then removing the unused ones, but this way we
/// never generate unused outputs, and can potentially even optimize away some
/// redundant dataflow (e.g. `if cond { true } else { false }` is just `cond`).
enum LazyCond {
    // FIXME(eddyb) remove `False` in favor of `Option<LazyCond>`?
    False,
    True,
    MergeSelect {
        control_node: ControlNode,
        // FIXME(eddyb) the lowest level of this ends up with a `Vec` containing
        // only `LazyCond::{False,True}`, and that could more easily be expressed
        // as e.g. a bitset? (or even `SmallVec<[bool; 16]>`, tho that's silly)
        per_case_conds: Vec<LazyCond>,
    },
}

/// A target for one of the edge bundles in a [`DeferredEdgeBundleSet`], mostly
/// separate from [`ControlRegion`] to allow expressing returns as well.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
enum DeferredTarget {
    Region(ControlRegion),

    /// Structured "return" out of the function (with `target_inputs` used for
    /// the function body `output`s, i.e. inputs of [`ControlInstKind::Return`]).
    Return,
}

/// Set of [`DeferredEdgeBundle`]s, uniquely keyed by their `target`s.
//
// FIXME(eddyb) consider implementing `FromIterator<DeferredEdgeBundle<DeferredTarget>>`.
struct DeferredEdgeBundleSet {
    target_to_deferred: FxIndexMap<DeferredTarget, DeferredEdgeBundle<()>>,
}

/// Partially structurized [`ControlRegion`], the result of combining together
/// several smaller [`ControlRegion`]s, based on CFG edges between them.
struct PartialControlRegion {
    // FIXME(eddyb) keep this in the original `ControlRegion` instead.
    children: EntityList<ControlNode>,

    /// The transitive targets which can't be claimed into the [`ControlRegion`]
    /// remain as deferred exits, and will blocking further structurization until
    /// all other edges to those same targets are gathered together.
    ///
    /// **Note**: this will only be empty if the [`ControlRegion`] never exits,
    /// i.e. it has divergent control-flow (such as an infinite loop), as any
    /// control-flow path that can (eventually) return from the function, will
    /// end up using a deferred target for that (see [`DeferredTarget::Return`]).
    deferred_edges: DeferredEdgeBundleSet,
}

impl<'a> Structurizer<'a> {
    pub fn new(cx: &'a Context, func_def_body: &'a mut FuncDefBody) -> Self {
        // FIXME(eddyb) SPIR-T should have native booleans itself.
        let wk = &spv::spec::Spec::get().well_known;
        let type_bool = cx.intern(TypeKind::SpvInst {
            spv_inst: wk.OpTypeBool.into(),
            type_and_const_inputs: [].into_iter().collect(),
        });
        let const_true = cx.intern(ConstDef {
            attrs: AttrSet::default(),
            ty: type_bool,
            kind: ConstKind::SpvInst {
                spv_inst_and_const_inputs: Rc::new((
                    wk.OpConstantTrue.into(),
                    [].into_iter().collect(),
                )),
            },
        });
        let const_false = cx.intern(ConstDef {
            attrs: AttrSet::default(),
            ty: type_bool,
            kind: ConstKind::SpvInst {
                spv_inst_and_const_inputs: Rc::new((
                    wk.OpConstantFalse.into(),
                    [].into_iter().collect(),
                )),
            },
        });

        let (loop_header_to_exit_targets, incoming_edge_counts_including_loop_exits) =
            func_def_body
                .unstructured_cfg
                .as_ref()
                .map(|cfg| {
                    let loop_header_to_exit_targets = {
                        let mut loop_finder = LoopFinder::new(cfg);
                        loop_finder.find_earliest_scc_root_of(func_def_body.body);
                        loop_finder.loop_header_to_exit_targets
                    };

                    let mut state = TraversalState {
                        incoming_edge_counts: EntityOrientedDenseMap::new(),

                        pre_order_visit: |_| {},
                        post_order_visit: |_| {},
                        reverse_targets: false,
                    };
                    cfg.traverse_whole_func(func_def_body, &mut state);

                    // HACK(eddyb) treat loop exits as "false edges", that their
                    // respective loop header "owns", such that structurization
                    // naturally stops at those loop exits, instead of continuing
                    // greedily into the loop exterior (producing "maximal loops").
                    for loop_exit_targets in loop_header_to_exit_targets.values() {
                        for &exit_target in loop_exit_targets {
                            *state
                                .incoming_edge_counts
                                .entry(exit_target)
                                .get_or_insert(Default::default()) += IncomingEdgeCount::ONE;
                        }
                    }

                    (loop_header_to_exit_targets, state.incoming_edge_counts)
                })
                .unwrap_or_default();

        Self {
            cx,
            type_bool,
            const_true,
            const_false,

            func_def_body,

            loop_header_to_exit_targets,
            incoming_edge_counts_including_loop_exits,

            structurize_region_state: FxIndexMap::default(),
            control_region_input_replacements: EntityOrientedDenseMap::new(),
        }
    }

    pub fn structurize_func(mut self) {
        // Don't even try to re-structurize functions.
        if self.func_def_body.unstructured_cfg.is_none() {
            return;
        }

        let mut body_region =
            self.claim_or_defer_single_edge(self.func_def_body.body, SmallVec::new());

        if body_region.deferred_edges.target_to_deferred.len() == 1 {
            // Structured return, the function is fully structurized.
            //
            // FIXME(eddyb) also support structured return when the whole body
            // is divergent, by generating undef constants (needs access to the
            // whole `FuncDecl`, not just `FuncDefBody`, to get the right types).
            if let Some(deferred_return) =
                body_region.deferred_edges.target_to_deferred.remove(&DeferredTarget::Return)
            {
                let body_def = self.func_def_body.at_mut_body().def();
                body_def.children = body_region.children;
                body_def.outputs = deferred_return.edge_bundle.target_inputs;
                self.func_def_body.unstructured_cfg = None;

                self.apply_value_replacements();
                return;
            }
        }

        // Repair all the regions that remain unclaimed, including the body.
        let structurize_region_state =
            mem::take(&mut self.structurize_region_state).into_iter().chain([(
                self.func_def_body.body,
                StructurizeRegionState::Ready { region: body_region, backedge: None },
            )]);
        for (target, state) in structurize_region_state {
            if let StructurizeRegionState::Ready { mut region, backedge } = state {
                // Undo `backedge` extraction from deferred edges, if needed.
                if let Some(backedge) = backedge {
                    assert!(
                        region
                            .deferred_edges
                            .target_to_deferred
                            .insert(DeferredTarget::Region(target), backedge)
                            .is_none()
                    );
                }

                self.repair_unclaimed_region(target, region);
            }
        }

        self.apply_value_replacements();
    }

    /// The last step of structurization is processing bulk replacements
    /// collected while structurizing (like `control_region_input_replacements`).
    fn apply_value_replacements(self) {
        // FIXME(eddyb) maybe this should be provided by `transform`.
        use crate::transform::*;
        struct ReplaceValueWith<F>(F);
        impl<F: Fn(Value) -> Option<Value>> Transformer for ReplaceValueWith<F> {
            fn transform_value_use(&mut self, v: &Value) -> Transformed<Value> {
                self.0(*v).map_or(Transformed::Unchanged, Transformed::Changed)
            }
        }

        self.func_def_body.inner_in_place_transform_with(&mut ReplaceValueWith(|v| match v {
            Value::ControlRegionInput { region, input_idx } => {
                Some(self.control_region_input_replacements.get(region)?[input_idx as usize])
            }
            _ => None,
        }));
    }

    fn claim_or_defer_single_edge(
        &mut self,
        target: ControlRegion,
        target_inputs: SmallVec<[Value; 2]>,
    ) -> PartialControlRegion {
        self.try_claim_edge_bundle(IncomingEdgeBundle {
            target,
            accumulated_count: IncomingEdgeCount::ONE,
            target_inputs,
        })
        .unwrap_or_else(|deferred| {
            let (deferred_target, deferred) = deferred.into_target_keyed_kv_pair();
            PartialControlRegion {
                children: EntityList::empty(),
                deferred_edges: DeferredEdgeBundleSet {
                    target_to_deferred: [(DeferredTarget::Region(deferred_target), deferred)]
                        .into_iter()
                        .collect(),
                },
            }
        })
    }

    fn try_claim_edge_bundle(
        &mut self,
        mut edge_bundle: IncomingEdgeBundle<ControlRegion>,
    ) -> Result<PartialControlRegion, DeferredEdgeBundle<ControlRegion>> {
        let target = edge_bundle.target;

        // Always attempt structurization before checking the `IncomingEdgeCount`,
        // to be able to make use of backedges (if any were found).
        if self.structurize_region_state.get(&target).is_none() {
            self.structurize_region_from(target);
        }

        let backedge = match &self.structurize_region_state[&target] {
            // This `try_claim_edge_bundle` call is itself a backedge, and it's
            // coherent to not let any of them claim the loop itself, and only
            // allow claiming the whole loop (if successfully structurized).
            StructurizeRegionState::InProgress => None,

            StructurizeRegionState::Ready { backedge, .. } => backedge.as_ref(),

            StructurizeRegionState::Claimed => {
                unreachable!("cfg::Structurizer::try_claim_edge_bundle: already claimed");
            }
        };
        let backedge_count = backedge.map(|e| e.edge_bundle.accumulated_count).unwrap_or_default();

        if self.incoming_edge_counts_including_loop_exits[target]
            != edge_bundle.accumulated_count + backedge_count
        {
            return Err(DeferredEdgeBundle { condition: LazyCond::True, edge_bundle });
        }

        let state =
            self.structurize_region_state.insert(target, StructurizeRegionState::Claimed).unwrap();

        let (backedge, mut region) = match state {
            StructurizeRegionState::InProgress => unreachable!(
                "cfg::Structurizer::try_claim_edge_bundle: cyclic calls \
                 should not get this far"
            ),

            StructurizeRegionState::Ready { backedge, region } => (backedge, region),

            StructurizeRegionState::Claimed => {
                // Handled above.
                unreachable!()
            }
        };

        // If the target contains any backedge to itself, that's a loop, with:
        // * entry: `edge_bundle` (unconditional, i.e. `do`-`while`-like)
        // * body: `region.children`
        // * repeat ("continue") edge: `backedge` (with its `condition`)
        // * exit ("break") edges: `region.successor` (must be `Deferred`)
        if let Some(backedge) = backedge {
            let DeferredEdgeBundle { condition: repeat_condition, edge_bundle: backedge } =
                backedge;

            // If the body starts at a region with any `inputs`, receiving values
            // from both the loop entry and the backedge, that has to become
            // "loop state" (with values being passed to `body` `inputs`, i.e.
            // the structurized `body` region as a whole takes the same `inputs`).
            let body_inputs: SmallVec<[_; 2]> = self.func_def_body.at(target).def().inputs.clone();
            let initial_inputs = edge_bundle.target_inputs;
            let body_outputs = backedge.target_inputs;
            assert_eq!(initial_inputs.len(), body_inputs.len());
            assert_eq!(body_outputs.len(), body_inputs.len());

            let body = self.func_def_body.control_regions.define(
                self.cx,
                ControlRegionDef {
                    inputs: body_inputs,
                    children: region.children,
                    outputs: body_outputs,
                },
            );

            // The last step of turning `edge_bundle` into the complete merge of
            // the loop entry and its backedge, is to supply the structured
            // `body` `inputs` as the `target_inputs`, so that they can be
            // inserted into `control_region_input_replacements` below.
            //
            // FIXME(eddyb) if the original body region (`target`) were kept,
            // it would remove the need for all of this rewriting.
            edge_bundle.target_inputs = initial_inputs
                .iter()
                .enumerate()
                .map(|(input_idx, _)| Value::ControlRegionInput {
                    region: body,
                    input_idx: input_idx.try_into().unwrap(),
                })
                .collect();

            let repeat_condition = self.materialize_lazy_cond(repeat_condition);
            let loop_node = self.func_def_body.control_nodes.define(
                self.cx,
                ControlNodeDef {
                    kind: ControlNodeKind::Loop { initial_inputs, body, repeat_condition },
                    outputs: [].into_iter().collect(),
                }
                .into(),
            );

            // Replace the region with the whole loop, any exits out of the loop
            // being encoded in `region.deferred_*`.
            region.children = EntityList::empty();
            region.children.insert_last(loop_node, &mut self.func_def_body.control_nodes);

            // HACK(eddyb) we've treated loop exits as extra "false edges", so
            // here they have to be added to the loop (potentially unlocking
            // structurization to the outside of the loop, in the caller).
            if let Some(exit_targets) = self.loop_header_to_exit_targets.get(&target) {
                for &exit_target in exit_targets {
                    // FIXME(eddyb) what if this is `None`, is that impossible?
                    if let Some(deferred) = region
                        .deferred_edges
                        .target_to_deferred
                        .get_mut(&DeferredTarget::Region(exit_target))
                    {
                        deferred.edge_bundle.accumulated_count += IncomingEdgeCount::ONE;
                    }
                }
            }
        }

        if !edge_bundle.target_inputs.is_empty() {
            self.control_region_input_replacements.insert(target, edge_bundle.target_inputs);
        }

        Ok(region)
    }

    /// Structurize a region starting from `unstructured_region`, and extending
    /// it (by combining the smaller [`ControlRegion`]s) as much as possible into
    /// the CFG (likely everything dominated by `unstructured_region`).
    ///
    /// The output of this process is stored in, and any other bookkeeping is
    /// done through, `self.structurize_region_state[unstructured_region]`.
    ///
    /// See also [`StructurizeRegionState`]'s docs.
    fn structurize_region_from(&mut self, unstructured_region: ControlRegion) {
        {
            let old_state = self
                .structurize_region_state
                .insert(unstructured_region, StructurizeRegionState::InProgress);
            if let Some(old_state) = old_state {
                unreachable!(
                    "cfg::Structurizer::structurize_region_from: \
                     already {}, when attempting to start structurization",
                    match old_state {
                        StructurizeRegionState::InProgress => "in progress (cycle detected)",
                        StructurizeRegionState::Ready { .. } => "completed",
                        StructurizeRegionState::Claimed => "claimed",
                    }
                );
            }
        }

        let control_inst = self
            .func_def_body
            .unstructured_cfg
            .as_mut()
            .unwrap()
            .control_inst_on_exit_from
            .remove(unstructured_region)
            .expect(
                "cfg::Structurizer::structurize_region_from: missing \
                   `ControlInst` (CFG wasn't unstructured in the first place?)",
            );

        /// Marker error type for unhandled [`ControlInst`]s below.
        struct UnsupportedControlInst(ControlInst);

        let region_from_control_inst = {
            let ControlInst { attrs, kind, inputs, targets, target_inputs } = control_inst;

            // FIXME(eddyb) this loses `attrs`.
            let _ = attrs;

            let child_regions: SmallVec<[_; 8]> = targets
                .iter()
                .map(|&target| {
                    self.claim_or_defer_single_edge(
                        target,
                        target_inputs.get(&target).cloned().unwrap_or_default(),
                    )
                })
                .collect();

            match kind {
                ControlInstKind::Unreachable => {
                    assert_eq!((inputs.len(), child_regions.len()), (0, 0));

                    // FIXME(eddyb) this may result in lost optimizations over
                    // actually encoding it in `ControlNode`/`ControlRegion`
                    // (e.g. a new `ControlKind`, or replacing region `outputs`),
                    // but it's simpler to handle it like this.
                    Ok(PartialControlRegion {
                        children: EntityList::empty(),
                        deferred_edges: DeferredEdgeBundleSet {
                            target_to_deferred: [].into_iter().collect(),
                        },
                    })
                }

                ControlInstKind::ExitInvocation(_) => {
                    assert_eq!(child_regions.len(), 0);

                    // FIXME(eddyb) introduce equivalent `ControlNodeKind` for these.
                    Err(UnsupportedControlInst(ControlInst {
                        attrs,
                        kind,
                        inputs,
                        targets,
                        target_inputs,
                    }))
                }

                ControlInstKind::Return => {
                    assert_eq!(child_regions.len(), 0);

                    Ok(PartialControlRegion {
                        children: EntityList::empty(),
                        deferred_edges: DeferredEdgeBundleSet {
                            target_to_deferred: [DeferredEdgeBundle {
                                condition: LazyCond::True,
                                edge_bundle: IncomingEdgeBundle {
                                    accumulated_count: IncomingEdgeCount::default(),
                                    target: DeferredTarget::Return,
                                    target_inputs: inputs,
                                },
                            }
                            .into_target_keyed_kv_pair()]
                            .into_iter()
                            .collect(),
                        },
                    })
                }

                ControlInstKind::Branch => {
                    assert_eq!((inputs.len(), child_regions.len()), (0, 1));

                    Ok(child_regions.into_iter().next().unwrap())
                }

                ControlInstKind::SelectBranch(kind) => {
                    assert_eq!(inputs.len(), 1);

                    let scrutinee = inputs[0];

                    Ok(self.structurize_select(kind, scrutinee, child_regions))
                }
            }
        };

        let region_from_control_inst =
            region_from_control_inst.unwrap_or_else(|UnsupportedControlInst(control_inst)| {
                // HACK(eddyb) this only remains used for `ExitInvocation`.
                assert!(control_inst.targets.is_empty());

                // HACK(eddyb) attach the unsupported `ControlInst` to a fresh
                // new "proxy" `ControlRegion`, that can then be the target of
                // a deferred edge, specially crafted to be unclaimable.
                let proxy = self.func_def_body.control_regions.define(
                    self.cx,
                    ControlRegionDef {
                        inputs: [].into_iter().collect(),
                        children: EntityList::empty(),
                        outputs: [].into_iter().collect(),
                    },
                );
                self.func_def_body
                    .unstructured_cfg
                    .as_mut()
                    .unwrap()
                    .control_inst_on_exit_from
                    .insert(proxy, control_inst);
                self.structurize_region_state.insert(proxy, StructurizeRegionState::InProgress);
                self.incoming_edge_counts_including_loop_exits
                    .insert(proxy, IncomingEdgeCount::ONE);
                let deferred_proxy = DeferredEdgeBundle {
                    condition: LazyCond::True,
                    edge_bundle: IncomingEdgeBundle {
                        target: DeferredTarget::Region(proxy),
                        accumulated_count: IncomingEdgeCount::default(),
                        target_inputs: [].into_iter().collect(),
                    },
                };

                PartialControlRegion {
                    children: EntityList::empty(),
                    deferred_edges: DeferredEdgeBundleSet {
                        target_to_deferred: [deferred_proxy]
                            .into_iter()
                            .map(|d| d.into_target_keyed_kv_pair())
                            .collect(),
                    },
                }
            });

        // Prepend `unstructured_region`'s children to `region_from_control_inst`.
        let mut region = {
            let mut children = self.func_def_body.at(unstructured_region).def().children;

            children
                .append(region_from_control_inst.children, &mut self.func_def_body.control_nodes);

            // HACK(eddyb) this updates `unstructured_region` just in case
            // `repair_unclaimed_region` needs to use it again. But it would be
            // better if `PartialControlRegion` didn't have a `children` copy.
            self.func_def_body.at_mut(unstructured_region).def().children = children;

            PartialControlRegion { children, ..region_from_control_inst }
        };

        // Try to resolve deferred edges that may have accumulated, and keep
        // going until there's no more deferred edges that can be claimed.
        let try_claim_any_deferred_edge =
            |this: &mut Self, deferred_edges: &mut DeferredEdgeBundleSet| {
                // FIXME(eddyb) this should try to take as many edges as possible,
                // and incorporate them all at once, potentially with a switch instead
                // of N individual branches with their own booleans etc.
                for (i, (&deferred_target, deferred)) in
                    deferred_edges.target_to_deferred.iter_mut().enumerate()
                {
                    let deferred_target = match deferred_target {
                        DeferredTarget::Region(target) => target,
                        DeferredTarget::Return => continue,
                    };

                    // HACK(eddyb) "take" `deferred.edge_bundle` so it can be
                    // passed to `try_claim_edge_bundle` (and put back if `Err`).
                    let DeferredEdgeBundle { condition: _, ref mut edge_bundle } = *deferred;
                    let taken_edge_bundle = IncomingEdgeBundle {
                        target: deferred_target,
                        accumulated_count: edge_bundle.accumulated_count,
                        target_inputs: mem::take(&mut edge_bundle.target_inputs),
                    };

                    match this.try_claim_edge_bundle(taken_edge_bundle) {
                        Ok(claimed_region) => {
                            // FIXME(eddyb) should this use `swap_remove_index`?
                            let (_, DeferredEdgeBundle { condition, edge_bundle: _ }) =
                                deferred_edges.target_to_deferred.shift_remove_index(i).unwrap();
                            return Some((condition, claimed_region));
                        }

                        // Put back the `IncomingEdgeBundle` and keep looking.
                        Err(new_deferred) => {
                            let (new_deferred_target, new_deferred) =
                                new_deferred.into_target_keyed_kv_pair();
                            assert!(new_deferred_target == deferred_target);
                            *edge_bundle = new_deferred.edge_bundle;
                        }
                    }
                }
                None
            };
        while let Some((condition, then_region)) =
            try_claim_any_deferred_edge(self, &mut region.deferred_edges)
        {
            let else_region = PartialControlRegion { children: EntityList::empty(), ..region };
            let else_is_unreachable = else_region.deferred_edges.target_to_deferred.is_empty();

            // `then_region` is only taken if `condition` holds, except that
            // `condition` can be ignored when `else_region` is unreachable.
            let mut merged_region = if else_is_unreachable {
                then_region
            } else {
                let condition = self.materialize_lazy_cond(condition);
                self.structurize_select(
                    SelectionKind::BoolCond,
                    condition,
                    [then_region, else_region].into_iter().collect(),
                )
            };

            // Prepend the original children to the freshly merged region.
            merged_region.children.prepend(region.children, &mut self.func_def_body.control_nodes);

            region = merged_region;
        }

        // Try to extract (deferred) backedges (which later get turned into loops).
        let backedge = region
            .deferred_edges
            .target_to_deferred
            .remove(&DeferredTarget::Region(unstructured_region));

        let old_state = self
            .structurize_region_state
            .insert(unstructured_region, StructurizeRegionState::Ready { backedge, region });
        if !matches!(old_state, Some(StructurizeRegionState::InProgress)) {
            unreachable!(
                "cfg::Structurizer::structurize_region_from: \
                 already {}, when attempting to store structurization result",
                match old_state {
                    None => "reverted to missing (removed from the map?)",
                    Some(StructurizeRegionState::InProgress) => unreachable!(),
                    Some(StructurizeRegionState::Ready { .. }) => "completed",
                    Some(StructurizeRegionState::Claimed) => "claimed",
                }
            );
        }
    }

    /// Build a `Select` [`ControlNode`], from partially structured `cases`,
    /// merging all of their `deferred_{edges,returns}` together.
    fn structurize_select(
        &mut self,
        kind: SelectionKind,
        scrutinee: Value,
        cases: SmallVec<[PartialControlRegion; 8]>,
    ) -> PartialControlRegion {
        // `Select` isn't actually needed unless there's at least two `cases`.
        if cases.len() <= 1 {
            return cases.into_iter().next().unwrap_or_else(|| PartialControlRegion {
                children: EntityList::empty(),
                deferred_edges: DeferredEdgeBundleSet {
                    target_to_deferred: [].into_iter().collect(),
                },
            });
        }

        // Gather the full set of deferred edges (and returns), along with the
        // necessary information for the `Select`'s `ControlNodeOutputDecl`s.
        let mut deferred_edges_to_input_count_and_total_edge_count = FxIndexMap::default();
        let mut deferred_return_types = None;
        for case in &cases {
            for (&target, deferred) in &case.deferred_edges.target_to_deferred {
                let input_count = deferred.edge_bundle.target_inputs.len();

                let (old_input_count, accumulated_edge_count) =
                    deferred_edges_to_input_count_and_total_edge_count
                        .entry(target)
                        .or_insert((input_count, IncomingEdgeCount::default()));
                assert_eq!(*old_input_count, input_count);
                *accumulated_edge_count += deferred.edge_bundle.accumulated_count;

                if target == DeferredTarget::Return && deferred_return_types.is_none() {
                    // HACK(eddyb) because there's no `FuncDecl` available, take the
                    // types from the returned values and hope they match.
                    deferred_return_types = Some(
                        deferred
                            .edge_bundle
                            .target_inputs
                            .iter()
                            .map(|&v| self.func_def_body.at(v).type_of(self.cx)),
                    );
                }
            }
        }

        // The `Select` outputs are the concatenation of `target_inputs`, for
        // each unique `deferred_edges` target.
        //
        // FIXME(eddyb) this `struct` only really exists for readability.
        struct Deferred {
            target: DeferredTarget,
            target_input_count: usize,

            /// Sum of `accumulated_count` for this `target` across all `cases`.
            total_edge_count: IncomingEdgeCount,
        }
        let deferreds = || {
            deferred_edges_to_input_count_and_total_edge_count.iter().map(
                |(&target, &(target_input_count, total_edge_count))| Deferred {
                    target,
                    target_input_count,
                    total_edge_count,
                },
            )
        };
        let mut output_decls: SmallVec<[_; 2]> =
            SmallVec::with_capacity(deferreds().map(|deferred| deferred.target_input_count).sum());
        for deferred in deferreds() {
            let target_input_types = match deferred.target {
                DeferredTarget::Region(target) => {
                    Either::Left(self.func_def_body.at(target).def().inputs.iter().map(|i| i.ty))
                }
                DeferredTarget::Return => Either::Right(deferred_return_types.take().unwrap()),
            };
            assert_eq!(target_input_types.len(), deferred.target_input_count);

            output_decls.extend(
                target_input_types
                    .map(|ty| ControlNodeOutputDecl { attrs: AttrSet::default(), ty }),
            );
        }

        // Convert the cases into `ControlRegion`s, each outputting the full set
        // of values described by `outputs` (with undef filling in any gaps),
        // while deferred conditions are collected separately (for `LazyCond`).
        let mut deferred_per_case_conditions: SmallVec<[_; 8]> =
            deferreds().map(|_| Vec::with_capacity(cases.len())).collect();
        let cases = cases
            .into_iter()
            .enumerate()
            .map(|(case_idx, case)| {
                let PartialControlRegion { children, mut deferred_edges } = case;

                let mut outputs = SmallVec::with_capacity(output_decls.len());
                for (deferred, per_case_conditions) in
                    deferreds().zip_eq(&mut deferred_per_case_conditions)
                {
                    let (edge_condition, values_or_count) =
                        match deferred_edges.target_to_deferred.remove(&deferred.target) {
                            Some(DeferredEdgeBundle { condition, edge_bundle }) => {
                                (Some(condition), Ok(edge_bundle.target_inputs))
                            }

                            None => (Some(LazyCond::False), Err(deferred.target_input_count)),
                        };

                    if let Some(edge_condition) = edge_condition {
                        assert_eq!(per_case_conditions.len(), case_idx);
                        per_case_conditions.push(edge_condition);
                    }

                    match values_or_count {
                        Ok(values) => outputs.extend(values),
                        Err(missing_value_count) => {
                            let decls_for_missing_values =
                                &output_decls[outputs.len()..][..missing_value_count];
                            outputs.extend(
                                decls_for_missing_values
                                    .iter()
                                    .map(|output| Value::Const(self.const_undef(output.ty))),
                            );
                        }
                    }
                }

                // All deferrals must have been converted into outputs above.
                assert!(deferred_edges.target_to_deferred.is_empty());
                assert_eq!(outputs.len(), output_decls.len());

                self.func_def_body.control_regions.define(
                    self.cx,
                    ControlRegionDef { inputs: [].into_iter().collect(), children, outputs },
                )
            })
            .collect();

        let kind = ControlNodeKind::Select { kind, scrutinee, cases };
        let select_node = self
            .func_def_body
            .control_nodes
            .define(self.cx, ControlNodeDef { kind, outputs: output_decls }.into());

        // Build `deferred_edges` for the whole `Select`, pointing to
        // the outputs of the `select_node` `ControlNode` for all `Value`s.
        let mut outputs = (0..)
            .map(|output_idx| Value::ControlNodeOutput { control_node: select_node, output_idx });
        let deferreds = deferreds().zip_eq(deferred_per_case_conditions).map(
            |(deferred, per_case_conditions)| {
                let target_inputs = outputs.by_ref().take(deferred.target_input_count).collect();

                // Simplify `LazyCond`s eagerly, to reduce costs later on.
                let condition =
                    if per_case_conditions.iter().all(|cond| matches!(cond, LazyCond::True)) {
                        LazyCond::True
                    } else {
                        LazyCond::MergeSelect {
                            control_node: select_node,
                            per_case_conds: per_case_conditions,
                        }
                    };

                DeferredEdgeBundle {
                    condition,
                    edge_bundle: IncomingEdgeBundle {
                        target: deferred.target,
                        accumulated_count: deferred.total_edge_count,
                        target_inputs,
                    },
                }
            },
        );

        let mut children = EntityList::empty();
        children.insert_last(select_node, &mut self.func_def_body.control_nodes);
        PartialControlRegion {
            children,
            deferred_edges: DeferredEdgeBundleSet {
                target_to_deferred: deferreds
                    .map(|deferred| deferred.into_target_keyed_kv_pair())
                    .collect(),
            },
        }
    }

    // FIXME(eddyb) this should try to handle as many `LazyCond` as are available,
    // for incorporating them all at once, ideally with a switch instead
    // of N individual branches with their own booleans etc.
    fn materialize_lazy_cond(&mut self, cond: LazyCond) -> Value {
        match cond {
            LazyCond::False => Value::Const(self.const_false),
            LazyCond::True => Value::Const(self.const_true),
            LazyCond::MergeSelect { control_node, per_case_conds } => {
                // HACK(eddyb) this should not allocate most of the time, and
                // avoids complications later below, when mutating the cases.
                let per_case_conds: SmallVec<[_; 8]> = per_case_conds
                    .into_iter()
                    .map(|cond| self.materialize_lazy_cond(cond))
                    .collect();

                // FIXME(eddyb) this should handle an all-`true` `per_case_conds`
                // (but `structurize_select` currently takes care of those).

                let ControlNodeDef { kind, outputs: output_decls } =
                    &mut *self.func_def_body.control_nodes[control_node];
                let cases = match kind {
                    ControlNodeKind::Select { kind, scrutinee, cases } => {
                        assert_eq!(cases.len(), per_case_conds.len());

                        if let SelectionKind::BoolCond = kind {
                            let [val_false, val_true] =
                                [self.const_false, self.const_true].map(Value::Const);
                            if per_case_conds[..] == [val_true, val_false] {
                                return *scrutinee;
                            } else if per_case_conds[..] == [val_false, val_true] {
                                // FIXME(eddyb) this could also be special-cased,
                                // at least when called from the topmost level,
                                // where which side is `false`/`true` doesn't
                                // matter (or we could even generate `!cond`?).
                                let _not_cond = *scrutinee;
                            }
                        }

                        cases
                    }
                    _ => unreachable!(),
                };

                let output_idx = u32::try_from(output_decls.len()).unwrap();
                output_decls
                    .push(ControlNodeOutputDecl { attrs: AttrSet::default(), ty: self.type_bool });

                for (&case, cond) in cases.iter().zip_eq(per_case_conds) {
                    let ControlRegionDef { outputs, .. } =
                        &mut self.func_def_body.control_regions[case];
                    outputs.push(cond);
                    assert_eq!(outputs.len(), output_decls.len());
                }

                Value::ControlNodeOutput { control_node, output_idx }
            }
        }
    }

    /// When structurization is only partial, and there remain unclaimed regions,
    /// they have to be reintegrated into the CFG, putting back [`ControlInst`]s
    /// where `structurize_region_from` has taken them from.
    ///
    /// This function handles one region at a time to make it more manageable,
    /// despite it having a single call site (in a loop in `structurize_func`).
    fn repair_unclaimed_region(
        &mut self,
        unstructured_region: ControlRegion,
        partial_control_region: PartialControlRegion,
    ) {
        assert!(
            self.structurize_region_state.is_empty(),
            "cfg::Structurizer::repair_unclaimed_region: must only be called \
             from `structurize_func`, after it takes `structurize_region_state`"
        );

        let PartialControlRegion { children, mut deferred_edges } = partial_control_region;

        // HACK(eddyb) this'd be unnecessary if `PartialControlRegion` didn't
        // hold `children` (and the original `ControlRegion` was relied upon).
        {
            let list_eq_key = |l: EntityList<_>| (l.iter().first, l.iter().last);
            assert!(
                list_eq_key(children)
                    == list_eq_key(self.func_def_body.at(unstructured_region).def().children)
            );
        }

        // Build a chain of conditional branches to apply deferred edges.
        let deferred_return = deferred_edges
            .target_to_deferred
            .remove(&DeferredTarget::Return)
            .map(|deferred| deferred.edge_bundle.target_inputs);
        let mut deferred_edge_targets =
            deferred_edges.target_to_deferred.into_iter().map(|(deferred_target, deferred)| {
                let deferred_target = match deferred_target {
                    DeferredTarget::Region(target) => target,
                    DeferredTarget::Return => unreachable!(),
                };
                (deferred.condition, (deferred_target, deferred.edge_bundle.target_inputs))
            });
        let mut control_source = Some(unstructured_region);
        while let Some((condition, then_target_and_inputs)) = deferred_edge_targets.next() {
            let branch_source = control_source.take().unwrap();
            let else_target_and_inputs =
                if deferred_edge_targets.len() <= 1 && deferred_return.is_none() {
                    // At most one deferral left, so it can be used as the "else"
                    // case, or the branch left unconditional in its absence.
                    deferred_edge_targets.next().map(|(_, t)| t)
                } else {
                    // Either more branches, or a deferred return, are needed, so
                    // the "else" case must be a `ControlRegion` that itself can
                    // have a `ControlInst` attached to it later on.
                    let new_empty_region = self.func_def_body.control_regions.define(
                        self.cx,
                        ControlRegionDef {
                            inputs: [].into_iter().collect(),
                            children: EntityList::empty(),
                            outputs: [].into_iter().collect(),
                        },
                    );
                    control_source = Some(new_empty_region);
                    Some((new_empty_region, [].into_iter().collect()))
                };

            let condition = Some(condition)
                .filter(|_| else_target_and_inputs.is_some())
                .map(|cond| self.materialize_lazy_cond(cond));
            let branch_control_inst = ControlInst {
                attrs: AttrSet::default(),
                kind: if condition.is_some() {
                    ControlInstKind::SelectBranch(SelectionKind::BoolCond)
                } else {
                    ControlInstKind::Branch
                },
                inputs: condition.into_iter().collect(),
                targets: [&then_target_and_inputs]
                    .into_iter()
                    .chain(&else_target_and_inputs)
                    .map(|&(target, _)| target)
                    .collect(),
                target_inputs: [then_target_and_inputs]
                    .into_iter()
                    .chain(else_target_and_inputs)
                    .filter(|(_, inputs)| !inputs.is_empty())
                    .collect(),
            };
            assert!(
                self.func_def_body
                    .unstructured_cfg
                    .as_mut()
                    .unwrap()
                    .control_inst_on_exit_from
                    .insert(branch_source, branch_control_inst)
                    .is_none()
            );
        }

        let final_source = match control_source {
            Some(region) => region,
            None => {
                // The loop above handled all the targets, nothing left to do.
                assert!(deferred_return.is_none());
                return;
            }
        };

        // Final deferral is either a `Return` (if needed), or an `Unreachable`
        // (only when truly divergent, i.e. no `deferred_edges`/`deferred_return`).
        let final_control_inst = {
            let (kind, inputs) = match deferred_return {
                Some(return_values) => (ControlInstKind::Return, return_values),
                None => (ControlInstKind::Unreachable, [].into_iter().collect()),
            };
            ControlInst {
                attrs: AttrSet::default(),
                kind,
                inputs,
                targets: [].into_iter().collect(),
                target_inputs: FxIndexMap::default(),
            }
        };
        assert!(
            self.func_def_body
                .unstructured_cfg
                .as_mut()
                .unwrap()
                .control_inst_on_exit_from
                .insert(final_source, final_control_inst)
                .is_none()
        );
    }

    /// Create an undefined constant (as a placeholder where a value needs to be
    /// present, but won't actually be used), of type `ty`.
    fn const_undef(&self, ty: Type) -> Const {
        // FIXME(eddyb) SPIR-T should have native undef itself.
        let wk = &spv::spec::Spec::get().well_known;
        self.cx.intern(ConstDef {
            attrs: AttrSet::default(),
            ty,
            kind: ConstKind::SpvInst {
                spv_inst_and_const_inputs: Rc::new((wk.OpUndef.into(), [].into_iter().collect())),
            },
        })
    }
}
