//! Control-flow graph (CFG) abstractions and utilities.

use crate::func_at::FuncAt;
use crate::{
    spv, AttrSet, Const, ConstCtor, ConstDef, Context, ControlNode, ControlNodeDef,
    ControlNodeKind, ControlRegion, ControlRegionDef, EntityList, EntityListIter,
    EntityOrientedDenseMap, EntityOrientedMapKey, FuncDefBody, FxIndexMap, SelectionKind, TypeCtor,
    TypeDef, Value,
};
use smallvec::SmallVec;
use std::{mem, slice};

/// The control-flow graph (CFG) of a function, as control-flow instructions
/// (`ControlInst`s) attached to `ControlNode`-relative CFG points (`ControlPoint`s).
#[derive(Clone, Default)]
pub struct ControlFlowGraph {
    // FIXME(eddyb) if all keys are `ControlPoint::Exit`s, should this map be
    // keyed on `ControlNode` (and have e.g. `_on_exit` in the name) instead?
    pub control_insts: EntityOrientedDenseMap<ControlPoint, ControlInst>,
}

/// A point in the control-flow graph (CFG) of a function, relative to a `ControlNode`.
///
/// The whole CFG of the function consists of `ControlInst`s connecting all such
/// points, expect for these special cases:
///
/// * `ControlNodeKind::UnstructuredMerge`: lacks an `Entry` point entirely, as
///   its purpose is to represent an effectively multiple-entry single-exit (MESE)
///   "half-`ControlNode`", that could only become complete by structurization
///   (and would likely end up the "merge" / exit side of the structured node)
///
/// * `ControlNodeKind::Block`: between its `Entry` and `Exit` points, a block only
///   has its own linear sequence of instructions as (implied) control-flow, so
///   no `ControlInst` can attach to its `Entry` or target its `Exit`
//
// FIXME(eddyb) the above comment treats `Block` specially but the trend has
// been to make all the CFG logic treat structured `ControlNode`s (or several of
// them in linear chains, as found in a `ControlRegion`) as never having any
// `ControlInst`s except at the very last `Exit`, and the CFG mostly ignoring
// the structured control-flow (see also the comments on `ControlPointRange`).
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum ControlPoint {
    Entry(ControlNode),
    Exit(ControlNode),
}

impl ControlPoint {
    pub fn control_node(self) -> ControlNode {
        match self {
            Self::Entry(control_node) | Self::Exit(control_node) => control_node,
        }
    }
}

impl<V> EntityOrientedMapKey<V> for ControlPoint {
    type Entity = ControlNode;
    fn to_entity(point: Self) -> ControlNode {
        point.control_node()
    }

    type DenseValueSlots = [Option<V>; 2];
    fn get_dense_value_slot(point: Self, [entry, exit]: &[Option<V>; 2]) -> &Option<V> {
        match point {
            Self::Entry(_) => entry,
            Self::Exit(_) => exit,
        }
    }
    fn get_dense_value_slot_mut(point: Self, [entry, exit]: &mut [Option<V>; 2]) -> &mut Option<V> {
        match point {
            Self::Entry(_) => entry,
            Self::Exit(_) => exit,
        }
    }
}

#[derive(Clone)]
pub struct ControlInst {
    pub attrs: AttrSet,

    pub kind: ControlInstKind,

    pub inputs: SmallVec<[Value; 2]>,

    // FIXME(eddyb) change the inline size of this to fit most instructions.
    pub targets: SmallVec<[ControlPoint; 4]>,

    /// `target_merge_outputs[control_node][output_idx]` is the `Value` that
    /// `Value::ControlNodeOutput { control_node, output_idx }` will get on exit
    /// from `control_node` (via `ControlPoint::Exit(control_node)` in `targets`).
    pub target_merge_outputs: FxIndexMap<ControlNode, SmallVec<[Value; 2]>>,
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

/// Abstraction for (potentially partially structured) CFG traversal, taking
/// advantage of structured control-flow to avoid allocating `ControlPoint`
/// sequences which are otherwise entirely predictable from the linear chaining
/// of the `ControlNode` children in a `ControlRegion`.
#[derive(Copy, Clone)]
pub enum ControlPointRange {
    /// Individual `ControlPoint`, equivalent to `Exit(control_node)`.
    ///
    /// For the `Entry` case, see `LinearChain` below (which always has a paired
    /// `Exit`, even for leaf `ControlNode`s - i.e. can't enter without exiting).
    UnstructuredExit(ControlNode),

    /// All `ControlPoint`s from `Entry(first)` to `Exit(last)`, including all
    /// `ControlPoint`s from nested `ControlRegion`s (recursively).
    ///
    /// Of those, only the two ends interact with unstructured control-flow:
    /// * `Entry(first)` alone can be a target of a `ControlInst` (elsewhere)
    /// * `Exit(last)` alone can have a `ControlInst` associated with it
    ///
    /// The `ControlInst` taking over from `Exit(last)` definitely has to exist
    /// if there is any unstructured control-flow in the function, as all exits
    /// out of the function have to be unstructured in that case.
    /// In other words, `Exit(last)` not having a `ControlInst` can only occur
    /// for the implicit structured return at the end of a function's body, and
    /// such a return implies the lack of any unstructured control-flow, as it's
    /// impossible to nest unstructured control-flow in structured control-flow.
    //
    // FIXME(eddyb) is using `EntityListIter` here good? CFG traversal can end up
    // in structured control-flow through an `Entry` into a `ControlNode`, that
    // it keeps following `.next_in_list()` to find the last node in the list,
    // but ideally it shouldn't have to do that work in the first place.
    // Alternatively, each target from a `ControlInst` could have the whole list
    // of chained `ControlNode`s in the `Entry` case, instead of just the first.
    LinearChain(EntityListIter<ControlNode>),
}

impl ControlPointRange {
    /// Return the first `ControlPoint` in this `ControlPointRange`.
    ///
    /// This is the only `ControlPoint` in a `ControlPointRange` that can be
    /// targeted by `ControlInst`s in the CFG (i.e. be the destination of an edge).
    pub fn first(self) -> ControlPoint {
        match self {
            Self::UnstructuredExit(control_node) => ControlPoint::Exit(control_node),
            Self::LinearChain(control_node_list) => ControlPoint::Entry(control_node_list.first),
        }
    }

    /// Return the last `ControlPoint` in this `ControlPointRange`, which is
    /// always an `Exit` (e.g. the final exit of a `ControlRegion`).
    ///
    /// This is the only `ControlPoint` in a `ControlPointRange` that can have
    /// `ControlInst`s attached to in the CFG (i.e. be the source of an edge).
    pub fn last(self) -> ControlPoint {
        match self {
            Self::UnstructuredExit(control_node) => ControlPoint::Exit(control_node),
            Self::LinearChain(control_node_list) => ControlPoint::Exit(control_node_list.last),
        }
    }

    /// Iterate over the `ControlNode`s in the `ControlPointRange`, shallowly.
    pub fn control_nodes(self) -> EntityListIter<ControlNode> {
        match self {
            Self::UnstructuredExit(control_node) => EntityListIter {
                first: control_node,
                last: control_node,
            },
            Self::LinearChain(control_node_list) => control_node_list,
        }
    }
}

/// Helper type for deep traversal of `ControlPointRange`, which tracks the
/// necessary context for "peeking around" within the `ControlPointRange`.
#[derive(Copy, Clone)]
pub struct ControlCursor<'p, P> {
    pub position: P,
    pub parent: Option<&'p ControlCursor<'p, (ControlNode, ControlRegion)>>,
}

impl<'a> FuncAt<'a, ControlCursor<'_, ControlPoint>> {
    /// Return the next `ControlPoint` (wrapped in `ControlCursor`) in a linear
    /// chain within structured control-flow (i.e. no branching to child regions).
    ///
    /// For exits out of a parent `ControlRegion`, the value outputs are also
    /// provided (as they would otherwise require non-trivial work to get to).
    //
    // FIXME(eddyb) introduce more types to make the whole `ControlRegion` outputs
    // stuff seem less hacky.
    pub fn unique_successor(self) -> Option<(Self, Option<&'a [Value]>)> {
        let cursor = self.position;
        let control_node = cursor.position.control_node();
        let control_node_def = &self.control_nodes[control_node];
        match cursor.position {
            // Entering a `ControlNode` depends entirely on the `ControlNodeKind`.
            ControlPoint::Entry(_) => {
                let child_regions: &[_] = match &control_node_def.kind {
                    ControlNodeKind::UnstructuredMerge => {
                        unreachable!("cfg: `UnstructuredMerge` can only be exited, not entered");
                    }
                    ControlNodeKind::Block { .. } => &[],
                    ControlNodeKind::Select { cases, .. } => cases,
                    ControlNodeKind::Loop { body, .. } => slice::from_ref(body),
                };

                if child_regions.is_empty() {
                    Some((
                        self.at(ControlCursor {
                            position: ControlPoint::Exit(control_node),
                            parent: cursor.parent,
                        }),
                        None,
                    ))
                } else {
                    None
                }
            }

            // Exiting a `ControlNode` chains to a sibling/parent.
            ControlPoint::Exit(_) => {
                match control_node_def.next_in_list() {
                    // Enter the next sibling in the `ControlRegion`, if one exists.
                    Some(next_control_node) => Some((
                        self.at(ControlCursor {
                            position: ControlPoint::Entry(next_control_node),
                            parent: cursor.parent,
                        }),
                        None,
                    )),

                    // Exit the parent `ControlNode`, if one exists.
                    None => cursor.parent.map(|parent| {
                        let (parent_control_node, parent_control_region) = parent.position;
                        (
                            self.at(ControlCursor {
                                position: ControlPoint::Exit(parent_control_node),
                                parent: parent.parent,
                            }),
                            Some(&self.at(parent_control_region).def().outputs[..]),
                        )
                    }),
                }
            }
        }
    }
}

impl<'a> FuncAt<'a, ControlPointRange> {
    /// Traverse every `ControlPoint` described by this `ControlPointRange`,
    /// in reverse post-order (RPO), with `f` receiving each `ControlPoint`
    /// in turn (wrapped in `ControlCursor`, for further traversal flexibility),
    /// and being able to stop iteration by returning `Err`.
    ///
    /// RPO iteration over a CFG provides certain guarantees, most importantly
    /// that SSA definitions are visited before any of their uses.
    ///
    /// While this form of traversal is efficient enough (it doesn't allocate,
    /// as non-trivial `ControlPointRange`s only describe structured control-flow,
    /// which doesn't require bookkeeping to visit every `ControlNode` only once,
    /// nor the kind of buffering involved in arbitrary CFG RPO), it should be
    /// nevertheless avoided where possible, in favor of custom recursion on the
    /// `ControlNode`s described by `ControlPointRange::LinearChain`, which can
    /// handle structured control-flow in a manner simpler than arbitrary CFGs.
    pub fn rev_post_order_try_for_each<E>(
        self,
        mut f: impl FnMut(FuncAt<'a, ControlCursor<'_, ControlPoint>>) -> Result<(), E>,
    ) -> Result<(), E> {
        match self.position {
            ControlPointRange::UnstructuredExit(control_node) => f(self.at(ControlCursor {
                position: ControlPoint::Exit(control_node),
                parent: None,
            })),
            ControlPointRange::LinearChain(control_node_list) => self
                .at(Some(control_node_list))
                .rev_post_order_try_for_each_inner(&mut f, None),
        }
    }
}

impl<'a> FuncAt<'a, Option<EntityListIter<ControlNode>>> {
    fn rev_post_order_try_for_each_inner<E>(
        self,
        f: &mut impl FnMut(FuncAt<'a, ControlCursor<'_, ControlPoint>>) -> Result<(), E>,
        parent: Option<&ControlCursor<'_, (ControlNode, ControlRegion)>>,
    ) -> Result<(), E> {
        for func_at_control_node in self {
            let child_regions: &[_] = match &func_at_control_node.def().kind {
                ControlNodeKind::UnstructuredMerge => {
                    unreachable!("cfg: `UnstructuredMerge` can only be exited, not entered");
                }
                ControlNodeKind::Block { .. } => &[],
                ControlNodeKind::Select { cases, .. } => cases,
                ControlNodeKind::Loop { body, .. } => slice::from_ref(body),
            };

            let control_node = func_at_control_node.position;
            f(self.at(ControlCursor {
                position: ControlPoint::Entry(control_node),
                parent,
            }))?;
            for &region in child_regions {
                self.at(region)
                    .at_children()
                    .into_iter()
                    .rev_post_order_try_for_each_inner(
                        f,
                        Some(&ControlCursor {
                            position: (control_node, region),
                            parent,
                        }),
                    )?;
            }
            f(self.at(ControlCursor {
                position: ControlPoint::Exit(control_node),
                parent,
            }))?;
        }
        Ok(())
    }
}

impl ControlFlowGraph {
    /// Iterate over all `ControlPointRange`s (effectively, `ControlPoint`s)
    /// reachable through `func_def_body`'s CFG, in reverse post-order (RPO).
    ///
    /// RPO iteration over a CFG provides certain guarantees, most importantly
    /// that SSA definitions are visited before any of their uses.
    pub fn rev_post_order(
        &self,
        func_def_body: &FuncDefBody,
    ) -> impl DoubleEndedIterator<Item = ControlPointRange> {
        let mut post_order = SmallVec::<[_; 8]>::new();
        {
            let mut incoming_edge_counts = EntityOrientedDenseMap::new();
            self.traverse_whole_func(
                func_def_body,
                &mut incoming_edge_counts,
                &mut |_| {},
                &mut |point| post_order.push(point),
            );
        }

        post_order.into_iter().rev()
    }
}

// HACK(eddyb) this only serves to disallow accessing `private_count` field of
// `IncomingEdgeCount`.
mod sealed {
    /// Opaque newtype for the count of incoming edges (into a `ControlPoint`).
    ///
    /// The private field prevents direct mutation or construction, forcing the
    /// use of `IncomingEdgeCount::ONE` and addition operations to produce some
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

impl ControlFlowGraph {
    fn traverse_whole_func(
        &self,
        func_def_body: &FuncDefBody,
        incoming_edge_counts: &mut EntityOrientedDenseMap<ControlPoint, IncomingEdgeCount>,
        pre_order_visit: &mut impl FnMut(ControlPointRange),
        post_order_visit: &mut impl FnMut(ControlPointRange),
    ) {
        let body_def = func_def_body.at_body().def();

        // Quick sanity check that this is the right CFG for `func_def_body`.
        assert!(std::ptr::eq(
            func_def_body.unstructured_cfg.as_ref().unwrap(),
            self
        ));
        assert!(body_def.outputs.is_empty());

        let body_children = body_def.children.iter();
        let body_range = ControlPointRange::LinearChain(body_children);
        self.traverse(
            func_def_body.at(body_range),
            incoming_edge_counts,
            pre_order_visit,
            post_order_visit,
        );
    }

    fn traverse(
        &self,
        func_at_unnormalized_point_range: FuncAt<ControlPointRange>,
        incoming_edge_counts: &mut EntityOrientedDenseMap<ControlPoint, IncomingEdgeCount>,
        pre_order_visit: &mut impl FnMut(ControlPointRange),
        post_order_visit: &mut impl FnMut(ControlPointRange),
    ) {
        let control_nodes = func_at_unnormalized_point_range.control_nodes;

        // The initial `ControlPointRange` is "unnormalized" because it might be
        // shorter than what's actually possible, but it would be wasteful to
        // compute the last `ControlNode` in the `LinearChain`, so it's not done
        // in the caller. If that ever changes, the normalization code can be
        // switched to assert that the provided range is always normalized.
        let unnormalized_point_range = func_at_unnormalized_point_range.position;

        // The first `ControlPoint` in the `ControlPointRange` is the same,
        // regardless of normalization (which extends the last `ControlPoint`).
        let first_point = unnormalized_point_range.first();

        // FIXME(eddyb) `EntityOrientedDenseMap` should have an `entry` API.
        if let Some(existing_count) = incoming_edge_counts.get_mut(first_point) {
            *existing_count += IncomingEdgeCount::ONE;
            return;
        }
        incoming_edge_counts.insert(first_point, IncomingEdgeCount::ONE);

        // Normalize the `ControlPointRange`, extending its last `ControlPoint`
        // (which is always an `Exit`) as much as necessary.
        let point_range = match unnormalized_point_range {
            ControlPointRange::UnstructuredExit(_) => unnormalized_point_range,
            ControlPointRange::LinearChain(mut control_node_list) => {
                assert!(
                    control_nodes[control_node_list.first]
                        .prev_in_list()
                        .is_none(),
                    "cfg: unstructured targets cannot point to the middle of \
                     a structured `ControlRegion`, only to its very start"
                );

                // Extend the list with siblings from the parent `ControlRegion`.
                while let Some(next) = control_nodes[control_node_list.last].next_in_list() {
                    control_node_list.last = next;
                }

                ControlPointRange::LinearChain(control_node_list)
            }
        };

        pre_order_visit(point_range);

        let control_inst = self
            .control_insts
            .get(point_range.last())
            .expect("cfg: missing `ControlInst`, despite having left structured control-flow");

        for &target in &control_inst.targets {
            let target_range = match target {
                ControlPoint::Entry(control_node) => {
                    ControlPointRange::LinearChain(EntityListIter {
                        first: control_node,
                        last: control_node,
                    })
                }
                ControlPoint::Exit(control_node) => {
                    ControlPointRange::UnstructuredExit(control_node)
                }
            };
            self.traverse(
                func_at_unnormalized_point_range.at(target_range),
                incoming_edge_counts,
                pre_order_visit,
                post_order_visit,
            );
        }

        post_order_visit(point_range);
    }
}

pub struct Structurizer<'a> {
    cx: &'a Context,

    /// Input for `SelectionKind::BoolCond`, corresponding to the "then" case.
    const_true: Const,

    func_def_body: &'a mut FuncDefBody,
    incoming_edge_counts: EntityOrientedDenseMap<ControlPoint, IncomingEdgeCount>,

    /// Keyed by the input to `structurize_region_from` (the start `ControlPoint`),
    /// and describing the state of that partial structurization step.
    ///
    /// See also `StructurizeRegionState`'s docs.
    //
    // FIXME(eddyb) use `EntityOrientedDenseMap` (which lacks iteration by design).
    structurize_region_state: FxIndexMap<ControlPoint, StructurizeRegionState>,
}

/// The state of one `structurize_region_from` invocation (keyed on its start
/// `ControlPoint` in `Structurizer`) and its `PartialControlRegion` output.
///
/// There is a fourth (or 0th) implicit state, which is where nothing has yet
/// observed some region, and `Structurizer` isn't tracking it at all.
//
// FIXME(eddyb) make the 0th state explicit and move `incoming_edge_counts` to it.
enum StructurizeRegionState {
    /// Structurization is still running, and observing this is a cycle.
    InProgress,

    /// Structurization completed, and this region can now be claimed.
    Ready {
        /// If this region had backedges (targeting its start `ControlPoint`),
        /// their bundle is taken from the region's `DeferredEdgeBundleSet`,
        /// and kept in this field instead (for simpler/faster access).
        ///
        /// Claiming a region with backedges can combine them with the bundled
        /// edges coming into the CFG cycle from outside, and instead of failing
        /// due to the latter not being enough to claim the region on their own,
        /// actually perform loop structurization.
        backedge: Option<DeferredEdgeBundle>,

        region: PartialControlRegion,
    },

    /// Region was claimed (by an `IncomingEdgeBundle`, with the appropriate
    /// total `IncomingEdgeCount`, minus any `consumed_backedges`), and has
    /// since likely been incorporated as part of some larger region.
    Claimed,
}

/// An "(incoming) edge bundle" is a subset of the edges into a single `target`.
///
/// When `accumulated_count` reaches the total `IncomingEdgeCount` for `target`,
/// that `IncomingEdgeBundle` is said to "effectively own" its `target` (akin to
/// the more commonly used CFG domination relation, but more "incremental").
struct IncomingEdgeBundle {
    target: ControlPoint,
    accumulated_count: IncomingEdgeCount,

    /// When `target` is `ControlPoint::Exit(control_node)`, this holds the
    /// `Value`s that `Value::ControlNodeOutput { control_node, .. }` will get
    /// on exit from `control_node`, through this "edge bundle".
    target_merge_outputs: SmallVec<[Value; 2]>,
}

/// A "deferred (incoming) edge bundle" is an `IncomingEdgeBundle` that cannot
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
/// which could theoretically be simplified (after the `Structurizer`) to:
/// ```text
/// label1_condition = a | b
/// if label1_condition {
///     branch => label1
/// }
/// ```
struct DeferredEdgeBundle {
    condition: Value,
    edge_bundle: IncomingEdgeBundle,
}

/// Set of `DeferredEdgeBundle`s, uniquely keyed by their `target`s.
struct DeferredEdgeBundleSet {
    // FIXME(eddyb) this field requires this invariant to be maintained:
    // `target_to_deferred[target].edge_bundle.target == target` - but that's
    // a bit wasteful and also not strongly controlled either - maybe seal this?
    target_to_deferred: FxIndexMap<ControlPoint, DeferredEdgeBundle>,
}

/// Partially structurized `ControlRegion`.
struct PartialControlRegion {
    // FIXME(eddyb) maybe `EntityList` should really be able to be empty,
    // but that messes with the ability of
    children: Option<EntityList<ControlNode>>,

    successor: PartialControlRegionSuccessor,
}

/// The logical continuation of a partially structurized `ControlRegion`.
enum PartialControlRegionSuccessor {
    /// Leave structured control-flow, using the `ControlInst`.
    //
    // FIXME(eddyb) fully implement CFG structurization, which shouldn't need this.
    Unstructured(ControlInst),

    /// When not all transitive targets could be claimed into the `ControlRegion`,
    /// some remain as deferred exits, blocking further structurization until
    /// all other edges to those targets are gathered together.
    ///
    /// If both `deferred_edges` is empty and `deferred_return` is `None`, then
    /// the `ControlRegion` never exits, i.e. it has divergent control-flow
    /// (such as an infinite loop).
    Deferred {
        deferred_edges: DeferredEdgeBundleSet,

        /// Structured "return" out of the function (holding `output`s for the
        /// function body, i.e. the inputs to the `ControlInstKind::Return`).
        ///
        /// Unlike `DeferredEdgeBundle`, this doesn't need a condition, as it's
        /// effectively a "fallback", only used when `deferred_edges` is empty.
        deferred_return: Option<SmallVec<[Value; 2]>>,
    },
}

impl<'a> Structurizer<'a> {
    pub fn new(cx: &'a Context, func_def_body: &'a mut FuncDefBody) -> Self {
        // FIXME(eddyb) SPIR-T should have native booleans itself.
        let wk = &spv::spec::Spec::get().well_known;
        let bool_ty = cx.intern(TypeDef {
            attrs: AttrSet::default(),
            ctor: TypeCtor::SpvInst(wk.OpTypeBool.into()),
            ctor_args: [].into_iter().collect(),
        });
        let const_true = cx.intern(ConstDef {
            attrs: AttrSet::default(),
            ty: bool_ty,
            ctor: ConstCtor::SpvInst(wk.OpConstantTrue.into()),
            ctor_args: [].into_iter().collect(),
        });

        let mut incoming_edge_counts = EntityOrientedDenseMap::new();
        if let Some(cfg) = &func_def_body.unstructured_cfg {
            cfg.traverse_whole_func(
                func_def_body,
                &mut incoming_edge_counts,
                &mut |_| {},
                &mut |_| {},
            );
        }

        Self {
            cx,
            const_true,

            func_def_body,
            incoming_edge_counts,

            structurize_region_state: FxIndexMap::default(),
        }
    }

    pub fn structurize_func(mut self) {
        // Don't even try to re-structurize functions.
        if self.func_def_body.unstructured_cfg.is_none() {
            return;
        }

        let body_entry =
            ControlPoint::Entry(self.func_def_body.at_body().def().children.iter().first);
        let PartialControlRegion {
            mut children,
            successor,
        } = self.claim_or_defer_single_edge(body_entry, SmallVec::new());

        children = Some(children.unwrap_or_else(|| self.empty_control_region_children()));

        self.func_def_body.at_mut_body().def().children = children.unwrap();

        match successor {
            // Structured return, the function is fully structurized.
            //
            // FIXME(eddyb) also support structured return when the whole body
            // is divergent, by generating undef constants (needs access to the
            // whole `FuncDecl`, not just `FuncDefBody`, or some kind of system
            // of "inputs decls" in `ControlRegion`s, to get the right types).
            PartialControlRegionSuccessor::Deferred {
                deferred_edges,
                deferred_return: Some(return_values),
            } if deferred_edges.target_to_deferred.is_empty() => {
                self.func_def_body.at_mut_body().def().outputs = return_values;
                self.func_def_body.unstructured_cfg = None;
                return;
            }

            // Some cleanup left to do (see after the `match`).
            PartialControlRegionSuccessor::Unstructured(_)
            | PartialControlRegionSuccessor::Deferred { .. } => {}
        }

        // Structurization was only partial, time to start cleaning up.
        self.undo_claim(
            body_entry,
            PartialControlRegion {
                children,
                successor,
            },
        );

        // Undo anything that got unused (e.g. because of unstructurized loops).
        let structurize_region_state = mem::take(&mut self.structurize_region_state);
        for (target, state) in structurize_region_state {
            if let StructurizeRegionState::Ready {
                mut region,
                backedge,
            } = state
            {
                // Undo `backedge` extraction from deferred edges, if needed.
                if let Some(backedge) = backedge {
                    match &mut region.successor {
                        PartialControlRegionSuccessor::Deferred { deferred_edges, .. } => {
                            assert!(
                                deferred_edges
                                    .target_to_deferred
                                    .insert(backedge.edge_bundle.target, backedge)
                                    .is_none()
                            );
                        }
                        _ => unreachable!(
                            "cfg::Structurizer: `backedge`s must come from \
                             `PartialControlRegionSuccessor::Deferred`"
                        ),
                    }
                }

                self.undo_claim(target, region);
            }
        }
    }

    fn claim_or_defer_single_edge(
        &mut self,
        target: ControlPoint,
        target_merge_outputs: SmallVec<[Value; 2]>,
    ) -> PartialControlRegion {
        self.try_claim_edge_bundle(IncomingEdgeBundle {
            target,
            accumulated_count: IncomingEdgeCount::ONE,
            target_merge_outputs,
        })
        .unwrap_or_else(|deferred| PartialControlRegion {
            children: None,
            successor: PartialControlRegionSuccessor::Deferred {
                deferred_edges: DeferredEdgeBundleSet {
                    target_to_deferred: [(deferred.edge_bundle.target, deferred)]
                        .into_iter()
                        .collect(),
                },
                deferred_return: None,
            },
        })
    }

    fn try_claim_edge_bundle(
        &mut self,
        edge_bundle: IncomingEdgeBundle,
    ) -> Result<PartialControlRegion, DeferredEdgeBundle> {
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
        let backedge_count = backedge
            .map(|e| e.edge_bundle.accumulated_count)
            .unwrap_or_default();

        if self.incoming_edge_counts[target] != edge_bundle.accumulated_count + backedge_count {
            return Err(DeferredEdgeBundle {
                condition: Value::Const(self.const_true),
                edge_bundle,
            });
        }

        let state = self
            .structurize_region_state
            .insert(target, StructurizeRegionState::Claimed)
            .unwrap();

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
            // FIXME(eddyb) implement loop "state" with
            // inputs/outputs on the body `ControlRegion`.
            {
                // Guaranteed by `structurize_region_from` handling `backedge`.
                assert!(backedge.edge_bundle.target_merge_outputs.is_empty());
                // Must be the case as it's the same target as `backedge`.
                assert!(edge_bundle.target_merge_outputs.is_empty());
            }

            let DeferredEdgeBundle {
                condition: repeat_condition,
                edge_bundle: backedge,
            } = backedge;
            assert!(backedge.target == target);

            let children = region
                .children
                .unwrap_or_else(|| self.empty_control_region_children());
            let body = self.func_def_body.control_regions.define(
                self.cx,
                ControlRegionDef {
                    children,
                    outputs: [].into_iter().collect(),
                },
            );

            let loop_node = self.func_def_body.control_nodes.define(
                self.cx,
                ControlNodeDef {
                    kind: ControlNodeKind::Loop {
                        body,
                        repeat_condition,
                    },
                    outputs: [].into_iter().collect(),
                }
                .into(),
            );

            // Replace the region with the whole loop, any exits out of the loop
            // being encoded in `region.successor` being a non-empty `Deferred`.
            region.children = Some(EntityList::insert_last(
                None,
                loop_node,
                &mut self.func_def_body.control_nodes,
            ));
        } else {
            // FIXME(eddyb) collect these for later replacement.
            assert!(edge_bundle.target_merge_outputs.is_empty());
        }

        Ok(region)
    }

    /// Structurize a region starting from `first_point`, and extending as much
    /// as possible into the CFG (likely everything dominated by `first_point`).
    ///
    /// The output of this process is stored in, and any other bookkeeping is
    /// done through, `self.structurize_region_state[first_point]`.
    ///
    /// See also `StructurizeRegionState`'s docs.
    //
    // FIXME(eddyb) should this take `ControlPointRange` instead?
    fn structurize_region_from(&mut self, first_point: ControlPoint) {
        {
            let old_state = self
                .structurize_region_state
                .insert(first_point, StructurizeRegionState::InProgress);
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

        /// Marker error type indicating a structured `Entry`, w/o a `ControlInst`.
        #[derive(Debug)]
        struct StructuredEntry;

        let control_inst = if let ControlPoint::Entry(_) = first_point {
            Err(StructuredEntry)
        } else {
            Ok(self
                .func_def_body
                .unstructured_cfg
                .as_mut()
                .unwrap()
                .control_insts
                .remove(first_point)
                .unwrap_or_else(|| {
                    unreachable!(
                        "cfg::Structurizer::structurize_region_from: missing \
                         `ControlInst` (CFG wasn't unstructured in the first place?)"
                    )
                }))
        };

        // HACK(eddyb) these variables are present here to avoid having to bump
        // the indent for the `ControlInstKind` handling below, any further.
        let (kind, inputs, child_regions) = match &control_inst {
            Err(StructuredEntry) => (Err(StructuredEntry), &[][..], [].into_iter().collect()),
            Ok(ControlInst {
                attrs,
                kind,
                inputs,
                targets,
                target_merge_outputs,
            }) => {
                // FIXME(eddyb) this loses `attrs`.
                let _ = attrs;

                let child_regions: SmallVec<[_; 8]> = targets
                    .iter()
                    .map(|&target| {
                        self.claim_or_defer_single_edge(
                            target,
                            target_merge_outputs
                                .get(&target.control_node())
                                .filter(|_| matches!(target, ControlPoint::Exit(_)))
                                .cloned()
                                .unwrap_or_default(),
                        )
                    })
                    .collect();

                (Ok(kind), &inputs[..], child_regions)
            }
        };

        /// Marker error type for unhandled `ControlInst`s below.
        struct UnsupportedControlInst<CI, CR> {
            control_inst: CI,

            /// Kept here only to have `undo_claim` called on each of them.
            child_regions: CR,
        }

        let region = match kind {
            // Entering a structured `ControlNode` always results in a structured
            // exit from that node (even if initially that might only be `Block`s).
            Err(StructuredEntry) => {
                let control_node = first_point.control_node();

                assert!(
                    self.func_def_body.control_nodes[control_node]
                        .next_in_list()
                        .is_none(),
                    "cfg::Structurizer::structurize_region_from: re-structurizing \
                     with structured regions already present is not yet supported"
                );

                let exit_point = ControlPoint::Exit(control_node);

                self.structurize_region_from(exit_point);
                let exit_state = self
                    .structurize_region_state
                    .insert(exit_point, StructurizeRegionState::Claimed);

                let mut region = match exit_state {
                    Some(StructurizeRegionState::Ready {
                        backedge: None,
                        region,
                    }) => region,

                    _ => unreachable!(),
                };

                region.children = Some(EntityList::insert_first(
                    region.children,
                    control_node,
                    &mut self.func_def_body.control_nodes,
                ));

                Ok(region)
            }

            Ok(ControlInstKind::Unreachable) => {
                assert_eq!((inputs.len(), child_regions.len()), (0, 0));

                // FIXME(eddyb) this may result in lost optimizations over
                // actually encoding it in `ControlNode`/`ControlRegion`
                // (e.g. a new `ControlKind`, or replacing region `outputs`),
                // but it's simpler to handle it like this.
                Ok(PartialControlRegion {
                    children: None,
                    successor: PartialControlRegionSuccessor::Deferred {
                        deferred_edges: DeferredEdgeBundleSet {
                            target_to_deferred: [].into_iter().collect(),
                        },
                        deferred_return: None,
                    },
                })
            }

            Ok(ControlInstKind::ExitInvocation(_)) => {
                assert_eq!(child_regions.len(), 0);

                // FIXME(eddyb) introduce equivalent `ControlNodeKind` for these.
                Err(UnsupportedControlInst {
                    control_inst,
                    child_regions,
                })
            }

            Ok(ControlInstKind::Return) => {
                assert_eq!(child_regions.len(), 0);

                Ok(PartialControlRegion {
                    children: None,
                    successor: PartialControlRegionSuccessor::Deferred {
                        deferred_edges: DeferredEdgeBundleSet {
                            target_to_deferred: [].into_iter().collect(),
                        },
                        deferred_return: Some(control_inst.unwrap().inputs),
                    },
                })
            }

            Ok(ControlInstKind::Branch) => {
                assert_eq!((inputs.len(), child_regions.len()), (0, 1));

                Ok(child_regions.into_iter().nth(0).unwrap())
            }

            Ok(ControlInstKind::SelectBranch(_)) => {
                assert_eq!(inputs.len(), 1);

                let scrutinee = inputs[0];

                // HACK(eddyb) special-case the happy path of all child
                // regions branching together into a common merge point.
                struct NoCommonMerge;
                let merge_bundle = child_regions
                    .iter()
                    .filter_map(|child_region| match &child_region.successor {
                        // Ignore divergent children, they don't need to merge.
                        PartialControlRegionSuccessor::Deferred {
                            deferred_edges,
                            deferred_return: None,
                        } if deferred_edges.target_to_deferred.is_empty() => None,

                        PartialControlRegionSuccessor::Deferred {
                            deferred_edges,
                            deferred_return: None,
                        } => {
                            assert_eq!(deferred_edges.target_to_deferred.len(), 1);

                            let &DeferredEdgeBundle {
                                condition,
                                edge_bundle:
                                    IncomingEdgeBundle {
                                        target,
                                        accumulated_count,
                                        target_merge_outputs: _,
                                    },
                            } = deferred_edges.target_to_deferred.values().nth(0).unwrap();

                            assert!(condition == Value::Const(self.const_true));

                            Some(Ok(IncomingEdgeBundle {
                                target,
                                accumulated_count,
                                target_merge_outputs: [].into_iter().collect(),
                            }))
                        }

                        _ => Some(Err(NoCommonMerge)),
                    })
                    .reduce(
                        |merge_bundle, new_bundle| match (merge_bundle, new_bundle) {
                            (Ok(a), Ok(b)) if a.target == b.target => Ok(IncomingEdgeBundle {
                                target: a.target,
                                accumulated_count: a.accumulated_count + b.accumulated_count,
                                target_merge_outputs: [].into_iter().collect(),
                            }),
                            _ => Err(NoCommonMerge),
                        },
                    )
                    .unwrap_or(
                        // FIXME(eddyb) caseless selections can be supported
                        // by introducing an `Unreachable` after them.
                        Err(NoCommonMerge),
                    );

                if let Ok(merge_bundle) = merge_bundle {
                    let merge_target = merge_bundle.target;

                    // If an `UnstructuredMerge` is being `Exit`ed, that
                    // means the unstructured CFG effectively has phis,
                    // which have to be taken into account, and the
                    // merge `ControlNode` reused.
                    let unstructured_exit_merge = match merge_target {
                        ControlPoint::Exit(merge_node) => {
                            assert!(matches!(
                                self.func_def_body.control_nodes[merge_node].kind,
                                ControlNodeKind::UnstructuredMerge
                            ));
                            Some(merge_node)
                        }
                        _ => None,
                    };

                    // HACK(eddyb) allow the "common merge" to not actually be
                    // claimed, when there's no `UnstructuredMerge` to replace.
                    let region = if unstructured_exit_merge.is_none() {
                        Ok(self.claim_or_defer_single_edge(merge_target, [].into_iter().collect()))
                    } else {
                        self.try_claim_edge_bundle(merge_bundle)
                    };
                    if let Ok(mut region) = region {
                        let kind = match control_inst.unwrap().kind {
                            ControlInstKind::SelectBranch(kind) => kind,
                            _ => unreachable!(),
                        };
                        let cases = child_regions
                            .into_iter()
                            .map(|child_region| {
                                let PartialControlRegion {
                                    children,
                                    successor,
                                } = child_region;

                                let outputs = match successor {
                                    PartialControlRegionSuccessor::Deferred {
                                        mut deferred_edges,
                                        deferred_return: None,
                                    } => {
                                        match deferred_edges
                                            .target_to_deferred
                                            .remove(&merge_target)
                                        {
                                            Some(deferred) => {
                                                assert!(
                                                    deferred_edges.target_to_deferred.is_empty()
                                                );
                                                deferred.edge_bundle.target_merge_outputs
                                            }
                                            // FIXME(eddyb) support having outputs when some
                                            // cases are divergent, by generating undef constants.
                                            None => {
                                                assert!(unstructured_exit_merge.is_none());
                                                [].into_iter().collect()
                                            }
                                        }
                                    }
                                    _ => unreachable!(),
                                };

                                let children = children
                                    .unwrap_or_else(|| self.empty_control_region_children());
                                self.func_def_body
                                    .control_regions
                                    .define(self.cx, ControlRegionDef { children, outputs })
                            })
                            .collect();

                        let kind = ControlNodeKind::Select {
                            kind,
                            scrutinee,
                            cases,
                        };
                        let select_node = match unstructured_exit_merge {
                            Some(merge_node) => {
                                // Reuse the `UnstructuredMerge` region, and
                                // specifically its `outputs`, which cannot
                                // change without rewriting all their uses
                                // elsewhere in the function.
                                self.func_def_body.control_nodes[merge_node].kind = kind;

                                merge_node
                            }
                            _ => self.func_def_body.control_nodes.define(
                                self.cx,
                                ControlNodeDef {
                                    kind,
                                    outputs: [].into_iter().collect(),
                                }
                                .into(),
                            ),
                        };

                        // FIXME(eddyb) maybe make a method for this?
                        // It's also used above for `Err(StructuredEntry)`.
                        region.children = Some(EntityList::insert_first(
                            region.children,
                            select_node,
                            &mut self.func_def_body.control_nodes,
                        ));

                        Ok(region)
                    } else {
                        Err(UnsupportedControlInst {
                            control_inst,
                            child_regions,
                        })
                    }
                } else {
                    Err(UnsupportedControlInst {
                        control_inst,
                        child_regions,
                    })
                }
            }
        };

        let mut region = region.unwrap_or_else(
            |UnsupportedControlInst {
                 control_inst,
                 child_regions,
             }| {
                let control_inst = control_inst.unwrap();

                // Undo claims if the child regions aren't used above.
                for (&undo_target, undo_child_region) in
                    control_inst.targets.iter().zip(child_regions)
                {
                    self.undo_claim(undo_target, undo_child_region);
                }

                PartialControlRegion {
                    children: None,
                    successor: PartialControlRegionSuccessor::Unstructured(control_inst),
                }
            },
        );

        // Try to resolve deferred edges that may have accumulated.
        // FIXME(eddyb) implement deferred edges.

        // Try to extract (deferred) backedges (which later get turned into loops).
        let backedge = match &mut region.successor {
            PartialControlRegionSuccessor::Deferred { deferred_edges, .. } => {
                match deferred_edges.target_to_deferred.get(&first_point) {
                    Some(backedge) => {
                        // FIXME(eddyb) implement loop "state" with
                        // inputs/outputs on the body `ControlRegion`.
                        if backedge.edge_bundle.target_merge_outputs.is_empty() {
                            deferred_edges.target_to_deferred.remove(&first_point)
                        } else {
                            None
                        }
                    }
                    _ => None,
                }
            }
            _ => None,
        };

        let old_state = self.structurize_region_state.insert(
            first_point,
            StructurizeRegionState::Ready { backedge, region },
        );
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

    /// Place back relevant information into the CFG, that was taken by claiming
    /// an edge (bundle) to `target`, which resulted in `partial_control_region`.
    fn undo_claim(&mut self, target: ControlPoint, partial_control_region: PartialControlRegion) {
        let PartialControlRegion {
            children,
            successor,
        } = partial_control_region;

        let undo_point = children
            .map(|list| ControlPoint::Exit(list.iter().last))
            .unwrap_or(target);

        let undo_control_inst = match successor {
            PartialControlRegionSuccessor::Unstructured(control_inst) => control_inst,

            // There is no actual claim for an initial deferral, only for
            // e.g. branches to a deferred target.
            PartialControlRegionSuccessor::Deferred {
                deferred_edges: _,
                deferred_return: None,
            } if children.is_none() => return,

            PartialControlRegionSuccessor::Deferred {
                deferred_edges,
                deferred_return,
            } if deferred_edges.target_to_deferred.is_empty() => {
                let (kind, inputs) = match deferred_return {
                    Some(return_values) => (ControlInstKind::Return, return_values),

                    // Divergent regions only need successors to avoid special-casing
                    // everywhere else, and `Unreachable` works for that.
                    None => (ControlInstKind::Unreachable, [].into_iter().collect()),
                };
                ControlInst {
                    attrs: AttrSet::default(),
                    kind,
                    inputs,
                    targets: [].into_iter().collect(),
                    target_merge_outputs: FxIndexMap::default(),
                }
            }

            PartialControlRegionSuccessor::Deferred {
                deferred_edges,
                deferred_return,
            } => {
                // FIXME(eddyb) support multiple (and conditional) deferred exits.
                assert_eq!(deferred_edges.target_to_deferred.len(), 1);
                assert!(deferred_return.is_none());

                let (_, deferred) = deferred_edges
                    .target_to_deferred
                    .into_iter()
                    .nth(0)
                    .unwrap();
                assert!(deferred.condition == Value::Const(self.const_true));

                ControlInst {
                    attrs: AttrSet::default(),
                    kind: ControlInstKind::Branch,
                    inputs: [].into_iter().collect(),
                    targets: [deferred.edge_bundle.target].into_iter().collect(),
                    target_merge_outputs: [(
                        deferred.edge_bundle.target.control_node(),
                        deferred.edge_bundle.target_merge_outputs,
                    )]
                    .into_iter()
                    .filter(|(_, outputs)| !outputs.is_empty())
                    .collect(),
                }
            }
        };

        assert!(
            self.func_def_body
                .unstructured_cfg
                .as_mut()
                .unwrap()
                .control_insts
                .insert(undo_point, undo_control_inst)
                .is_none()
        );
    }

    /// Create an empty `Block` `ControlNode` to use as the single child of an
    /// otherwise empty `ControlRegion`.
    //
    // FIXME(eddyb) should `ControlRegion`s just allowed to be empty? That might
    // complicate anything that relies on `ControlPoint`s covering everything.
    fn empty_control_region_children(&mut self) -> EntityList<ControlNode> {
        let dummy_block = self.func_def_body.control_nodes.define(
            self.cx,
            ControlNodeDef {
                kind: ControlNodeKind::Block { insts: None },
                outputs: [].into_iter().collect(),
            }
            .into(),
        );
        EntityList::insert_last(None, dummy_block, &mut self.func_def_body.control_nodes)
    }
}
