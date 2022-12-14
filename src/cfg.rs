//! Control-flow graph (CFG) abstractions and utilities.

use crate::func_at::FuncAt;
use crate::{
    spv, AttrSet, Const, ConstCtor, ConstDef, Context, ControlNode, ControlNodeDef,
    ControlNodeKind, ControlNodeOutputDecl, ControlRegion, ControlRegionDef, EntityList,
    EntityOrientedDenseMap, FuncDefBody, FxIndexMap, SelectionKind, Type, TypeCtor, TypeDef, Value,
};
use smallvec::SmallVec;
use std::mem;

/// The control-flow graph (CFG) of a function, as control-flow instructions
/// (`ControlInst`s) attached to `ControlRegion`s, as an "action on exit", i.e.
/// "terminator" (while intra-region control-flow is strictly structured).
#[derive(Clone, Default)]
pub struct ControlFlowGraph {
    pub control_inst_on_exit_from: EntityOrientedDenseMap<ControlRegion, ControlInst>,
}

#[derive(Clone)]
pub struct ControlInst {
    pub attrs: AttrSet,

    pub kind: ControlInstKind,

    pub inputs: SmallVec<[Value; 2]>,

    // FIXME(eddyb) change the inline size of this to fit most instructions.
    pub targets: SmallVec<[ControlRegion; 4]>,

    /// `target_inputs[region][input_idx]` is the `Value` that
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
    /// Iterate over all `ControlRegion`s making up `func_def_body`'s CFG, in
    /// reverse post-order (RPO).
    ///
    /// RPO iteration over a CFG provides certain guarantees, most importantly
    /// that SSA definitions are visited before any of their uses.
    pub fn rev_post_order(
        &self,
        func_def_body: &FuncDefBody,
    ) -> impl DoubleEndedIterator<Item = ControlRegion> {
        let mut post_order = SmallVec::<[_; 8]>::new();
        {
            let mut incoming_edge_counts = EntityOrientedDenseMap::new();
            self.traverse_whole_func(
                func_def_body,
                &mut incoming_edge_counts,
                &mut |_| {},
                &mut |region| post_order.push(region),
            );
        }

        post_order.into_iter().rev()
    }
}

// HACK(eddyb) this only serves to disallow accessing `private_count` field of
// `IncomingEdgeCount`.
mod sealed {
    /// Opaque newtype for the count of incoming edges (into a `ControlRegion`).
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
        incoming_edge_counts: &mut EntityOrientedDenseMap<ControlRegion, IncomingEdgeCount>,
        pre_order_visit: &mut impl FnMut(ControlRegion),
        post_order_visit: &mut impl FnMut(ControlRegion),
    ) {
        let func_at_body = func_def_body.at_body();

        // Quick sanity check that this is the right CFG for `func_def_body`.
        assert!(std::ptr::eq(
            func_def_body.unstructured_cfg.as_ref().unwrap(),
            self
        ));
        assert!(func_at_body.def().outputs.is_empty());

        self.traverse(
            func_at_body,
            incoming_edge_counts,
            pre_order_visit,
            post_order_visit,
        );
    }

    fn traverse(
        &self,
        func_at_region: FuncAt<ControlRegion>,
        incoming_edge_counts: &mut EntityOrientedDenseMap<ControlRegion, IncomingEdgeCount>,
        pre_order_visit: &mut impl FnMut(ControlRegion),
        post_order_visit: &mut impl FnMut(ControlRegion),
    ) {
        let region = func_at_region.position;

        // FIXME(eddyb) `EntityOrientedDenseMap` should have an `entry` API.
        if let Some(existing_count) = incoming_edge_counts.get_mut(region) {
            *existing_count += IncomingEdgeCount::ONE;
            return;
        }
        incoming_edge_counts.insert(region, IncomingEdgeCount::ONE);

        pre_order_visit(region);

        let control_inst = self
            .control_inst_on_exit_from
            .get(region)
            .expect("cfg: missing `ControlInst`, despite having left structured control-flow");

        for &target in &control_inst.targets {
            self.traverse(
                func_at_region.at(target),
                incoming_edge_counts,
                pre_order_visit,
                post_order_visit,
            );
        }

        post_order_visit(region);
    }
}

/// Control-flow "structurizer", which attempts to convert as much of the CFG
/// as possible into structural control-flow (regions).
///
/// See `StructurizeRegionState`'s docs for more details on the algorithm.
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

    /// Scrutinee type for `SelectionKind::BoolCond`.
    type_bool: Type,

    /// Scrutinee value for `SelectionKind::BoolCond`, for the "then" case.
    const_true: Const,

    /// Scrutinee value for `SelectionKind::BoolCond`, for the "else" case.
    const_false: Const,

    func_def_body: &'a mut FuncDefBody,
    incoming_edge_counts: EntityOrientedDenseMap<ControlRegion, IncomingEdgeCount>,

    /// Keyed by the input to `structurize_region_from` (the start `ControlRegion`),
    /// and describing the state of that partial structurization step.
    ///
    /// See also `StructurizeRegionState`'s docs.
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
/// `ControlRegion` in `Structurizer`) and its `PartialControlRegion` output.
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
        /// If this region had backedges (targeting its start `ControlRegion`),
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
    target: ControlRegion,
    accumulated_count: IncomingEdgeCount,

    /// The `Value`s that `Value::ControlRegionInput { region, .. }` will get
    /// on entry into `region`, through this "edge bundle".
    target_inputs: SmallVec<[Value; 2]>,
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
    target_to_deferred: FxIndexMap<ControlRegion, DeferredEdgeBundle>,
}

/// Partially structurized `ControlRegion`, the result of combining together
/// several smaller `ControlRegion`s, based on CFG edges between them.
struct PartialControlRegion {
    // FIXME(eddyb) keep this in the original `ControlRegion` instead.
    children: EntityList<ControlNode>,

    /// When not all transitive targets could be claimed into the `ControlRegion`,
    /// some remain as deferred exits, blocking further structurization until
    /// all other edges to those targets are gathered together.
    ///
    /// If both `deferred_edges` is empty and `deferred_return` is `None`, then
    /// the `ControlRegion` never exits, i.e. it has divergent control-flow
    /// (such as an infinite loop).
    deferred_edges: DeferredEdgeBundleSet,

    /// Structured "return" out of the function (holding `output`s for the
    /// function body, i.e. the inputs to the `ControlInstKind::Return`).
    ///
    /// Unlike `DeferredEdgeBundle`, this doesn't need a condition, as it's
    /// effectively a "fallback", only used when `deferred_edges` is empty.
    deferred_return: Option<SmallVec<[Value; 2]>>,
}

impl<'a> Structurizer<'a> {
    pub fn new(cx: &'a Context, func_def_body: &'a mut FuncDefBody) -> Self {
        // FIXME(eddyb) SPIR-T should have native booleans itself.
        let wk = &spv::spec::Spec::get().well_known;
        let type_bool = cx.intern(TypeDef {
            attrs: AttrSet::default(),
            ctor: TypeCtor::SpvInst(wk.OpTypeBool.into()),
            ctor_args: [].into_iter().collect(),
        });
        let const_true = cx.intern(ConstDef {
            attrs: AttrSet::default(),
            ty: type_bool,
            ctor: ConstCtor::SpvInst(wk.OpConstantTrue.into()),
            ctor_args: [].into_iter().collect(),
        });
        let const_false = cx.intern(ConstDef {
            attrs: AttrSet::default(),
            ty: type_bool,
            ctor: ConstCtor::SpvInst(wk.OpConstantFalse.into()),
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
            type_bool,
            const_true,
            const_false,

            func_def_body,
            incoming_edge_counts,

            structurize_region_state: FxIndexMap::default(),
            control_region_input_replacements: EntityOrientedDenseMap::new(),
        }
    }

    pub fn structurize_func(mut self) {
        // Don't even try to re-structurize functions.
        if self.func_def_body.unstructured_cfg.is_none() {
            return;
        }

        let body_region = self.claim_or_defer_single_edge(self.func_def_body.body, SmallVec::new());

        if body_region.deferred_edges.target_to_deferred.is_empty() {
            // Structured return, the function is fully structurized.
            //
            // FIXME(eddyb) also support structured return when the whole body
            // is divergent, by generating undef constants (needs access to the
            // whole `FuncDecl`, not just `FuncDefBody`, to get the right types).
            if let Some(return_values) = body_region.deferred_return {
                let body_def = self.func_def_body.at_mut_body().def();
                body_def.children = body_region.children;
                body_def.outputs = return_values;
                self.func_def_body.unstructured_cfg = None;

                self.apply_value_replacements();
                return;
            }
        }

        // Repair all the regions that remain unclaimed, including the body.
        let structurize_region_state = mem::take(&mut self.structurize_region_state)
            .into_iter()
            .chain([(
                self.func_def_body.body,
                StructurizeRegionState::Ready {
                    region: body_region,
                    backedge: None,
                },
            )]);
        for (target, state) in structurize_region_state {
            if let StructurizeRegionState::Ready {
                mut region,
                backedge,
            } = state
            {
                // Undo `backedge` extraction from deferred edges, if needed.
                if let Some(backedge) = backedge {
                    assert!(
                        region
                            .deferred_edges
                            .target_to_deferred
                            .insert(backedge.edge_bundle.target, backedge)
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

        self.func_def_body
            .inner_in_place_transform_with(&mut ReplaceValueWith(|v| match v {
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
        .unwrap_or_else(|deferred| PartialControlRegion {
            children: EntityList::empty(),
            deferred_edges: DeferredEdgeBundleSet {
                target_to_deferred: [(deferred.edge_bundle.target, deferred)]
                    .into_iter()
                    .collect(),
            },
            deferred_return: None,
        })
    }

    fn try_claim_edge_bundle(
        &mut self,
        mut edge_bundle: IncomingEdgeBundle,
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
            let DeferredEdgeBundle {
                condition: repeat_condition,
                edge_bundle: backedge,
            } = backedge;
            assert!(backedge.target == target);

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

            let loop_node = self.func_def_body.control_nodes.define(
                self.cx,
                ControlNodeDef {
                    kind: ControlNodeKind::Loop {
                        initial_inputs,
                        body,
                        repeat_condition,
                    },
                    outputs: [].into_iter().collect(),
                }
                .into(),
            );

            // Replace the region with the whole loop, any exits out of the loop
            // being encoded in `region.deferred_*`.
            region.children = EntityList::empty();
            region
                .children
                .insert_last(loop_node, &mut self.func_def_body.control_nodes);
        }

        if !edge_bundle.target_inputs.is_empty() {
            self.control_region_input_replacements
                .insert(target, edge_bundle.target_inputs);
        }

        Ok(region)
    }

    /// Structurize a region starting from `unstructured_region`, and extending
    /// it (by combining the smaller `ControlRegion`s) as much as possible into
    /// the CFG (likely everything dominated by `unstructured_region`).
    ///
    /// The output of this process is stored in, and any other bookkeeping is
    /// done through, `self.structurize_region_state[unstructured_region]`.
    ///
    /// See also `StructurizeRegionState`'s docs.
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

        /// Marker error type for unhandled `ControlInst`s below.
        struct UnsupportedControlInst(ControlInst);

        let region_from_control_inst = {
            let ControlInst {
                attrs,
                kind,
                inputs,
                targets,
                target_inputs,
            } = control_inst;

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
                        deferred_return: None,
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
                            target_to_deferred: [].into_iter().collect(),
                        },
                        deferred_return: Some(inputs),
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
                self.structurize_region_state
                    .insert(proxy, StructurizeRegionState::InProgress);
                self.incoming_edge_counts
                    .insert(proxy, IncomingEdgeCount::ONE);
                let deferred_proxy = DeferredEdgeBundle {
                    condition: Value::Const(self.const_true),
                    edge_bundle: IncomingEdgeBundle {
                        target: proxy,
                        accumulated_count: IncomingEdgeCount::default(),
                        target_inputs: [].into_iter().collect(),
                    },
                };

                PartialControlRegion {
                    children: EntityList::empty(),
                    deferred_edges: DeferredEdgeBundleSet {
                        target_to_deferred: [deferred_proxy]
                            .into_iter()
                            .map(|d| (d.edge_bundle.target, d))
                            .collect(),
                    },
                    deferred_return: None,
                }
            });

        // Prepend `unstructured_region`'s children to `region_from_control_inst`.
        let mut region = {
            let mut children = self.func_def_body.at(unstructured_region).def().children;

            children.append(
                region_from_control_inst.children,
                &mut self.func_def_body.control_nodes,
            );

            // HACK(eddyb) this updates `unstructured_region` just in case
            // `repair_unclaimed_region` needs to use it again. But it would be
            // better if `PartialControlRegion` didn't have a `children` copy.
            self.func_def_body
                .at_mut(unstructured_region)
                .def()
                .children = children;

            PartialControlRegion {
                children,
                ..region_from_control_inst
            }
        };

        // Try to resolve deferred edges that may have accumulated, and keep
        // going until there's no more deferred edges that can be claimed.
        let try_claim_any_deferred_edge =
            |this: &mut Self, deferred_edges: &mut DeferredEdgeBundleSet| {
                for (i, deferred) in deferred_edges.target_to_deferred.values_mut().enumerate() {
                    // HACK(eddyb) "take" `deferred.edge_bundle` so it can be
                    // passed to `try_claim_edge_bundle` (and put back if `Err`).
                    let DeferredEdgeBundle {
                        condition,
                        ref mut edge_bundle,
                    } = *deferred;
                    let taken_edge_bundle = IncomingEdgeBundle {
                        target: edge_bundle.target,
                        accumulated_count: edge_bundle.accumulated_count,
                        target_inputs: mem::take(&mut edge_bundle.target_inputs),
                    };

                    match this.try_claim_edge_bundle(taken_edge_bundle) {
                        Ok(claimed_region) => {
                            // FIXME(eddyb) should this use `swap_remove_index`?
                            deferred_edges.target_to_deferred.shift_remove_index(i);
                            return Some((condition, claimed_region));
                        }

                        // Put back the `IncomingEdgeBundle` and keep looking.
                        Err(new_deferred) => *edge_bundle = new_deferred.edge_bundle,
                    }
                }
                None
            };
        while let Some((condition, then_region)) =
            try_claim_any_deferred_edge(self, &mut region.deferred_edges)
        {
            let else_region = PartialControlRegion {
                children: EntityList::empty(),
                ..region
            };
            let else_is_unreachable = else_region.deferred_edges.target_to_deferred.is_empty()
                && else_region.deferred_return.is_none();

            // `then_region` is only taken if `condition` holds, except that
            // `condition` can be ignored when `else_region` is unreachable.
            let mut merged_region = if else_is_unreachable {
                then_region
            } else {
                self.structurize_select(
                    SelectionKind::BoolCond,
                    condition,
                    [then_region, else_region].into_iter().collect(),
                )
            };

            // Prepend the original children to the freshly merged region.
            merged_region
                .children
                .prepend(region.children, &mut self.func_def_body.control_nodes);

            region = merged_region;
        }

        // Try to extract (deferred) backedges (which later get turned into loops).
        let backedge = region
            .deferred_edges
            .target_to_deferred
            .remove(&unstructured_region);

        let old_state = self.structurize_region_state.insert(
            unstructured_region,
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

    /// Build a `Select` `ControlNode`, from partially structured `cases`,
    /// merging all of their `deferred_{edges,returns}` together.
    fn structurize_select(
        &mut self,
        kind: SelectionKind,
        scrutinee: Value,
        cases: SmallVec<[PartialControlRegion; 8]>,
    ) -> PartialControlRegion {
        // `Select` isn't actually needed unless there's at least two `cases`.
        if cases.len() <= 1 {
            return cases
                .into_iter()
                .next()
                .unwrap_or_else(|| PartialControlRegion {
                    children: EntityList::empty(),
                    deferred_edges: DeferredEdgeBundleSet {
                        target_to_deferred: [].into_iter().collect(),
                    },
                    deferred_return: None,
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
            }
            if let Some(return_values) = &case.deferred_return {
                // HACK(eddyb) because there's no `FuncDecl` available, take the
                // types from the returned values and hope they match.
                deferred_return_types = Some(
                    return_values
                        .iter()
                        .map(|&v| self.func_def_body.at(v).type_of(self.cx)),
                );
            }
        }
        let deferred_return_value_count = deferred_return_types.clone().map(|tys| tys.len());

        // Avoid computing deferral conditions when the target isn't ambiguous.
        let needs_per_deferred_edge_condition =
            deferred_edges_to_input_count_and_total_edge_count.len() > 1
                || deferred_return_types.is_some();

        // The `Select` outputs are the concatenation of:
        // * for each unique `deferred_edges` target:
        //   * condition (only if `needs_per_deferred_edge_condition` - see above)
        //   * `target_inputs`
        // * `deferred_return` values (if needed)
        //
        // FIXME(eddyb) some of this could maybe be generalized to deferred infra.
        enum Deferred {
            Edge {
                target: ControlRegion,
                // NOTE(eddyb) not including condition, only `target_inputs`.
                target_input_count: usize,

                /// Sum of `accumulated_count` for this `target` across all `cases`.
                total_edge_count: IncomingEdgeCount,
            },
            Return {
                value_count: usize,
            },
        }
        let deferreds = || {
            deferred_edges_to_input_count_and_total_edge_count
                .iter()
                .map(
                    |(&target, &(target_input_count, total_edge_count))| Deferred::Edge {
                        target,
                        target_input_count,
                        total_edge_count,
                    },
                )
                .chain(
                    deferred_return_value_count.map(|value_count| Deferred::Return { value_count }),
                )
        };
        let mut output_decls: SmallVec<[_; 2]> = SmallVec::with_capacity(
            deferreds()
                .map(|deferred| match deferred {
                    Deferred::Edge {
                        target_input_count, ..
                    } => (needs_per_deferred_edge_condition as usize) + target_input_count,
                    Deferred::Return { value_count } => value_count,
                })
                .sum(),
        );
        for deferred in deferreds() {
            let output_decl_from_ty = |ty| ControlNodeOutputDecl {
                attrs: AttrSet::default(),
                ty,
            };
            match deferred {
                Deferred::Edge {
                    target,
                    target_input_count,
                    ..
                } => {
                    let target_inputs = &self.func_def_body.at(target).def().inputs;
                    assert_eq!(target_inputs.len(), target_input_count);

                    if needs_per_deferred_edge_condition {
                        output_decls.push(output_decl_from_ty(self.type_bool));
                    }
                    output_decls.extend(target_inputs.iter().map(|i| output_decl_from_ty(i.ty)));
                }
                Deferred::Return { value_count } => {
                    let types = deferred_return_types.clone().unwrap();
                    assert_eq!(types.len(), value_count);

                    output_decls.extend(types.map(output_decl_from_ty));
                }
            }
        }

        // Convert the cases into `ControlRegion`s, each outputting the full set
        // of values described by `outputs` (with undef filling in any gaps).
        let cases = cases
            .into_iter()
            .map(|case| {
                let PartialControlRegion {
                    children,
                    mut deferred_edges,
                    mut deferred_return,
                } = case;

                let mut outputs = SmallVec::with_capacity(output_decls.len());
                for deferred in deferreds() {
                    let (edge_condition, values_or_count) = match deferred {
                        Deferred::Edge {
                            target,
                            target_input_count,
                            ..
                        } => match deferred_edges.target_to_deferred.remove(&target) {
                            Some(DeferredEdgeBundle {
                                condition,
                                edge_bundle,
                            }) => (Some(condition), Ok(edge_bundle.target_inputs)),

                            None => (
                                Some(Value::Const(self.const_false)),
                                Err(target_input_count),
                            ),
                        },
                        Deferred::Return { value_count } => {
                            (None, deferred_return.take().ok_or(value_count))
                        }
                    };

                    if needs_per_deferred_edge_condition {
                        outputs.extend(edge_condition);
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
                assert!(deferred_edges.target_to_deferred.is_empty() && deferred_return.is_none());
                assert_eq!(outputs.len(), output_decls.len());

                self.func_def_body.control_regions.define(
                    self.cx,
                    ControlRegionDef {
                        inputs: [].into_iter().collect(),
                        children,
                        outputs,
                    },
                )
            })
            .collect();

        let kind = ControlNodeKind::Select {
            kind,
            scrutinee,
            cases,
        };
        let select_node = self.func_def_body.control_nodes.define(
            self.cx,
            ControlNodeDef {
                kind,
                outputs: output_decls,
            }
            .into(),
        );

        // Build `deferred_{edges,return}` for the whole `Select`, pointing to
        // the outputs of the `select_node` `ControlNode` for all `Value`s.
        let mut deferred_edges = DeferredEdgeBundleSet {
            target_to_deferred: FxIndexMap::default(),
        };
        let mut deferred_return = None;

        let mut outputs = (0..).map(|output_idx| Value::ControlNodeOutput {
            control_node: select_node,
            output_idx,
        });
        for deferred in deferreds() {
            match deferred {
                Deferred::Edge {
                    target,
                    target_input_count,
                    total_edge_count,
                } => {
                    let condition = if needs_per_deferred_edge_condition {
                        outputs.next().unwrap()
                    } else {
                        Value::Const(self.const_true)
                    };
                    let target_inputs = outputs.by_ref().take(target_input_count).collect();

                    deferred_edges.target_to_deferred.insert(
                        target,
                        DeferredEdgeBundle {
                            condition,
                            edge_bundle: IncomingEdgeBundle {
                                target,
                                accumulated_count: total_edge_count,
                                target_inputs,
                            },
                        },
                    );
                }
                Deferred::Return { value_count } => {
                    assert!(deferred_return.is_none());
                    deferred_return = Some(outputs.by_ref().take(value_count).collect());
                }
            }
        }

        let mut children = EntityList::empty();
        children.insert_last(select_node, &mut self.func_def_body.control_nodes);
        PartialControlRegion {
            children,
            deferred_edges,
            deferred_return,
        }
    }

    /// When structurization is only partial, and there remain unclaimed regions,
    /// they have to be reintegrated into the CFG, putting back `ControlInst`s
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

        let PartialControlRegion {
            children,
            deferred_edges,
            deferred_return,
        } = partial_control_region;

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
        let mut deferred_edge_targets =
            deferred_edges
                .target_to_deferred
                .into_iter()
                .map(|(_, deferred)| {
                    (
                        deferred.condition,
                        (
                            deferred.edge_bundle.target,
                            deferred.edge_bundle.target_inputs,
                        ),
                    )
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

            let condition = Some(condition).filter(|_| else_target_and_inputs.is_some());
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
            ctor: ConstCtor::SpvInst(wk.OpUndef.into()),
            ctor_args: [].into_iter().collect(),
        })
    }
}
