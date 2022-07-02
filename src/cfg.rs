//! Control-flow graph (CFG) abstractions and utilities.

use crate::func_at::FuncAt;
use crate::{
    spv, AttrSet, Const, ConstCtor, ConstDef, Context, ControlNode, ControlNodeDef,
    ControlNodeKind, ControlNodeOutputDecl, ControlRegion, ControlRegionDef,
    ControlRegionInputDecl, EntityList, EntityListIter, EntityOrientedDenseMap,
    EntityOrientedMapKey, FuncDefBody, FxIndexMap, SelectionKind, Type, TypeCtor, TypeDef, Value,
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

    /// Scrutinee type for `SelectionKind::BoolCond`.
    type_bool: Type,

    /// Scrutinee value for `SelectionKind::BoolCond`, for the "then" case.
    const_true: Const,

    /// Scrutinee value for `SelectionKind::BoolCond`, for the "else" case.
    const_false: Const,

    func_def_body: &'a mut FuncDefBody,
    incoming_edge_counts: EntityOrientedDenseMap<ControlPoint, IncomingEdgeCount>,

    /// Keyed by the input to `structurize_region_from` (the start `ControlPoint`),
    /// and describing the state of that partial structurization step.
    ///
    /// See also `StructurizeRegionState`'s docs.
    //
    // FIXME(eddyb) use `EntityOrientedDenseMap` (which lacks iteration by design).
    structurize_region_state: FxIndexMap<ControlPoint, StructurizeRegionState>,

    /// Accumulated replacements (caused by `target_merge_output`s), i.e.:
    /// `Value::ControlNodeOutput { control_node, output_idx }` must be replaced
    /// with `control_node_output_replacements[control_node][output_idx]`, as
    /// the original `control_node` cannot be meaningfully reused.
    control_node_output_replacements: EntityOrientedDenseMap<ControlNode, SmallVec<[Value; 2]>>,
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
    // but that messes with the ability of `ControlPoint` to describe the two
    // endpoints of a `ControlRegion` (should `ControlPoint` be changed to be
    // relative to `ControlRegion`s instead of `ControlNode`s? unsure for now).
    children: Option<EntityList<ControlNode>>,

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
            control_node_output_replacements: EntityOrientedDenseMap::new(),
        }
    }

    pub fn structurize_func(mut self) {
        // Don't even try to re-structurize functions.
        if self.func_def_body.unstructured_cfg.is_none() {
            return;
        }

        let body_entry =
            ControlPoint::Entry(self.func_def_body.at_body().def().children.iter().first);
        let body_region = self.claim_or_defer_single_edge(body_entry, SmallVec::new());

        if body_region.deferred_edges.target_to_deferred.is_empty() {
            // Structured return, the function is fully structurized.
            //
            // FIXME(eddyb) also support structured return when the whole body
            // is divergent, by generating undef constants (needs access to the
            // whole `FuncDecl`, not just `FuncDefBody`, to get the right types).
            if let Some(return_values) = body_region.deferred_return {
                let body_children = body_region
                    .children
                    .unwrap_or_else(|| self.empty_control_region_children());

                let body_def = self.func_def_body.at_mut_body().def();
                body_def.children = body_children;
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
                body_entry,
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
    /// collected while structurizing (like `control_node_output_replacements`).
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
                Value::ControlNodeOutput {
                    control_node,
                    output_idx,
                } => Some(
                    self.control_node_output_replacements.get(control_node)?[output_idx as usize],
                ),
                _ => None,
            }));
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

            // If the body starts with an `UnstructuredMerge`, receiving values
            // from both the loop entry and the backedge, that has to become
            // "loop state" (with values being passed to `body` `inputs`).
            let body_inputs: SmallVec<[_; 2]> = {
                let header_merge_output_decls = match target {
                    ControlPoint::Exit(header_merge_node) => {
                        let header_merge_node_def = self.func_def_body.at(header_merge_node).def();
                        assert!(matches!(
                            header_merge_node_def.kind,
                            ControlNodeKind::UnstructuredMerge
                        ));
                        &header_merge_node_def.outputs
                    }
                    _ => &[][..],
                };
                header_merge_output_decls
                    .iter()
                    .map(
                        |&ControlNodeOutputDecl { attrs, ty }| ControlRegionInputDecl { attrs, ty },
                    )
                    .collect()
            };
            let initial_inputs = edge_bundle.target_merge_outputs;
            let body_outputs = backedge.target_merge_outputs;
            assert_eq!(initial_inputs.len(), body_inputs.len());
            assert_eq!(body_outputs.len(), body_inputs.len());

            let body_children = region
                .children
                .unwrap_or_else(|| self.empty_control_region_children());
            let body = self.func_def_body.control_regions.define(
                self.cx,
                ControlRegionDef {
                    inputs: body_inputs,
                    children: body_children,
                    outputs: body_outputs,
                },
            );

            // The last step of turning `edge_bundle` into the complete merge of
            // the loop entry and its backedge, is to supply the structured
            // `body` `inputs` as the `target_merge_outputs`, so that they can
            // be inserted into `control_node_output_replacements` below.
            edge_bundle.target_merge_outputs = initial_inputs
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
            region.children = Some(EntityList::insert_last(
                None,
                loop_node,
                &mut self.func_def_body.control_nodes,
            ));
        }

        if !edge_bundle.target_merge_outputs.is_empty() {
            assert!(matches!(target, ControlPoint::Exit(_)));
            self.control_node_output_replacements
                .insert(target.control_node(), edge_bundle.target_merge_outputs);
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

        /// Marker error type for unhandled `ControlInst`s below.
        struct UnsupportedControlInst(ControlInst);

        let region = match control_inst {
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

            Ok(control_inst) => {
                let ControlInst {
                    attrs,
                    kind,
                    inputs,
                    targets,
                    target_merge_outputs,
                } = control_inst;

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

                match kind {
                    ControlInstKind::Unreachable => {
                        assert_eq!((inputs.len(), child_regions.len()), (0, 0));

                        // FIXME(eddyb) this may result in lost optimizations over
                        // actually encoding it in `ControlNode`/`ControlRegion`
                        // (e.g. a new `ControlKind`, or replacing region `outputs`),
                        // but it's simpler to handle it like this.
                        Ok(PartialControlRegion {
                            children: None,
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
                            target_merge_outputs,
                        }))
                    }

                    ControlInstKind::Return => {
                        assert_eq!(child_regions.len(), 0);

                        Ok(PartialControlRegion {
                            children: None,
                            deferred_edges: DeferredEdgeBundleSet {
                                target_to_deferred: [].into_iter().collect(),
                            },
                            deferred_return: Some(inputs),
                        })
                    }

                    ControlInstKind::Branch => {
                        assert_eq!((inputs.len(), child_regions.len()), (0, 1));

                        Ok(child_regions.into_iter().nth(0).unwrap())
                    }

                    ControlInstKind::SelectBranch(kind) => {
                        assert_eq!(inputs.len(), 1);

                        let scrutinee = inputs[0];

                        Ok(self.structurize_select(kind, scrutinee, child_regions))
                    }
                }
            }
        };

        let mut region = region.unwrap_or_else(|UnsupportedControlInst(control_inst)| {
            // HACK(eddyb) this only remains used for `ExitInvocation`.
            assert!(control_inst.targets.is_empty());

            // HACK(eddyb) attach the unsupported `ControlInst` to a fresh
            // new "proxy" `ControlNode`, that can then be the target of
            // a deferred edge, specially crafted to be unclaimable.
            let proxy = self.func_def_body.control_nodes.define(
                self.cx,
                ControlNodeDef {
                    kind: ControlNodeKind::Block { insts: None },
                    outputs: [].into_iter().collect(),
                }
                .into(),
            );
            let (proxy_entry, proxy_exit) = (ControlPoint::Entry(proxy), ControlPoint::Exit(proxy));
            self.func_def_body
                .unstructured_cfg
                .as_mut()
                .unwrap()
                .control_insts
                .insert(proxy_exit, control_inst);
            self.structurize_region_state
                .insert(proxy_entry, StructurizeRegionState::InProgress);
            self.incoming_edge_counts
                .insert(proxy_entry, IncomingEdgeCount::ONE);
            let deferred_proxy = DeferredEdgeBundle {
                condition: Value::Const(self.const_true),
                edge_bundle: IncomingEdgeBundle {
                    target: proxy_entry,
                    accumulated_count: IncomingEdgeCount::default(),
                    target_merge_outputs: [].into_iter().collect(),
                },
            };

            PartialControlRegion {
                children: None,
                deferred_edges: DeferredEdgeBundleSet {
                    target_to_deferred: [deferred_proxy]
                        .into_iter()
                        .map(|d| (d.edge_bundle.target, d))
                        .collect(),
                },
                deferred_return: None,
            }
        });

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
                        target_merge_outputs: mem::take(&mut edge_bundle.target_merge_outputs),
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
                children: None,
                ..region
            };
            let else_is_unreachable = else_region.deferred_edges.target_to_deferred.is_empty()
                && else_region.deferred_return.is_none();

            // `then_region` is only taken if `condition` holds, except that
            // `condition` can be ignored when `else_region` is unreachable.
            let merged_region = if else_is_unreachable {
                then_region
            } else {
                self.structurize_select(
                    SelectionKind::BoolCond,
                    condition,
                    [then_region, else_region].into_iter().collect(),
                )
            };

            // Prepend the original children to the freshly merged region.
            region = PartialControlRegion {
                children: EntityList::concat(
                    region.children,
                    merged_region.children,
                    &mut self.func_def_body.control_nodes,
                ),
                ..merged_region
            };
        }

        // Try to extract (deferred) backedges (which later get turned into loops).
        let backedge = region
            .deferred_edges
            .target_to_deferred
            .remove(&first_point);

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
                    children: None,
                    deferred_edges: DeferredEdgeBundleSet {
                        target_to_deferred: [].into_iter().collect(),
                    },
                    deferred_return: None,
                });
        }

        // Gather the full set of deferred edges (and returns), along with the
        // necessary information for the `Select`'s `ControlNodeOutputDecl`s.
        let mut deferred_edges_to_output_count_and_total_edge_count = FxIndexMap::default();
        let mut deferred_return_types = None;
        for case in &cases {
            for (&target, deferred) in &case.deferred_edges.target_to_deferred {
                let output_count = deferred.edge_bundle.target_merge_outputs.len();

                let (old_output_count, accumulated_edge_count) =
                    deferred_edges_to_output_count_and_total_edge_count
                        .entry(target)
                        .or_insert((output_count, IncomingEdgeCount::default()));
                assert_eq!(*old_output_count, output_count);
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
            deferred_edges_to_output_count_and_total_edge_count.len() > 1
                || deferred_return_types.is_some();

        // The `Select` outputs are the concatenation of:
        // * for each unique `deferred_edges` target:
        //   * condition (only if `needs_per_deferred_edge_condition` - see above)
        //   * `target_merge_outputs`
        // * `deferred_return` values (if needed)
        //
        // FIXME(eddyb) some of this could maybe be generalized to deferred infra.
        enum Deferred {
            Edge {
                target: ControlPoint,
                // NOTE(eddyb) not including condition, only `target_merge_outputs`.
                target_output_count: usize,

                /// Sum of `accumulated_count` for this `target` across all `cases`.
                total_edge_count: IncomingEdgeCount,
            },
            Return {
                value_count: usize,
            },
        }
        let deferreds = || {
            deferred_edges_to_output_count_and_total_edge_count
                .iter()
                .map(
                    |(&target, &(target_output_count, total_edge_count))| Deferred::Edge {
                        target,
                        target_output_count,
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
                        target_output_count,
                        ..
                    } => (needs_per_deferred_edge_condition as usize) + target_output_count,
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
                    target_output_count,
                    ..
                } => {
                    let target_outputs = match target {
                        ControlPoint::Entry(_) => &[][..],
                        ControlPoint::Exit(target_node) => {
                            &self.func_def_body.at(target_node).def().outputs
                        }
                    };
                    assert_eq!(target_outputs.len(), target_output_count);

                    if needs_per_deferred_edge_condition {
                        output_decls.push(output_decl_from_ty(self.type_bool));
                    }
                    output_decls.extend(target_outputs.iter().map(|o| output_decl_from_ty(o.ty)));
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
                            target_output_count,
                            ..
                        } => match deferred_edges.target_to_deferred.remove(&target) {
                            Some(DeferredEdgeBundle {
                                condition,
                                edge_bundle,
                            }) => (Some(condition), Ok(edge_bundle.target_merge_outputs)),

                            None => (
                                Some(Value::Const(self.const_false)),
                                Err(target_output_count),
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
                        Err(missing_output_count) => {
                            let decls_for_missing_outputs =
                                &output_decls[outputs.len()..][..missing_output_count];
                            outputs.extend(
                                decls_for_missing_outputs
                                    .iter()
                                    .map(|output| Value::Const(self.const_undef(output.ty))),
                            );
                        }
                    }
                }

                // All deferrals must have been converted into outputs above.
                assert!(deferred_edges.target_to_deferred.is_empty() && deferred_return.is_none());
                assert_eq!(outputs.len(), output_decls.len());

                let children = children.unwrap_or_else(|| self.empty_control_region_children());
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
                    target_output_count,
                    total_edge_count,
                } => {
                    let condition = if needs_per_deferred_edge_condition {
                        outputs.next().unwrap()
                    } else {
                        Value::Const(self.const_true)
                    };
                    let target_merge_outputs = outputs.by_ref().take(target_output_count).collect();

                    deferred_edges.target_to_deferred.insert(
                        target,
                        DeferredEdgeBundle {
                            condition,
                            edge_bundle: IncomingEdgeBundle {
                                target,
                                accumulated_count: total_edge_count,
                                target_merge_outputs,
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

        PartialControlRegion {
            children: Some(EntityList::insert_last(
                None,
                select_node,
                &mut self.func_def_body.control_nodes,
            )),
            deferred_edges,
            deferred_return,
        }
    }

    /// When structurization is only partial, and there remain unclaimed regions,
    /// they have to be reintegrated into the CFG, putting back `ControlInst`s
    /// where `structurize_region_from` has taken them (only around entry/exit).
    ///
    /// This function handles one region at a time to make it more manageable,
    /// despite it having a single call site (in a loop in `structurize_func`).
    fn repair_unclaimed_region(
        &mut self,
        first_point: ControlPoint,
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

        let children = children.map(|list| list.iter());

        // First off, ensure `first_point` reaches `children`, which may not be
        // the case if `first_point` is an `Exit` out of an `UnstructuredMerge`.
        match first_point {
            ControlPoint::Entry(first_node) => {
                assert!(children.map(|list| list.first) == Some(first_node));
            }
            ControlPoint::Exit(unstructured_merge_node) => {
                assert!(matches!(
                    self.func_def_body.at(unstructured_merge_node).def().kind,
                    ControlNodeKind::UnstructuredMerge
                ));

                // Reaching the children requires a branch that must've been
                // taken by `structurize_region_from`, place it back.
                if let Some(children) = children {
                    let entry_control_inst = ControlInst {
                        attrs: AttrSet::default(),
                        kind: ControlInstKind::Branch,
                        inputs: [].into_iter().collect(),
                        targets: [ControlPoint::Entry(children.first)].into_iter().collect(),
                        target_merge_outputs: FxIndexMap::default(),
                    };
                    assert!(
                        self.func_def_body
                            .unstructured_cfg
                            .as_mut()
                            .unwrap()
                            .control_insts
                            .insert(first_point, entry_control_inst)
                            .is_none()
                    );
                }
            }
        }

        // Exiting the region must be done from the last `ControlNode` reachable
        // from `first_point`, which in the absence of any children, must be the
        // very `UnstructuredMerge` that `first_point` is an `Exit` out of.
        let last_node = children
            .map(|list| list.last)
            .unwrap_or(first_point.control_node());

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
                            deferred.edge_bundle.target_merge_outputs,
                        ),
                    )
                });
        let mut last_node = Some(last_node);
        while let Some((condition, then_target_and_merge_outputs)) = deferred_edge_targets.next() {
            let branch_point = ControlPoint::Exit(last_node.take().unwrap());
            let else_target_and_merge_outputs =
                if deferred_edge_targets.len() <= 1 && deferred_return.is_none() {
                    // At most one deferral left, so it can be used as the "else"
                    // case, or the branch left unconditional in its absence.
                    deferred_edge_targets.next().map(|(_, t)| t)
                } else {
                    // Either more branches, or a deferred return, are needed, so
                    // the "else" case must be a `ControlNode` (a new empty block)
                    // that itself can have a `ControlInst` attached to it later on.
                    let new_empty_block = self.empty_control_region_children().iter().first;
                    last_node = Some(new_empty_block);
                    Some((
                        ControlPoint::Entry(new_empty_block),
                        [].into_iter().collect(),
                    ))
                };

            let condition = Some(condition).filter(|_| else_target_and_merge_outputs.is_some());
            let branch_control_inst = ControlInst {
                attrs: AttrSet::default(),
                kind: if condition.is_some() {
                    ControlInstKind::SelectBranch(SelectionKind::BoolCond)
                } else {
                    ControlInstKind::Branch
                },
                inputs: condition.into_iter().collect(),
                targets: [&then_target_and_merge_outputs]
                    .into_iter()
                    .chain(&else_target_and_merge_outputs)
                    .map(|&(target, _)| target)
                    .collect(),
                target_merge_outputs: [then_target_and_merge_outputs]
                    .into_iter()
                    .chain(else_target_and_merge_outputs)
                    .map(|(target, outputs)| (target.control_node(), outputs))
                    .filter(|(_, outputs)| !outputs.is_empty())
                    .collect(),
            };
            assert!(
                self.func_def_body
                    .unstructured_cfg
                    .as_mut()
                    .unwrap()
                    .control_insts
                    .insert(branch_point, branch_control_inst)
                    .is_none()
            );
        }

        let final_point = match last_node {
            Some(node) => ControlPoint::Exit(node),
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
                target_merge_outputs: FxIndexMap::default(),
            }
        };
        assert!(
            self.func_def_body
                .unstructured_cfg
                .as_mut()
                .unwrap()
                .control_insts
                .insert(final_point, final_control_inst)
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
