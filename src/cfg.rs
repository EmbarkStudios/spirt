//! Control-flow graph (CFG) abstractions and utilities.

use crate::{
    spv, AttrSet, ControlNode, ControlNodeKind, ControlRegion, EntityList, EntityListIter,
    EntityOrientedDenseMap, EntityOrientedMapKey, FuncAt, FuncDefBody, FxIndexMap, Value,
};
use smallvec::SmallVec;

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

#[derive(Clone)]
pub enum SelectionKind {
    /// Conditional branch on boolean condition, i.e. `if`-`else`.
    BoolCond,

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
pub struct ControlCursor<'a, 'p, P> {
    pub position: P,
    pub parent: Option<&'p ControlCursor<'a, 'p, (ControlNode, &'a ControlRegion)>>,
}

impl<'a> FuncAt<'a, ControlCursor<'a, '_, ControlPoint>> {
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
                let child_regions: &[ControlRegion] = match control_node_def.kind {
                    ControlNodeKind::Block { .. } => &[],

                    ControlNodeKind::UnstructuredMerge => {
                        unreachable!("cfg: `UnstructuredMerge` can only be exited, not entered");
                    }
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
                            Some(&parent_control_region.outputs[..]),
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
        mut f: impl FnMut(FuncAt<'a, ControlCursor<'a, '_, ControlPoint>>) -> Result<(), E>,
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
        f: &mut impl FnMut(FuncAt<'a, ControlCursor<'a, '_, ControlPoint>>) -> Result<(), E>,
        parent: Option<&ControlCursor<'a, '_, (ControlNode, &'a ControlRegion)>>,
    ) -> Result<(), E> {
        for func_at_control_node in self {
            let child_regions: &[ControlRegion] = match func_at_control_node.def().kind {
                ControlNodeKind::Block { .. } => &[],

                ControlNodeKind::UnstructuredMerge => {
                    unreachable!("cfg: `UnstructuredMerge` can only be exited, not entered");
                }
            };

            let control_node = func_at_control_node.position;
            f(self.at(ControlCursor {
                position: ControlPoint::Entry(control_node),
                parent,
            }))?;
            for region in child_regions {
                self.at(region.children)
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
        let body_children = func_def_body.body.children.iter();
        let body_range = ControlPointRange::LinearChain(body_children);
        let body_exit = ControlPoint::Exit(body_children.last);

        if self.control_insts.get(body_exit).is_some() {
            self.traverse(
                func_def_body.at(body_range),
                incoming_edge_counts,
                pre_order_visit,
                post_order_visit,
            );
        } else {
            // Entirely structured function body, no CFG traversal needed.

            // FIXME(eddyb) this feels potentially wasteful, but it can probably
            // be alleviated by `FuncDefBody` not keeping its `ControlFlowGraph`
            // once structurization is complete, and not ending up in traversal
            // APIs like this, afterwards, in the first place.
            incoming_edge_counts.insert(
                ControlPoint::Entry(body_children.first),
                IncomingEdgeCount::ONE,
            );

            pre_order_visit(body_range);
            post_order_visit(body_range);
        }
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
    func_def_body: &'a mut FuncDefBody,
    incoming_edge_counts: EntityOrientedDenseMap<ControlPoint, IncomingEdgeCount>,
}

/// An "(incoming) edge bundle" is a subset of the edges into a single `target`.
///
/// When `accumulated_count` reaches the total `IncomingEdgeCount` for `target`,
/// that `IncomingEdgeBundle` is said to "effectively own" its `target` (akin to
/// the more commonly used CFG domination relation, but more "incremental").
#[derive(Copy, Clone)]
struct IncomingEdgeBundle {
    target: ControlPoint,
    accumulated_count: IncomingEdgeCount,
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
    /// Leave structural control-flow, using the `ControlInst`.
    //
    // FIXME(eddyb) fully implement CFG structurization, which shouldn't need this.
    Unstructured(ControlInst),
}

impl<'a> Structurizer<'a> {
    pub fn new(func_def_body: &'a mut FuncDefBody) -> Self {
        let mut incoming_edge_counts = EntityOrientedDenseMap::new();
        func_def_body.cfg.traverse_whole_func(
            func_def_body,
            &mut incoming_edge_counts,
            &mut |_| {},
            &mut |_| {},
        );
        Self {
            func_def_body,
            incoming_edge_counts,
        }
    }

    pub fn try_structurize_func(mut self) {
        let entry_edge = IncomingEdgeBundle {
            target: ControlPoint::Entry(self.func_def_body.body.children.iter().first),
            accumulated_count: IncomingEdgeCount::ONE,
        };
        if let Ok(body_region) = self.try_claim_edge_bundle(entry_edge) {
            let PartialControlRegion {
                children,
                successor,
            } = body_region;

            // FIXME(eddyb) make e.g. a dummy block when childless.
            let children = children.expect(
                "cfg::Structurizer::try_structurize_func: did not expect blockless function",
            );

            self.func_def_body.body.children = children;
            match successor {
                PartialControlRegionSuccessor::Unstructured(control_inst) => {
                    self.func_def_body
                        .cfg
                        .control_insts
                        .insert(ControlPoint::Exit(children.iter().last), control_inst);
                }
            }
        }
    }

    fn try_claim_edge_bundle(
        &mut self,
        edge_bundle: IncomingEdgeBundle,
    ) -> Result<PartialControlRegion, ()> {
        if self.incoming_edge_counts[edge_bundle.target] != edge_bundle.accumulated_count {
            return Err(());
        }

        // Entering a block implies the block itself, and also exiting the block.
        //
        // FIXME(eddyb) replace this with something more general about encountering
        // already-structured regions and "bringing them into the fold".
        if let ControlPoint::Entry(control_node) = edge_bundle.target {
            if let ControlNodeKind::Block { .. } =
                self.func_def_body.control_nodes[control_node].kind
            {
                let exit_point = ControlPoint::Exit(control_node);

                // HACK(eddyb) the initial `incoming_edge_counts` can't account
                // for such edges internal to structured control-flow, so they
                // have to be supplanted here.
                assert!(
                    self.incoming_edge_counts
                        .insert(exit_point, IncomingEdgeCount::ONE)
                        .is_none()
                );

                let mut region = self
                    .try_claim_edge_bundle(IncomingEdgeBundle {
                        target: exit_point,
                        accumulated_count: IncomingEdgeCount::ONE,
                    })
                    .unwrap();

                region.children = Some(EntityList::insert_first(
                    region.children,
                    control_node,
                    &mut self.func_def_body.control_nodes,
                ));

                return Ok(region);
            }
        }

        let control_inst = self
            .func_def_body
            .cfg
            .control_insts
            .remove(edge_bundle.target)
            .unwrap_or_else(|| {
                unreachable!(
                    "cfg::Structurizer::try_claim_edge_bundle: already claimed \
                     or the CFG wasn't unstructured in the first place"
                )
            });

        {
            let ControlInst {
                attrs,
                kind,
                inputs,
                targets,
                target_merge_outputs,
            } = &control_inst;

            // FIXME(eddyb) this loses `attrs`.
            let _ = attrs;

            // FIXME(eddyb) support more than merely linear control-flow.
            if target_merge_outputs.is_empty() {
                if let ControlInstKind::Branch = kind {
                    assert!(inputs.is_empty() && targets.len() == 1);
                    let branch_edge = IncomingEdgeBundle {
                        target: targets[0],
                        accumulated_count: IncomingEdgeCount::ONE,
                    };
                    if let Ok(region) = self.try_claim_edge_bundle(branch_edge) {
                        return Ok(region);
                    }
                }
            }
        }

        Ok(PartialControlRegion {
            children: None,
            successor: PartialControlRegionSuccessor::Unstructured(control_inst),
        })
    }
}
