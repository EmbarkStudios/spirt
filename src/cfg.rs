//! Control-flow graph (CFG) abstractions and utilities.

use crate::{
    spv, AttrSet, ControlNode, ControlNodeKind, ControlRegion, EntityList, EntityOrientedDenseMap,
    EntityOrientedMapKey, FuncAt, FuncDefBody, FxIndexMap, Value,
};
use smallvec::SmallVec;

/// The control-flow graph (CFG) of a function, as control-flow instructions
/// (`ControlInst`s) attached to `ControlNode`-relative CFG points (`ControlPoint`s).
#[derive(Clone, Default)]
pub struct ControlFlowGraph {
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

impl ControlFlowGraph {
    /// Iterate over all `ControlPoint`s reachable through the CFG for `func_def_body`,
    /// in reverse post-order (RPO).
    ///
    /// RPO iteration over a CFG provides certain guarantees, most importantly
    /// that SSA definitions are visited before any of their uses.
    pub fn rev_post_order(
        &self,
        func_def_body: &FuncDefBody,
    ) -> impl DoubleEndedIterator<Item = ControlPoint> {
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

/// The logical continuation of a `ControlRegion` (used by `traverse`).
enum ControlRegionSuccessor<'a> {
    /// No structural exit allowed, only `ControlInst`.
    Unstructured,

    /// Structural return implied by leaving a function body.
    Return,

    /// The `ControlRegion` has a parent `ControlNode`, which must also be exited.
    ExitParent {
        parent: ControlNode,
        parent_region_successor: &'a ControlRegionSuccessor<'a>,
    },
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
        pre_order_visit: &mut impl FnMut(ControlPoint),
        post_order_visit: &mut impl FnMut(ControlPoint),
    ) {
        let body_children = func_def_body.body.children.iter();
        let body_entry = ControlPoint::Entry(body_children.first);
        let body_exit = ControlPoint::Exit(body_children.last);

        let body_successor = if self.control_insts.get(body_exit).is_some() {
            ControlRegionSuccessor::Unstructured
        } else {
            ControlRegionSuccessor::Return
        };

        self.traverse(
            func_def_body.at(body_entry),
            &body_successor,
            incoming_edge_counts,
            pre_order_visit,
            post_order_visit,
        );
    }

    fn traverse(
        &self,
        func_at_point: FuncAt<ControlPoint>,
        region_successor: &ControlRegionSuccessor<'_>,
        incoming_edge_counts: &mut EntityOrientedDenseMap<ControlPoint, IncomingEdgeCount>,
        pre_order_visit: &mut impl FnMut(ControlPoint),
        post_order_visit: &mut impl FnMut(ControlPoint),
    ) {
        let point = func_at_point.position;

        // FIXME(eddyb) `EntityOrientedDenseMap` should have an `entry` API.
        if let Some(existing_count) = incoming_edge_counts.get_mut(point) {
            *existing_count += IncomingEdgeCount::ONE;
            return;
        }
        incoming_edge_counts.insert(point, IncomingEdgeCount::ONE);

        pre_order_visit(point);

        let mut visit_target = |target, new_region_successor: &_| {
            self.traverse(
                func_at_point.at(target),
                new_region_successor,
                incoming_edge_counts,
                pre_order_visit,
                post_order_visit,
            );
        };

        let control_node = point.control_node();
        let control_node_def = &func_at_point.control_nodes[control_node];

        let mut used_unstructured_control_inst = false;
        match point {
            // Entering a `ControlNode` depends entirely on the `ControlNodeKind`.
            ControlPoint::Entry(_) => {
                let child_regions: &[ControlRegion] = match control_node_def.kind {
                    // Blocks don't have `ControlInst`s attached to their `Entry`,
                    // only to their `Exit`, so we pretend here there is an edge
                    // between their `Entry` and `Exit` points.
                    ControlNodeKind::Block { .. } => {
                        visit_target(ControlPoint::Exit(control_node), region_successor);
                        &[]
                    }

                    ControlNodeKind::UnstructuredMerge => {
                        unreachable!("cfg: `UnstructuredMerge` can only be exited, not entered");
                    }
                };
                for region in child_regions {
                    visit_target(
                        ControlPoint::Entry(region.children.iter().first),
                        &ControlRegionSuccessor::ExitParent {
                            parent: control_node,
                            parent_region_successor: region_successor,
                        },
                    )
                }
            }

            // Exiting a `ControlNode` chains to a sibling/parent.
            ControlPoint::Exit(_) => {
                match control_node_def.next_in_list() {
                    // Enter the next sibling in the `ControlRegion`, if one exists.
                    Some(next_control_node) => {
                        visit_target(ControlPoint::Entry(next_control_node), region_successor);
                    }

                    // Exit the parent `ControlNode`, if one exists.
                    None => match region_successor {
                        ControlRegionSuccessor::Unstructured => {
                            let control_inst = self.control_insts.get(point).expect(
                                "cfg: missing `ControlInst`, despite \
                                 having left structured control-flow",
                            );
                            // With a `ControlInst`, it can be followed regardless of `ControlNodeKind`.
                            for &target in &control_inst.targets {
                                visit_target(target, &ControlRegionSuccessor::Unstructured);
                            }
                            used_unstructured_control_inst = true;
                        }

                        ControlRegionSuccessor::Return => {}

                        &ControlRegionSuccessor::ExitParent {
                            parent,
                            parent_region_successor,
                        } => visit_target(ControlPoint::Exit(parent), parent_region_successor),
                    },
                }
            }
        }

        if !used_unstructured_control_inst {
            assert!(
                self.control_insts.get(point).is_none(),
                "cfg: `ControlPoint` has associated `ControlInst`, but didn't \
                 get used because structured control-flow took precedence"
            );
        }

        post_order_visit(point);
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
            if let Some(children) = children {
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
    }

    fn try_claim_edge_bundle(
        &mut self,
        edge_bundle: IncomingEdgeBundle,
    ) -> Result<PartialControlRegion, ()> {
        if self.incoming_edge_counts[edge_bundle.target] != edge_bundle.accumulated_count {
            return Err(());
        }

        // Entering a block implies the block itself, and also exiting the block.
        if let ControlPoint::Entry(control_node) = edge_bundle.target {
            if let ControlNodeKind::Block { .. } =
                self.func_def_body.control_nodes[control_node].kind
            {
                let mut region = self
                    .try_claim_edge_bundle(IncomingEdgeBundle {
                        target: ControlPoint::Exit(control_node),
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
