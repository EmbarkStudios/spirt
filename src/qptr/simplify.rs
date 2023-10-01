//! [`QPtr`](crate::TypeKind::QPtr) simplification passes.

// HACK(eddyb) sharing layout code with other modules.
use super::layout::*;

use super::{shapes, QPtrOp};
use crate::func_at::{FuncAt, FuncAtMut};
use crate::visit::{InnerVisit, Visitor};
use crate::{
    vector, AttrSet, Const, ConstDef, ConstKind, Context, ControlNodeOutputDecl, ControlRegion,
    ControlRegionDef, ControlRegionInputDecl, DataInst, DataInstDef, DataInstForm, DataInstKind,
    Func, FuncDefBody, FxIndexMap, FxIndexSet, GlobalVar, Type, TypeKind,
};
use crate::{ControlNode, Value};
use crate::{ControlNodeKind, DataInstFormDef};
use smallvec::SmallVec;
use std::collections::BTreeMap;
use std::num::NonZeroU32;
use std::ops::{Bound, Range};
use std::rc::Rc;
use std::{mem, slice};

/// Split all function-local variables in `func_def_body` into independent ones.
//
// FIXME(eddyb) reduce the cost of creating all the per-partition local variables
// by feeding partitions to `propagate_contents_of_local_vars_in_func` directly.
pub fn partition_local_vars_in_func(
    cx: Rc<Context>,
    config: &LayoutConfig,
    func_def_body: &mut FuncDefBody,
) {
    let vars = {
        let mut collector = CollectLocalVarPartitions {
            cx: cx.clone(),
            layout_cache: LayoutCache::new(cx.clone(), config),
            vars: FxIndexMap::default(),
        };
        func_def_body.inner_visit_with(&mut collector);
        collector.vars
    };

    let qptr_type = cx.intern(TypeKind::QPtr);

    // Create new variables for all partitions, and replace their respective uses.
    for (original_var_inst, var) in vars {
        let original_var_qptr = Value::DataInstOutput { inst: original_var_inst, output_idx: 0 };

        // Also shrink the original variable, if necessary.
        if var.zero_offset_partition_size < var.original_layout.size {
            func_def_body.at_mut(original_var_inst).def().form = cx.intern(DataInstFormDef {
                kind: QPtrOp::FuncLocalVar(shapes::MemLayout {
                    size: var.zero_offset_partition_size,
                    ..var.original_layout
                })
                .into(),
                output_types: [qptr_type].into_iter().collect(),
            });
        }

        for (partition_offset, partition) in var.non_zero_offset_to_partition {
            let align_for_offset = 1 << partition_offset.trailing_zeros();

            let partition_var_inst = func_def_body.data_insts.define(
                &cx,
                DataInstDef {
                    // FIXME(eddyb) preserve at least debuginfo attrs.
                    attrs: Default::default(),
                    form: cx.intern(DataInstFormDef {
                        kind: QPtrOp::FuncLocalVar(shapes::MemLayout {
                            align: var.original_layout.align.min(align_for_offset),
                            legacy_align: var.original_layout.legacy_align.min(align_for_offset),
                            size: partition.size,
                        })
                        .into(),
                        output_types: [qptr_type].into_iter().collect(),
                    }),
                    inputs: Default::default(),
                }
                .into(),
            );

            match &mut func_def_body.control_nodes[var.parent_block].kind {
                ControlNodeKind::Block { insts } => {
                    // FIXME(eddyb) this could use an `insert_after`, to avoid
                    // having all the partitions end up before the original.
                    insts.insert_before(
                        partition_var_inst,
                        original_var_inst,
                        &mut func_def_body.data_insts,
                    );
                }
                _ => unreachable!(),
            }

            let partition_var_qptr =
                Value::DataInstOutput { inst: partition_var_inst, output_idx: 0 };

            // FIMXE(eddyb) when `QPtrOp::Offset` ends up with a `0` offset,
            // some further simplifications are possible, but it's not that
            // relevant for now, as we're mainly interested in loads/stores.
            for use_inst in partition.uses {
                let data_inst_def = func_def_body.at_mut(use_inst).def();

                assert!(
                    mem::replace(&mut data_inst_def.inputs[0], partition_var_qptr)
                        == original_var_qptr
                );

                let mut data_inst_form_def = cx[data_inst_def.form].clone();
                match &mut data_inst_form_def.kind {
                    DataInstKind::QPtr(
                        QPtrOp::Offset(offset) | QPtrOp::Load { offset } | QPtrOp::Store { offset },
                    ) => {
                        *offset =
                            offset.checked_sub(partition_offset.get().try_into().unwrap()).unwrap();
                    }
                    _ => unreachable!(),
                }
                data_inst_def.form = cx.intern(data_inst_form_def);
            }
        }
    }
}

struct CollectLocalVarPartitions<'a> {
    cx: Rc<Context>,
    layout_cache: LayoutCache<'a>,
    vars: FxIndexMap<DataInst, LocalVarPartitions>,
}

struct LocalVarPartitions {
    parent_block: ControlNode,
    original_layout: shapes::MemLayout,
    // HACK(eddyb) offset `0` reuses the original variable and is tracked separately,
    // to reduce the cost for both the collection, and to make replacement a noop.
    zero_offset_partition_size: u32,
    non_zero_offset_to_partition: BTreeMap<NonZeroU32, Partition>,
}

#[derive(Default)]
struct Partition {
    size: u32,

    /// All the `DataInst`s that have a `QPtr` input and an immediate offset
    /// (`QPtrOp::{Offset,Load,Store}`), which are updated after partitioning.
    uses: SmallVec<[DataInst; 4]>,
}

impl LocalVarPartitions {
    /// Remove all partitions and prevent any further ones from being added
    /// (typically only needed for variables used in unknown ways).
    fn forfeit_partitioning(&mut self) {
        self.zero_offset_partition_size = self.original_layout.size;
        mem::take(&mut self.non_zero_offset_to_partition);
    }

    /// Record a new partition range, and the `DataInst` it originated from,
    /// merging ranges and uses with existing ones, in case of overlaps.
    fn add_use(&mut self, range: Range<u32>, use_inst: DataInst) {
        // FIXME(eddyb) the logic below is not amenable to ZSTs.
        if range.is_empty() {
            return self.forfeit_partitioning();
        }

        // The partition starting at `0` is special and does not track `uses`.
        if range.start == 0 || range.start < self.zero_offset_partition_size {
            self.zero_offset_partition_size = self.zero_offset_partition_size.max(range.end);

            // Absorb overlaps without keeping track of their `uses`.
            while let Some(entry) = self.non_zero_offset_to_partition.first_entry() {
                let partition_offset = entry.key().get();
                if range.end <= partition_offset {
                    break;
                }
                let partition = entry.remove();
                self.zero_offset_partition_size =
                    partition_offset.checked_add(partition.size).unwrap();
            }
            return;
        }

        let range = NonZeroU32::new(range.start).unwrap()..NonZeroU32::new(range.end).unwrap();
        let mut rev_overlapping_entries = self
            .non_zero_offset_to_partition
            .range_mut((Bound::Unbounded, Bound::Excluded(range.end)))
            .rev()
            .take_while(|(&partition_offset, partition)| {
                partition_offset.checked_add(partition.size).unwrap() > range.start
            });

        // Fast path: `range` begins in an existing partition, and either already
        // ends within it, or at least ends before the next existing partition
        // (the second condition is guaranteed by this being the *last* overlap).
        let mut last_overlapping_entry = rev_overlapping_entries.next();
        if let Some((&partition_offset, partition)) = &mut last_overlapping_entry {
            if partition_offset <= range.start {
                partition.size = partition.size.max(range.end.get() - partition_offset.get());
                partition.uses.push(use_inst);
                return;
            }
        }

        let rev_overlapping_entries =
            last_overlapping_entry.into_iter().chain(rev_overlapping_entries);

        // FIXME(eddyb) this is a bit inefficient but we don't have
        // cursors, so we have to buffer the `BTreeMap` keys here.
        let rev_overlapping_offsets: SmallVec<[_; 4]> =
            rev_overlapping_entries.map(|(&offset, _)| offset).collect();

        let merged_entry = rev_overlapping_offsets
            .into_iter()
            .rev()
            .map(|offset| (offset, self.non_zero_offset_to_partition.remove(&offset).unwrap()))
            .chain([(
                range.start,
                Partition {
                    size: range.end.get() - range.start.get(),
                    uses: [use_inst].into_iter().collect(),
                },
            )])
            .reduce(|(a_start, a), (b_start, b)| {
                let (a_end, b_end) =
                    (a_start.checked_add(a.size).unwrap(), b_start.checked_add(b.size).unwrap());
                let start = a_start.min(b_start);
                let mut uses = a.uses;
                uses.extend(b.uses);
                (start, Partition { size: a_end.max(b_end).get() - start.get(), uses })
            })
            .unwrap();
        self.non_zero_offset_to_partition.extend([merged_entry]);
    }
}

impl Visitor<'_> for CollectLocalVarPartitions<'_> {
    // FIXME(eddyb) this is excessive, maybe different kinds of
    // visitors should exist for module-level and func-level?
    fn visit_attr_set_use(&mut self, _: AttrSet) {}
    fn visit_type_use(&mut self, _: Type) {}
    fn visit_const_use(&mut self, _: Const) {}
    fn visit_data_inst_form_use(&mut self, _: DataInstForm) {}
    fn visit_global_var_use(&mut self, _: GlobalVar) {}
    fn visit_func_use(&mut self, _: Func) {}

    // NOTE(eddyb) uses of variables that end up here disable partitioning of
    // that variable, as they're not one of the special cases which are allowed.
    fn visit_value_use(&mut self, &v: &Value) {
        if let Value::DataInstOutput { inst, output_idx } = v {
            if let Some(var) = self.vars.get_mut(&inst) {
                assert_eq!(output_idx, 0);
                var.forfeit_partitioning();
            }
        }
    }

    // FIXME(eddyb) we can't use `visit_data_inst_def` because we need either
    // the resulting `DataInst`, or access to `FuncAt<Value>::type_of`.
    fn visit_control_node_def(&mut self, func_at_control_node: FuncAt<'_, ControlNode>) {
        if let ControlNodeKind::Block { insts } = func_at_control_node.def().kind {
            for func_at_inst in func_at_control_node.at(insts) {
                let data_inst_def = func_at_inst.def();
                let data_inst_form_def = &self.cx[data_inst_def.form];
                if let DataInstKind::QPtr(op) = &data_inst_form_def.kind {
                    let first_input_qptr_with_offset_and_access_type = match *op {
                        QPtrOp::FuncLocalVar(layout) => {
                            // FIXME(eddyb) support optional initializers.
                            if data_inst_def.inputs.is_empty() {
                                self.vars.insert(
                                    func_at_inst.position,
                                    LocalVarPartitions {
                                        parent_block: func_at_control_node.position,
                                        original_layout: layout,
                                        zero_offset_partition_size: 0,
                                        non_zero_offset_to_partition: BTreeMap::new(),
                                    },
                                );
                            }

                            None
                        }

                        // FIXME(eddyb) support more uses of `qptr`s.
                        QPtrOp::Offset(offset) => {
                            // FIXME(eddyb) we could have a narrower range here,
                            // if it was recoded during `qptr::lower`.
                            Some((offset, None))
                        }
                        QPtrOp::Load { offset } => {
                            Some((offset, Some(data_inst_form_def.output_types[0])))
                        }
                        QPtrOp::Store { offset } => Some((
                            offset,
                            Some(func_at_inst.at(data_inst_def.inputs[1]).type_of(&self.cx)),
                        )),

                        _ => None,
                    };
                    let first_input_var_with_offset_range =
                        first_input_qptr_with_offset_and_access_type.and_then(
                            |(offset, access_type)| {
                                if let Value::DataInstOutput { inst, output_idx } =
                                    data_inst_def.inputs[0]
                                {
                                    let var = self.vars.get_mut(&inst)?;
                                    assert_eq!(output_idx, 0);

                                    let start = u32::try_from(offset).ok()?;

                                    let end = match access_type {
                                        Some(ty) => match self.layout_cache.layout_of(ty).ok()? {
                                            TypeLayout::Concrete(layout)
                                                if layout.mem_layout.dyn_unit_stride.is_none() =>
                                            {
                                                start.checked_add(
                                                    layout.mem_layout.fixed_base.size,
                                                )?
                                            }
                                            _ => return None,
                                        },
                                        None => var.original_layout.size,
                                    };

                                    Some((var, start..end))
                                } else {
                                    None
                                }
                            },
                        );
                    if let Some((var, offset_range)) = first_input_var_with_offset_range {
                        var.add_use(offset_range, func_at_inst.position);

                        // Only visit the *other* inputs, not the `qptr` one.
                        for v in &data_inst_def.inputs[1..] {
                            self.visit_value_use(v);
                        }

                        continue;
                    }
                }
                data_inst_def.inner_visit_with(self);
            }
        } else {
            func_at_control_node.inner_visit_with(self);
        }
    }
}

#[must_use]
#[derive(Default)]
pub struct PropagateLocalVarContentsReport {
    /// Whether at least one of the function-local variables that had its contents
    /// propagated, held a `qptr`, which may now allow further simplifications.
    pub any_qptrs_propagated: bool,
}

/// Propagate (from stores to loads) contents of `func_def_body`'s local variables.
pub fn propagate_contents_of_local_vars_in_func(
    cx: Rc<Context>,
    config: &LayoutConfig,
    func_def_body: &mut FuncDefBody,
) -> PropagateLocalVarContentsReport {
    let mut report = PropagateLocalVarContentsReport::default();

    // Avoid having to support unstructured control-flow.
    if func_def_body.unstructured_cfg.is_some() {
        return report;
    }

    let (vars, propagated_loads) = {
        let mut propagator = PropagateLocalVarContents {
            cx: &cx,
            layout_cache: LayoutCache::new(cx.clone(), config),
            vars: FxIndexMap::default(),
            mutation_log: vec![],
            propagated_loads: FxIndexMap::default(),
        };
        propagator.propagate_through_control_region(func_def_body.at_mut_body());
        (propagator.vars, propagator.propagated_loads)
    };

    // FIXME(eddyb) this is not the most efficient way to compute this, but it
    // should be straight-forwardly correct to do it here.
    report.any_qptrs_propagated = vars
        .values()
        .filter_map(|var| var.as_ref().ok()?.ty)
        .any(|ty| matches!(cx[ty].kind, TypeKind::QPtr));

    let insts_to_remove = propagated_loads
        .into_iter()
        .map(|(original_inst, (_, parent_block))| (original_inst, parent_block))
        .chain(vars.into_iter().flat_map(|(original_var_inst, var_contents)| {
            var_contents.ok().into_iter().flat_map(move |var_contents| {
                [(original_var_inst, var_contents.parent_block)]
                    .into_iter()
                    .chain(var_contents.stores_with_parent_block)
            })
        }));
    for (inst, parent_block) in insts_to_remove {
        match &mut func_def_body.control_nodes[parent_block].kind {
            ControlNodeKind::Block { insts } => {
                insts.remove(inst, &mut func_def_body.data_insts);
            }
            _ => unreachable!(),
        }
    }

    report
}

struct PropagateLocalVarContents<'a> {
    cx: &'a Context,
    layout_cache: LayoutCache<'a>,

    vars: FxIndexMap<DataInst, Result<LocalVarContents, UnknowableLocalVar>>,

    // HACK(eddyb) this allows a flat representation, and handling `Select`
    // control nodes at a cost proportional only to the number of variables
    // modified in any of the child regions (not the total number of variables).
    mutation_log: Vec<LocalVarMutation>,

    /// `QPtrOp::Load` instructions with known output `Value`s, and also tracking
    /// their parent `Block` control node for later removal.
    //
    // FIXME(eddyb) it should be possible to remove the loads as they are seen.
    propagated_loads: FxIndexMap<DataInst, (Value, ControlNode)>,
}

/// Error type for when a function-local variable's `LocalVarContents` cannot be
/// tracked, either because a pointer into it escapes, or there is some other
/// issue preventing tracking (e.g. layout error, type mismatch, etc.).
struct UnknowableLocalVar;

struct LocalVarContents {
    parent_block: ControlNode,
    size: u32,

    /// Deduced type (of `value`, but may be present even if `value` is missing),
    /// which cannot change once set (instead, `UnknowableLocalVar` is produced).
    ty: Option<Type>,

    value: Option<Value>,

    /// `QPtrOp::Store` instructions to remove, if the whole variable is removed,
    /// and their parent `Block` control node.
    stores_with_parent_block: SmallVec<[(DataInst, ControlNode); 4]>,
}

struct LocalVarMutation {
    /// Index of the variable in the `vars` field of `PropagateLocalVarContents`.
    var_idx: usize,

    /// Previous value of the `value` field of `LocalVarContents`.
    prev_value: Option<Value>,
}

struct LocalVarAccess<'a> {
    /// Index of the variable in the `vars` field of `PropagateLocalVarContents`.
    var_idx: usize,

    var: &'a mut LocalVarContents,

    /// If the local variable is an `OpTypeVector`, and this access is for one
    /// of its scalar elements, this will contain that element's index.
    vector_elem_idx: Option<u8>,
}

impl PropagateLocalVarContents<'_> {
    /// Validate an access into `var_qptr`, at `offset`, with type `access_type`,
    /// returning `Some` if, and only if, the access does not conflict with any
    /// previous ones, type-wise (with accesses smaller than the whole variable
    /// being inferred as vector element accesses if a valid vector type fits).
    ///
    /// When `Some(access)` is returned, `access.var.ty` is guaranteed to be
    /// `Some`, and the type of `access.var.value` (if the latter is present).
    fn lookup_var_for_access(
        &mut self,
        var_qptr: Value,
        offset: i32,
        access_type: Type,
    ) -> Option<LocalVarAccess<'_>> {
        // HACK(eddyb) we steal the `LocalVarContents` to make the logic below
        // easier to write: if *anything* goes wrong, `Err(UnknowableLocalVar)`
        // will be left behind, and `Ok(var)` will be be restored if and only if
        // everything about this access is valid (and `Some` will be returned).
        let (var_idx, mut var) = match var_qptr {
            Value::DataInstOutput { inst, output_idx } => {
                let (var_idx, _, var) = self.vars.get_full_mut(&inst)?;
                assert_eq!(output_idx, 0);
                (var_idx, mem::replace(var, Err(UnknowableLocalVar)).ok()?)
            }
            _ => return None,
        };

        let offset = u32::try_from(offset).ok()?;

        let layout = match self.layout_cache.layout_of(access_type).ok()? {
            TypeLayout::Concrete(layout) if layout.mem_layout.dyn_unit_stride.is_none() => layout,
            _ => return None,
        };
        let access_size = layout.mem_layout.fixed_base.size;

        let (inferred_var_type, vector_elem_idx) = if offset == 0 && access_size == var.size {
            (layout.original_type, None)
        } else {
            // HACK(eddyb) we only support vector types here, as
            // they're the most common cause of partial loads/stores.
            let inferred_vector_len = var.size / access_size;
            let elem_idx = offset / access_size;

            let scalar_access_type = access_type.as_scalar(self.cx)?;
            let legal_vector = var.size % access_size == 0
                && offset % access_size == 0
                && (2..=4).contains(&inferred_vector_len);
            if !legal_vector {
                return None;
            }
            (
                self.cx.intern(vector::Type {
                    elem: scalar_access_type,
                    elem_count: u8::try_from(inferred_vector_len).ok()?.try_into().ok()?,
                }),
                Some(u8::try_from(elem_idx).unwrap()),
            )
        };

        if var.ty.is_some_and(|ty| ty != inferred_var_type) {
            return None;
        }
        var.ty = Some(inferred_var_type);

        self.vars[var_idx] = Ok(var);
        let var = self.vars[var_idx].as_mut().ok().unwrap();

        // FIXME(eddyb) should the returned value not even contain a reference
        // into `self.vars`, given that it's entirely relying on indexing?
        Some(LocalVarAccess { var_idx, var, vector_elem_idx })
    }

    /// Apply active rewrites (i.e. `propagated_loads`) to all `values`.
    fn propagate_into_values(&mut self, values: &mut [Value]) {
        for v in values {
            if let Value::DataInstOutput { inst, output_idx } = *v {
                if let Some(&(replacement_value, _)) = self.propagated_loads.get(&inst) {
                    assert_eq!(output_idx, 0);
                    *v = replacement_value;
                }
            }
        }
    }

    /// Record `values` as used - this is expected to be called only after
    /// `propagate_into_values` was applied, and not to include `qptr`s which
    /// were part of propagated loads/stores, as this'd mark them as unknowable.
    fn track_value_uses(&mut self, values: &[Value]) {
        for &v in values {
            if let Value::DataInstOutput { inst, output_idx } = v {
                if let Some(var) = self.vars.get_mut(&inst) {
                    assert_eq!(output_idx, 0);
                    *var = Err(UnknowableLocalVar);
                }
            }
        }
    }

    fn propagate_through_data_inst(
        &mut self,
        mut func_at_inst: FuncAtMut<'_, DataInst>,
        parent_block: ControlNode,
    ) {
        let cx = self.cx;

        let const_undef = |ty| {
            Value::Const(cx.intern(ConstDef {
                attrs: AttrSet::default(),
                ty,
                kind: ConstKind::Undef,
            }))
        };

        let data_inst = func_at_inst.position;

        let DataInstDef { attrs: _, form, inputs } = func_at_inst.reborrow().def();

        let DataInstFormDef { kind, output_types } = &cx[*form];

        // FIXME(eddyb) it may be helpful to fold uses after propagation,
        // (e.g. `qptr.offset` into `qptr.{load,store}`), to allow propagation
        // of variables who had their pointers stored in other variables - note
        // that multiple propagation passes would *still* be needed, because the
        // original store of a pointer to a variable will make it unknowable.
        self.propagate_into_values(inputs);

        match *kind {
            DataInstKind::QPtr(QPtrOp::FuncLocalVar(layout)) => {
                assert!(inputs.len() <= 1);
                let init_value = inputs.first().copied();

                self.vars.insert(
                    data_inst,
                    Ok(LocalVarContents {
                        parent_block,
                        size: layout.size,
                        ty: init_value.map(|v| func_at_inst.reborrow().freeze().at(v).type_of(cx)),
                        value: init_value,
                        stores_with_parent_block: Default::default(),
                    }),
                );
            }

            DataInstKind::QPtr(QPtrOp::Load { offset }) => {
                assert_eq!(inputs.len(), 1);
                let src_ptr = inputs[0];

                if let Some(access) = self.lookup_var_for_access(src_ptr, offset, output_types[0]) {
                    let var_ty = access.var.ty.unwrap();

                    // HACK(eddyb) cache the `OpUndef` constant in-place.
                    let var_value = *access.var.value.get_or_insert_with(|| const_undef(var_ty));

                    match access.vector_elem_idx {
                        None => {
                            self.propagated_loads.insert(data_inst, (var_value, parent_block));
                            // FIXME(eddyb) maybe remove the instruction here and now?
                        }

                        // Element loads from vector variables don't need to
                        // have their uses replaced, but rather become extracts.
                        Some(elem_idx) => {
                            *form = cx.intern(DataInstFormDef {
                                kind: vector::Op::from(vector::WholeOp::Extract { elem_idx })
                                    .into(),
                                output_types: output_types.clone(),
                            });
                            *inputs = [var_value].into_iter().collect();
                        }
                    }

                    return;
                }
            }

            DataInstKind::QPtr(QPtrOp::Store { offset }) => {
                assert_eq!(inputs.len(), 2);
                let dst_ptr = inputs[0];
                let stored_value = inputs[1];

                if let Some(access) = self.lookup_var_for_access(
                    dst_ptr,
                    offset,
                    func_at_inst.reborrow().freeze().at(stored_value).type_of(cx),
                ) {
                    let var_ty = access.var.ty.unwrap();

                    let new_var_value = match access.vector_elem_idx {
                        None => stored_value,

                        // Element stores into vector variables become inserts,
                        // but because we don't know yet if the store will be
                        // removed (as the variable can still escape later, or
                        // change type, etc.), the insert needs to be separate.
                        Some(elem_idx) => {
                            // HACK(eddyb) cache the `OpUndef` constant in-place
                            // (this may seem unnecessary, but the `mutation_log`
                            // will record the `OpUndef` as the `prev_value`).
                            let var_value =
                                *access.var.value.get_or_insert_with(|| const_undef(var_ty));

                            let vector_insert_data_inst =
                                func_at_inst.reborrow().data_insts.define(
                                    cx,
                                    DataInstDef {
                                        // FIXME(eddyb) preserve at least debuginfo attrs.
                                        attrs: Default::default(),
                                        form: cx.intern(DataInstFormDef {
                                            kind: vector::Op::from(vector::WholeOp::Insert {
                                                elem_idx,
                                            })
                                            .into(),
                                            output_types: [var_ty].into_iter().collect(),
                                        }),
                                        inputs: [stored_value, var_value].into_iter().collect(),
                                    }
                                    .into(),
                                );

                            // HACK(eddyb) can't really use helpers like `FuncAtMut::def`,
                            // due to the need to borrow `control_nodes` and `data_insts`
                            // at the same time - perhaps some kind of `FuncAtMut` position
                            // types for "where a list is in a parent entity" could be used
                            // to make this more ergonomic, although the potential need for
                            // an actual list entity of its own, should be considered.
                            let func = func_at_inst.reborrow().at(());
                            match &mut func.control_nodes[parent_block].kind {
                                ControlNodeKind::Block { insts } => {
                                    insts.insert_before(
                                        vector_insert_data_inst,
                                        data_inst,
                                        func.data_insts,
                                    );
                                }
                                _ => unreachable!(),
                            }

                            Value::DataInstOutput { inst: vector_insert_data_inst, output_idx: 0 }
                        }
                    };

                    let prev_value = access.var.value.replace(new_var_value);
                    access.var.stores_with_parent_block.push((data_inst, parent_block));
                    let var_idx = access.var_idx;
                    self.mutation_log.push(LocalVarMutation { var_idx, prev_value });

                    // Only visit the value input, not the destination pointer.
                    self.track_value_uses(&[stored_value]);

                    return;
                }
            }

            _ => {}
        }

        self.track_value_uses(&func_at_inst.def().inputs);
    }

    fn propagate_through_control_region(
        &mut self,
        mut func_at_region: FuncAtMut<'_, ControlRegion>,
    ) {
        let mut children = func_at_region.reborrow().at_children().into_iter();
        while let Some(func_at_control_node) = children.next() {
            self.propagate_through_control_node(func_at_control_node);
        }

        let ControlRegionDef { inputs: _, children: _, outputs } = func_at_region.def();
        self.propagate_into_values(outputs);
        self.track_value_uses(outputs);
    }

    fn propagate_through_control_node(&mut self, func_at_control_node: FuncAtMut<'_, ControlNode>) {
        let const_undef = |ty| {
            Value::Const(self.cx.intern(ConstDef {
                attrs: AttrSet::default(),
                ty,
                kind: ConstKind::Undef,
            }))
        };

        let control_node = func_at_control_node.position;

        // FIXME(eddyb) is this a good convention?
        let mut func = func_at_control_node.at(());

        match &mut func.reborrow().at(control_node).def().kind {
            &mut ControlNodeKind::Block { insts } => {
                let mut func_at_inst_iter = func.at(insts).into_iter();
                while let Some(func_at_inst) = func_at_inst_iter.next() {
                    self.propagate_through_data_inst(func_at_inst, control_node);
                }
            }
            ControlNodeKind::Select { kind: _, scrutinee, cases } => {
                self.propagate_into_values(slice::from_mut(scrutinee));
                self.track_value_uses(&[*scrutinee]);

                let num_cases = cases.len();

                // FIXME(eddyb) represent the list of child regions without having them
                // in a `Vec` (or `SmallVec`), which requires workarounds like this.
                let get_case = |func: FuncAtMut<'_, ()>, i| match &func.at(control_node).def().kind
                {
                    ControlNodeKind::Select { cases, .. } => cases[i],
                    _ => unreachable!(),
                };

                // HACK(eddyb) degenerate `Select`s do not actually need merges.
                if num_cases <= 1 {
                    if num_cases == 1 {
                        let case = get_case(func.reborrow(), 0);
                        self.propagate_through_control_region(func.at(case));
                    }
                    return;
                }

                // HACK(eddyb) this is how we can both roll back changes to
                // variables' `value`s, and know which variables were changed
                // in the first place (to merge their changes values, together).
                let mutation_log_start = self.mutation_log.len();

                let mut var_idx_to_per_case_values =
                    FxIndexMap::<usize, SmallVec<[_; 2]>>::default();
                for case_idx in 0..num_cases {
                    let case = get_case(func.reborrow(), case_idx);
                    self.propagate_through_control_region(func.reborrow().at(case));

                    // NOTE(eddyb) we traverse the mutation log forwards, as we
                    // already have a way to determine whether we've seen any
                    // mutations for each variable, and only the oldest mutation
                    // is needed to roll back the variable to its original state.
                    for mutation in self.mutation_log.drain(mutation_log_start..) {
                        let original_var_value = mutation.prev_value;
                        if let Ok(var) = &mut self.vars[mutation.var_idx] {
                            let per_case_var_values = var_idx_to_per_case_values
                                .entry(mutation.var_idx)
                                .or_insert_with(|| {
                                    let mut per_case_var_values =
                                        SmallVec::with_capacity(num_cases);

                                    // This case may be the first to mutate this
                                    // variable - thankfully we know the original
                                    // value (which will be common across all cases).
                                    per_case_var_values
                                        .extend((0..case_idx).map(|_| original_var_value));

                                    per_case_var_values
                                });

                            if per_case_var_values.len() <= case_idx {
                                let new_var_value =
                                    mem::replace(&mut var.value, original_var_value);
                                per_case_var_values.push(new_var_value);
                            }
                            assert_eq!(per_case_var_values.len() - 1, case_idx);
                        }
                    }

                    // Some variables may only have been mutated in previous cases.
                    for (&var_idx, per_case_var_values) in &mut var_idx_to_per_case_values {
                        if per_case_var_values.len() <= case_idx {
                            if let Ok(var) = &self.vars[var_idx] {
                                per_case_var_values.push(var.value);
                                assert_eq!(per_case_var_values.len() - 1, case_idx);
                            }
                        }
                    }
                }

                // Variables mutated in at least one case can now be merged,
                // by creating `Select` outputs for all of them.
                for (var_idx, per_case_var_values) in var_idx_to_per_case_values {
                    if let Ok(var) = &mut self.vars[var_idx] {
                        assert_eq!(per_case_var_values.len(), num_cases);

                        // HACK(eddyb) do not create outputs if all cases agree.
                        let v0 = per_case_var_values[0];
                        if per_case_var_values[1..].iter().all(|&v| v == v0) {
                            let prev_value = mem::replace(&mut var.value, v0);
                            self.mutation_log.push(LocalVarMutation { var_idx, prev_value });
                            continue;
                        }

                        let var_ty = var.ty.unwrap();

                        let select_output_decls =
                            &mut func.reborrow().at(control_node).def().outputs;
                        let output_idx = u32::try_from(select_output_decls.len()).unwrap();
                        select_output_decls
                            .push(ControlNodeOutputDecl { attrs: Default::default(), ty: var_ty });

                        // FIXME(eddyb) avoid random access, perhaps by handling
                        // variables per-case, instead of cases per-variable.
                        for (case_idx, per_case_var_value) in
                            (0..num_cases).zip(per_case_var_values)
                        {
                            let case = get_case(func.reborrow(), case_idx);
                            let per_case_outputs = &mut func.reborrow().at(case).def().outputs;
                            assert_eq!(per_case_outputs.len(), output_idx as usize);
                            per_case_outputs
                                .push(per_case_var_value.unwrap_or_else(|| const_undef(var_ty)));
                        }

                        let prev_value = var
                            .value
                            .replace(Value::ControlNodeOutput { control_node, output_idx });
                        self.mutation_log.push(LocalVarMutation { var_idx, prev_value });
                    }
                }
            }
            ControlNodeKind::Loop { initial_inputs, body, repeat_condition: _ } => {
                self.propagate_into_values(initial_inputs);
                self.track_value_uses(initial_inputs);

                let body = *body;

                // HACK(eddyb) as the body of the loop may execute multiple times,
                // the initial states of variables have to account for potential
                // mutations in previous iterations, which we detect with this
                // separate visitor, then plumb through the region inputs/outputs.
                let mut mutated_var_indices = {
                    let mut mutation_finder = FindMutatedLocalVars {
                        propagator: self,
                        mutated_var_indices: FxIndexSet::default(),
                    };
                    mutation_finder.visit_control_region_def(func.reborrow().freeze().at(body));
                    mutation_finder.mutated_var_indices
                };
                mutated_var_indices.retain(|&var_idx| match &mut self.vars[var_idx] {
                    Ok(var) => {
                        let var_ty = var.ty.unwrap();

                        let body_input_decls = &mut func.reborrow().at(body).def().inputs;
                        let input_idx = u32::try_from(body_input_decls.len()).unwrap();
                        body_input_decls
                            .push(ControlRegionInputDecl { attrs: Default::default(), ty: var_ty });

                        let prev_value = var
                            .value
                            .replace(Value::ControlRegionInput { region: body, input_idx });

                        let initial_inputs = match &mut func.reborrow().at(control_node).def().kind
                        {
                            ControlNodeKind::Loop { initial_inputs, .. } => initial_inputs,
                            _ => unreachable!(),
                        };
                        assert_eq!(initial_inputs.len(), input_idx as usize);
                        initial_inputs.push(prev_value.unwrap_or_else(|| const_undef(var_ty)));

                        // NOTE(eddyb) can't avoid this, because the original
                        // values of mutated variables would otherwise be lost.
                        self.mutation_log.push(LocalVarMutation { var_idx, prev_value });

                        true
                    }
                    Err(_) => false,
                });

                let body_mutation_log_start = self.mutation_log.len();
                self.propagate_through_control_region(func.reborrow().at(body));

                // Record the updated values of variables, for future iterations.
                let body_outputs = &mut func.reborrow().at(body).def().outputs;
                body_outputs.extend(mutated_var_indices.iter().map(|&var_idx| {
                    // HACK(eddyb) we require `FindMutatedLocalVars` to perfectly
                    // model all the situations in which we may reach an error
                    // (i.e. `UnknowableLocalVar`), and in which variables get
                    // mutated, because we may have *already* replaced loads in
                    // `body` to refer to values stored *in previous iterations*,
                    // so we need those values to actually be always usable.
                    self.vars[var_idx].as_ref().ok().unwrap().value.unwrap()
                }));

                // HACK(eddyb) because we already recorded all the mutations
                // based on `mutated_var_indices` alone, we can discard all the
                // redundant log entries (this also doubles as a sanity check).
                // FIXME(eddyb) this requires two passes to avoid new allocations
                // for deduplicating the set mutated variables - perhaps it may
                // be possible for `mutation_log` to always deduplicate itself
                // "since the most recent snapshot" or something?
                for mutation in &self.mutation_log[body_mutation_log_start..] {
                    assert!(mutated_var_indices.contains(&mutation.var_idx));
                }
                for mutation in self.mutation_log.drain(body_mutation_log_start..) {
                    mutated_var_indices.swap_remove(&mutation.var_idx);
                }
                assert_eq!(mutated_var_indices.len(), 0);

                let repeat_condition = match &mut func.at(control_node).def().kind {
                    ControlNodeKind::Loop { repeat_condition, .. } => repeat_condition,
                    _ => unreachable!(),
                };
                self.propagate_into_values(slice::from_mut(repeat_condition));
                self.track_value_uses(&[*repeat_condition]);
            }
        }
    }
}

/// Helper `Visitor` used when propagating local variables across a `Loop`, to
/// determine *ahead of time* which variables require `ControlRegion` inputs.
struct FindMutatedLocalVars<'a, 'b> {
    propagator: &'a mut PropagateLocalVarContents<'b>,

    /// Indices of mutated variables, in the `propagator.vars` `IndexMap`.
    // FIXME(eddyb) this could probably be a compact bitset.
    // FIXME(eddyb) a more accurate check would also consider whether values from
    // previous iterations (or before the loop) are needed, not just mutations.
    mutated_var_indices: FxIndexSet<usize>,
}

impl Visitor<'_> for FindMutatedLocalVars<'_, '_> {
    // FIXME(eddyb) this is excessive, maybe different kinds of
    // visitors should exist for module-level and func-level?
    fn visit_attr_set_use(&mut self, _: AttrSet) {}
    fn visit_type_use(&mut self, _: Type) {}
    fn visit_const_use(&mut self, _: Const) {}
    fn visit_data_inst_form_use(&mut self, _: DataInstForm) {}
    fn visit_global_var_use(&mut self, _: GlobalVar) {}
    fn visit_func_use(&mut self, _: Func) {}

    // NOTE(eddyb) uses of variables that end up here disable tracking of
    // that variable's contents (see also `UnknowableLocalVar`).
    fn visit_value_use(&mut self, &v: &Value) {
        if let Value::DataInstOutput { inst, output_idx } = v {
            if let Some(var) = self.propagator.vars.get_mut(&inst) {
                assert_eq!(output_idx, 0);
                *var = Err(UnknowableLocalVar);
            }
        }
    }

    // FIXME(eddyb) we can't use `visit_data_inst_def` because we need either
    // the resulting `DataInst`, or access to `FuncAt<Value>::type_of`.
    fn visit_control_node_def(&mut self, func_at_control_node: FuncAt<'_, ControlNode>) {
        if let ControlNodeKind::Block { insts } = func_at_control_node.def().kind {
            for func_at_inst in func_at_control_node.at(insts) {
                let data_inst_def = func_at_inst.def();
                let data_inst_form_def = &self.propagator.cx[data_inst_def.form];
                if let DataInstKind::QPtr(op) = &data_inst_form_def.kind {
                    let first_input_qptr_with_offset_and_access_type = match *op {
                        // HACK(eddyb) declaring local variables in loops is unsupported.
                        QPtrOp::FuncLocalVar(_) => {
                            self.propagator
                                .vars
                                .insert(func_at_inst.position, Err(UnknowableLocalVar));

                            None
                        }

                        // NOTE(eddyb) these need to match up exactly with
                        // `propagate_through_data_inst`, for correctness.
                        QPtrOp::Load { offset } => {
                            Some((offset, data_inst_form_def.output_types[0]))
                        }
                        QPtrOp::Store { offset } => Some((
                            offset,
                            func_at_inst.at(data_inst_def.inputs[1]).type_of(self.propagator.cx),
                        )),

                        _ => None,
                    };
                    if let Some((offset, access_type)) =
                        first_input_qptr_with_offset_and_access_type
                    {
                        if let Some(access) = self.propagator.lookup_var_for_access(
                            data_inst_def.inputs[0],
                            offset,
                            access_type,
                        ) {
                            // FIXME(eddyb) a more accurate check would also
                            // consider whether values from previous iterations
                            // (or before the loop) are needed, not just mutations.
                            let _needs_previous_value = matches!(op, QPtrOp::Load { .. })
                                || access.vector_elem_idx.is_some();

                            if let QPtrOp::Store { .. } = op {
                                self.mutated_var_indices.insert(access.var_idx);
                            }

                            // Only visit the *other* inputs, not the `qptr` one.
                            for v in &data_inst_def.inputs[1..] {
                                self.visit_value_use(v);
                            }

                            continue;
                        }
                    }
                }
                data_inst_def.inner_visit_with(self);
            }
        } else {
            func_at_control_node.inner_visit_with(self);
        }
    }
}
