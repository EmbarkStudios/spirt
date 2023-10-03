//! [`QPtr`](crate::TypeKind::QPtr) lowering (e.g. from SPIR-V).

// HACK(eddyb) layout code used to be in this module.
use super::layout::*;

use crate::func_at::FuncAtMut;
use crate::qptr::{shapes, QPtrAttr, QPtrOp};
use crate::transform::{InnerInPlaceTransform, Transformed, Transformer};
use crate::{
    spv, AddrSpace, AttrSetDef, Const, ConstDef, ConstKind, Context, ControlNode, ControlNodeKind,
    DataInst, DataInstDef, DataInstForm, DataInstFormDef, DataInstKind, DeclDef, Diag,
    EntityOrientedDenseMap, FuncDecl, GlobalVarDecl, GlobalVarInit, OrdAssertEq, Type, TypeKind,
    TypeOrConst, Value,
};
use itertools::Either;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use std::cell::Cell;
use std::collections::BTreeMap;
use std::mem;
use std::num::NonZeroU32;
use std::rc::Rc;

struct LowerError(Diag);

/// Context for lowering SPIR-V `OpTypePointer`s to `QPtr`s.
///
/// See also `passes::qptr::lower_from_spv_ptrs` (which drives this).
pub struct LowerFromSpvPtrs<'a> {
    cx: Rc<Context>,
    wk: &'static spv::spec::WellKnown,
    layout_cache: LayoutCache<'a>,

    cached_qptr_type: Cell<Option<Type>>,
}

impl<'a> LowerFromSpvPtrs<'a> {
    pub fn new(cx: Rc<Context>, layout_config: &'a LayoutConfig) -> Self {
        Self {
            cx: cx.clone(),
            wk: &spv::spec::Spec::get().well_known,
            layout_cache: LayoutCache::new(cx, layout_config),
            cached_qptr_type: Default::default(),
        }
    }

    pub fn lower_global_var(&self, global_var_decl: &mut GlobalVarDecl) {
        let wk = self.wk;

        let (_, pointee_type) = self.as_spv_ptr_type(global_var_decl.type_of_ptr_to).unwrap();
        let handle_layout_to_handle = |handle_layout: HandleLayout| match handle_layout {
            shapes::Handle::Opaque(ty) => shapes::Handle::Opaque(ty),
            shapes::Handle::Buffer(addr_space, buf) => {
                shapes::Handle::Buffer(addr_space, buf.mem_layout)
            }
        };
        let mut shape_result = self.layout_of(pointee_type).and_then(|layout| {
            Ok(match layout {
                TypeLayout::Handle(handle) => shapes::GlobalVarShape::Handles {
                    handle: handle_layout_to_handle(handle),
                    fixed_count: Some(NonZeroU32::new(1).unwrap()),
                },
                TypeLayout::HandleArray(handle, fixed_count) => shapes::GlobalVarShape::Handles {
                    handle: handle_layout_to_handle(handle),
                    fixed_count,
                },
                TypeLayout::Concrete(concrete) => {
                    if concrete.mem_layout.dyn_unit_stride.is_some() {
                        return Err(LowerError(Diag::err([
                            "global variable cannot have dynamically sized type `".into(),
                            pointee_type.into(),
                            "`".into(),
                        ])));
                    }
                    match global_var_decl.addr_space {
                        // These SPIR-V Storage Classes are defined to require
                        // exact types, either because they're `BuiltIn`s, or
                        // for "interface matching" between pipeline stages.
                        AddrSpace::SpvStorageClass(sc)
                            if [
                                wk.Input,
                                wk.Output,
                                wk.IncomingRayPayloadKHR,
                                wk.IncomingCallableDataKHR,
                                wk.HitAttributeKHR,
                                wk.RayPayloadKHR,
                                wk.CallableDataKHR,
                            ]
                            .contains(&sc) =>
                        {
                            shapes::GlobalVarShape::TypedInterface(pointee_type)
                        }

                        _ => shapes::GlobalVarShape::UntypedData(concrete.mem_layout.fixed_base),
                    }
                }
            })
        });
        if let Ok(shapes::GlobalVarShape::Handles { handle, .. }) = &mut shape_result {
            match handle {
                shapes::Handle::Opaque(_) => {
                    if global_var_decl.addr_space != AddrSpace::SpvStorageClass(wk.UniformConstant)
                    {
                        shape_result = Err(LowerError(Diag::bug([
                            "opaque Handles require UniformConstant".into(),
                        ])));
                    }
                }
                // FIXME(eddyb) not all "interface blocks" imply buffers, so this
                // may need to be ignored based on the SPIR-V storage class.
                //
                // OH GOD but the lowering of operations to the right thing.......
                // depends on whether it's a buffer or not...... outside of
                // Rust-GPU's abuse of `Generic` it should at least be possible
                // to determine it from the pointer type itself, at the lowering
                // op time, but with storage class inference.... THIS IS FUCKED
                // OTOH, Rust-GPU doesn't really use `Block` outside of buffers!
                // Long-term it should probably have different types per storage
                // class, or even represent buffers as pointers.
                shapes::Handle::Buffer(buf_addr_space, _) => {
                    // HACK(eddyb) it couldn't have been known in `layout_of`.
                    assert!(*buf_addr_space == AddrSpace::Handles);
                    *buf_addr_space = global_var_decl.addr_space;
                }
            }
            if shape_result.is_ok() {
                global_var_decl.addr_space = AddrSpace::Handles;
            }
        }

        match &mut global_var_decl.def {
            DeclDef::Imported(_) => {}
            DeclDef::Present(global_var_def_body) => match &global_var_def_body.initializer {
                None | Some(GlobalVarInit::Direct(_)) => {}

                Some(GlobalVarInit::Composite { .. }) => {
                    global_var_decl.attrs.push_diag(
                        &self.cx,
                        Diag::bug([
                            "unexpected `GlobalVarInit::Composite` (already lowered?)".into()
                        ]),
                    );
                }

                Some(GlobalVarInit::SpvAggregate { ty, leaves }) => {
                    let lowered_initializer = self
                        .layout_of(*ty)
                        .and_then(|layout| match layout {
                            // FIXME(eddyb) consider bad interactions with "interface blocks"?
                            TypeLayout::Handle(_) | TypeLayout::HandleArray(..) => {
                                Err(LowerError(Diag::bug(["handles are not aggregates".into()])))
                            }
                            TypeLayout::Concrete(layout) => Ok(layout),
                        })
                        .and_then(|aggregate_layout| {
                            let mut leaf_values = leaves.iter().copied();
                            let mut offset_to_value = BTreeMap::new();
                            aggregate_layout
                                .deeply_flatten_if(
                                    0,
                                    // Whether `candidate_layout` is an aggregate (to recurse into).
                                    &|candidate_layout| {
                                        matches!(
                                            &self.cx[candidate_layout.original_type].kind,
                                            TypeKind::SpvInst {
                                                value_lowering: spv::ValueLowering::Disaggregate(_),
                                                ..
                                            }
                                        )
                                    },
                                    &mut |leaf_offset, leaf| {
                                        let leaf_offset =
                                            u32::try_from(leaf_offset).ok().ok_or_else(|| {
                                                LayoutError(Diag::bug([format!(
                                                    "negative initializer leaf offset {leaf_offset}"
                                                )
                                                .into()]))
                                            })?;

                                        let leaf_value = leaf_values.next().ok_or_else(|| {
                                            LayoutError(Diag::bug([
                                                "fewer initializer leaves than layout".into(),
                                            ]))
                                        })?;

                                        // FIXME(eddyb) should this compare only size/shape?
                                        let expected_ty = leaf.original_type;
                                        let found_ty = self.cx[leaf_value].ty;
                                        if expected_ty != found_ty {
                                            return Err(LayoutError(Diag::bug([
                                                "initializer leaf type mismatch: expected `".into(),
                                                expected_ty.into(),
                                                "`, found `".into(),
                                                found_ty.into(),
                                                "`".into(),
                                            ])));
                                        }

                                        offset_to_value.insert(leaf_offset, leaf_value);

                                        Ok(())
                                    },
                                )
                                .map_err(|LayoutError(e)| LowerError(e))?;

                            if leaf_values.next().is_some() {
                                return Err(LowerError(Diag::bug([
                                    "more initializer leaves than layout".into(),
                                ])));
                            }

                            Ok(GlobalVarInit::Composite { offset_to_value })
                        });
                    match lowered_initializer {
                        Ok(initializer) => {
                            global_var_def_body.initializer = Some(initializer);
                        }
                        Err(LowerError(e)) => {
                            global_var_decl.attrs.push_diag(&self.cx, e);
                        }
                    }
                }
            },
        }

        // HACK(eddyb) in case anything goes wrong, we want to keep `OpTypePointer`.
        let original_type_of_ptr_to = global_var_decl.type_of_ptr_to;

        EraseSpvPtrs { lowerer: self }.in_place_transform_global_var_decl(global_var_decl);

        match shape_result {
            Ok(shape) => {
                global_var_decl.shape = Some(shape);
            }
            Err(LowerError(e)) => {
                global_var_decl.attrs.push_diag(&self.cx, e);

                // HACK(eddyb) effectively undoes `EraseSpvPtrs` for one field.
                global_var_decl.type_of_ptr_to = original_type_of_ptr_to;
            }
        }
    }

    pub fn lower_func(&self, func_decl: &mut FuncDecl) {
        // HACK(eddyb) two-step to avoid having to record the original types
        // separately - so `LowerFromSpvPtrInstsInFunc` will leave all value defs
        // (including replaced instructions!) with unchanged `OpTypePointer`
        // types, that only `EraseSpvPtrs`, later, replaces with `QPtr`.
        LowerFromSpvPtrInstsInFunc {
            lowerer: self,
            data_inst_use_counts: Default::default(),
            remove_if_dead_inst_and_parent_block: Default::default(),
            noop_offsets_to_base_ptr: Default::default(),
            aggregate_load_to_leaf_loads: Default::default(),
        }
        .in_place_transform_func_decl(func_decl);
        EraseSpvPtrs { lowerer: self }.in_place_transform_func_decl(func_decl);
    }

    /// Returns `Some` iff `ty` is a SPIR-V `OpTypePointer`.
    //
    // FIXME(eddyb) deduplicate with `qptr::lift`.
    //
    // FIXME(eddyb) consider using the storage class to determine whether a
    // `Block`-annotated type is a buffer or just interface nonsense.
    // (!!! may cause bad interactions with storage class inference `Generic` abuse)
    fn as_spv_ptr_type(&self, ty: Type) -> Option<(AddrSpace, Type)> {
        match &self.cx[ty].kind {
            TypeKind::SpvInst { spv_inst, type_and_const_inputs, .. }
                if spv_inst.opcode == self.wk.OpTypePointer =>
            {
                let sc = match spv_inst.imms[..] {
                    [spv::Imm::Short(_, sc)] => sc,
                    _ => unreachable!(),
                };
                let pointee = match type_and_const_inputs[..] {
                    [TypeOrConst::Type(elem_type)] => elem_type,
                    _ => unreachable!(),
                };
                Some((AddrSpace::SpvStorageClass(sc), pointee))
            }
            _ => None,
        }
    }

    fn const_as_u32(&self, ct: Const) -> Option<u32> {
        // HACK(eddyb) lossless roundtrip through `i32` is most conservative
        // option (only `0..=i32::MAX`, i.e. `0 <= x < 2**32, is allowed).
        u32::try_from(ct.as_scalar(&self.cx)?.int_as_i32()?).ok()
    }

    /// Get the (likely cached) `QPtr` type.
    fn qptr_type(&self) -> Type {
        if let Some(cached) = self.cached_qptr_type.get() {
            return cached;
        }
        let ty = self.cx.intern(TypeKind::QPtr);
        self.cached_qptr_type.set(Some(ty));
        ty
    }

    /// Attempt to compute a `TypeLayout` for a given (SPIR-V) `Type`.
    fn layout_of(&self, ty: Type) -> Result<TypeLayout, LowerError> {
        self.layout_cache.layout_of(ty).map_err(|LayoutError(err)| LowerError(err))
    }
}

struct EraseSpvPtrs<'a> {
    lowerer: &'a LowerFromSpvPtrs<'a>,
}

impl Transformer for EraseSpvPtrs<'_> {
    // FIXME(eddyb) this is intentionally *shallow* and will not handle pointers
    // "hidden" in composites (which should be handled in SPIR-T explicitly).
    fn transform_type_use(&mut self, ty: Type) -> Transformed<Type> {
        // FIXME(eddyb) maybe cache this remap (in `LowerFromSpvPtrs`, globally).
        if self.lowerer.as_spv_ptr_type(ty).is_some() {
            Transformed::Changed(self.lowerer.qptr_type())
        } else {
            Transformed::Unchanged
        }
    }

    // FIXME(eddyb) this is intentionally *shallow* and will not handle pointers
    // "hidden" in composites (which should be handled in SPIR-T explicitly).
    fn transform_const_use(&mut self, ct: Const) -> Transformed<Const> {
        // FIXME(eddyb) maybe cache this remap (in `LowerFromSpvPtrs`, globally).
        let ct_def = &self.lowerer.cx[ct];
        if let ConstKind::PtrToGlobalVar(_) = ct_def.kind {
            Transformed::Changed(self.lowerer.cx.intern(ConstDef {
                attrs: ct_def.attrs,
                ty: self.lowerer.qptr_type(),
                kind: ct_def.kind.clone(),
            }))
        } else {
            Transformed::Unchanged
        }
    }

    // FIXME(eddyb) because this is now interned, it might be better to
    // temporarily track the old output types in a map, and not actually
    // intern the non-`qptr`-output `qptr.*` instructions, only to replace
    // the output type with `qptr` here.
    fn transform_data_inst_form_use(
        &mut self,
        data_inst_form: DataInstForm,
    ) -> Transformed<DataInstForm> {
        // FIXME(eddyb) maybe cache this remap (in `LowerFromSpvPtrs`, globally).
        self.transform_data_inst_form_def(&self.lowerer.cx[data_inst_form])
            .map(|data_inst_form_def| self.lowerer.cx.intern(data_inst_form_def))
    }
}

struct LowerFromSpvPtrInstsInFunc<'a> {
    lowerer: &'a LowerFromSpvPtrs<'a>,

    // FIXME(eddyb) consider removing this and just do a full second traversal.
    data_inst_use_counts: EntityOrientedDenseMap<DataInst, NonZeroU32>,

    // HACK(eddyb) this acts as a "queue" for `qptr`-producing instructions,
    // which may end up dead because they're unused (either unused originally,
    // in SPIR-V, or because of offset folding).
    remove_if_dead_inst_and_parent_block: Vec<(DataInst, ControlNode)>,

    // FIXME(eddyb) this is redundant with a few other things and only here
    // because it needs to be available from `transform_value`, which doesn't
    // have access to a `FuncAt` to look up anything.
    noop_offsets_to_base_ptr: FxHashMap<DataInst, Value>,

    // HACK(eddyb) perhaps this should be a generalized "replace all uses of"?
    aggregate_load_to_leaf_loads: FxHashMap<DataInst, SmallVec<[DataInst; 8]>>,
}

/// One `QPtr`->`QPtr` step used in the lowering of `Op*AccessChain`.
///
/// The `op` should take a `QPtr` as its first input and produce a `QPtr`.
struct QPtrChainStep {
    op: QPtrOp,

    /// For `QPtrOp::HandleArrayIndex` and `QPtrOp::DynOffset`, this is the
    /// second input (after the `QPtr` which is automatically handled).
    dyn_idx: Option<Value>,
}

impl QPtrChainStep {
    fn into_data_inst_kind_and_inputs(
        self,
        in_qptr: Value,
    ) -> (DataInstKind, SmallVec<[Value; 2]>) {
        let Self { op, dyn_idx } = self;
        (op.into(), [in_qptr].into_iter().chain(dyn_idx).collect())
    }
}

impl LowerFromSpvPtrInstsInFunc<'_> {
    fn try_lower_access_chain(
        &self,
        mut layout: TypeLayout,
        indices: &[Value],
    ) -> Result<SmallVec<[QPtrChainStep; 4]>, LowerError> {
        // FIXME(eddyb) pass in the `AddrSpace` to determine this correctly.
        let is_logical_addressing = true;

        let const_idx_as_i32 = |idx| match idx {
            // FIXME(eddyb) figure out the signedness semantics here.
            Value::Const(idx) => self.lowerer.const_as_u32(idx).map(|idx_u32| idx_u32 as i32),
            _ => None,
        };

        let mut steps: SmallVec<[QPtrChainStep; 4]> = SmallVec::new();
        let mut indices = indices.iter().copied();
        while indices.len() > 0 {
            let (mut op, component_layout) = match layout {
                TypeLayout::Handle(shapes::Handle::Opaque(_)) => {
                    return Err(LowerError(Diag::bug([
                        "opaque handles have no sub-components".into()
                    ])));
                }
                TypeLayout::Handle(shapes::Handle::Buffer(_, buffer_data_layout)) => {
                    (QPtrOp::BufferData, TypeLayout::Concrete(buffer_data_layout))
                }
                TypeLayout::HandleArray(handle, _) => {
                    (QPtrOp::HandleArrayIndex, TypeLayout::Handle(handle))
                }
                TypeLayout::Concrete(concrete) => match &concrete.components {
                    Components::Scalar => {
                        return Err(LowerError(Diag::bug([
                            "scalars have no sub-components".into()
                        ])));
                    }
                    // FIXME(eddyb) handle the weird `OpTypeMatrix` layout when `RowMajor`.
                    Components::Elements { stride, elem, fixed_len } => (
                        QPtrOp::DynOffset {
                            stride: *stride,
                            // FIXME(eddyb) even without a fixed length, logical
                            // addressing still implies the index is *positive*,
                            // that should be encoded here, to help analysis.
                            index_bounds: fixed_len
                                .filter(|_| is_logical_addressing)
                                .and_then(|len| Some(0..len.get().try_into().ok()?)),
                        },
                        TypeLayout::Concrete(elem.clone()),
                    ),
                    Components::Fields { offsets, layouts } => {
                        let field_idx =
                            const_idx_as_i32(indices.next().unwrap()).ok_or_else(|| {
                                LowerError(Diag::bug(["non-constant field index".into()]))
                            })?;
                        let (field_offset, field_layout) = usize::try_from(field_idx)
                            .ok()
                            .and_then(|field_idx| {
                                Some((*offsets.get(field_idx)?, layouts.get(field_idx)?.clone()))
                            })
                            .ok_or_else(|| {
                                LowerError(Diag::bug([format!(
                                    "field {field_idx} out of bounds (expected 0..{})",
                                    offsets.len()
                                )
                                .into()]))
                            })?;
                        (
                            QPtrOp::Offset(i32::try_from(field_offset).ok().ok_or_else(|| {
                                LowerError(Diag::bug([format!(
                                    "{field_offset} not representable as a positive s32"
                                )
                                .into()]))
                            })?),
                            TypeLayout::Concrete(field_layout),
                        )
                    }
                },
            };
            layout = component_layout;

            // Automatically grab the dynamic index, whenever necessary.
            let mut dyn_idx = match op {
                QPtrOp::HandleArrayIndex | QPtrOp::DynOffset { .. } => {
                    Some(indices.next().unwrap())
                }
                _ => None,
            };

            // Constant-fold dynamic indexing, whenever possible.
            if let QPtrOp::DynOffset { stride, index_bounds } = &op {
                let const_offset = const_idx_as_i32(dyn_idx.unwrap())
                    .filter(|const_idx| {
                        index_bounds.as_ref().map_or(true, |bounds| bounds.contains(const_idx))
                    })
                    .and_then(|const_idx| i32::try_from(stride.get()).ok()?.checked_mul(const_idx));
                if let Some(const_offset) = const_offset {
                    op = QPtrOp::Offset(const_offset);
                    dyn_idx = None;
                }
            }

            // Combine consecutive immediate offsets, whenever possible.
            match (steps.last_mut().map(|last_step| &mut last_step.op), &op) {
                // Complete ignore noop offsets.
                (_, QPtrOp::Offset(0)) => {}

                (Some(QPtrOp::Offset(last_offset)), &QPtrOp::Offset(new_offset)) => {
                    *last_offset = last_offset.checked_add(new_offset).ok_or_else(|| {
                        LowerError(Diag::bug([format!(
                            "offset overflow ({last_offset}+{new_offset})"
                        )
                        .into()]))
                    })?;
                }

                _ => steps.push(QPtrChainStep { op, dyn_idx }),
            }
        }
        Ok(steps)
    }

    fn try_lower_data_inst_def(
        &mut self,
        mut func_at_data_inst: FuncAtMut<'_, DataInst>,
        parent_block: ControlNode,
    ) -> Result<Transformed<DataInstDef>, LowerError> {
        let cx = &self.lowerer.cx;
        let wk = self.lowerer.wk;

        let func_at_data_inst_frozen = func_at_data_inst.reborrow().freeze();
        let data_inst = func_at_data_inst_frozen.position;
        let data_inst_def = func_at_data_inst_frozen.def();

        // FIXME(eddyb) is this a good convention?
        let func = func_at_data_inst_frozen.at(());

        let attrs = data_inst_def.attrs;
        let DataInstFormDef { kind, output_types } = &cx[data_inst_def.form];

        let (spv_inst, spv_inst_lowering) = match kind {
            DataInstKind::SpvInst(spv_inst, lowering) => (spv_inst, lowering),
            _ => return Ok(Transformed::Unchanged),
        };

        // HACK(eddyb) this is for easy bailing/asserting.
        let disaggregated_output_or_inputs_during_lowering =
            spv_inst_lowering.disaggregated_output.is_some()
                || !spv_inst_lowering.disaggregated_inputs.is_empty();

        // Flatten `QPtrOp::Offset`s behind `ptr` into a base pointer and offset.
        let flatten_offsets = |mut ptr| {
            let mut offset = 0;
            while let Value::DataInstOutput { inst: ptr_inst, output_idx: 0 } = ptr {
                let ptr_inst_def = func.at(ptr_inst).def();
                match cx[ptr_inst_def.form].kind {
                    DataInstKind::QPtr(QPtrOp::Offset(ptr_offset)) => {
                        match ptr_offset.checked_add(offset) {
                            Some(combined_offset) => {
                                ptr = ptr_inst_def.inputs[0];
                                offset = combined_offset;
                            }
                            None => break,
                        }
                    }
                    _ => break,
                }
            }
            (ptr, offset)
        };

        // NOTE(eddyb) the ordering of some checks below is not purely aesthetic,
        // if the types are invalid there could e.g. be disaggregation where it
        // should never otherwise appear, so type checks should precede them.

        let replacement_kind_and_inputs = if spv_inst.opcode == wk.OpVariable {
            // HACK(eddyb) only needed because of potentially invalid SPIR-V.
            let output_type =
                spv_inst_lowering.disaggregated_output.unwrap_or_else(|| output_types[0]);
            let (_, var_data_type) =
                self.lowerer.as_spv_ptr_type(output_type).ok_or_else(|| {
                    LowerError(Diag::bug(["output type not an `OpTypePointer`".into()]))
                })?;

            assert!(spv_inst_lowering.disaggregated_output.is_none());

            // FIXME(eddyb) this can be happen due to the optional initializer.
            // FIXME(eddyb) lower the initializer to store(s) just after variables.
            if !spv_inst_lowering.disaggregated_inputs.is_empty() {
                return Ok(Transformed::Unchanged);
            }

            assert_eq!(output_types.len(), 1);
            assert!(data_inst_def.inputs.len() <= 1);

            match self.lowerer.layout_of(var_data_type)? {
                TypeLayout::Concrete(concrete) if concrete.mem_layout.dyn_unit_stride.is_none() => {
                    (
                        QPtrOp::FuncLocalVar(concrete.mem_layout.fixed_base).into(),
                        data_inst_def.inputs.clone(),
                    )
                }
                _ => return Ok(Transformed::Unchanged),
            }
        } else if spv_inst.opcode == wk.OpArrayLength {
            if disaggregated_output_or_inputs_during_lowering {
                return Err(LowerError(Diag::bug([format!(
                    "unexpected aggregate types in `{}`",
                    spv_inst.opcode.name()
                )
                .into()])));
            }

            let field_idx = match spv_inst.imms[..] {
                [spv::Imm::Short(_, field_idx)] => field_idx,
                _ => unreachable!(),
            };
            assert_eq!(data_inst_def.inputs.len(), 1);
            let ptr = data_inst_def.inputs[0];
            let (_, pointee_type) =
                self.lowerer.as_spv_ptr_type(func.at(ptr).type_of(cx)).ok_or_else(|| {
                    LowerError(Diag::bug(["pointer input not an `OpTypePointer`".into()]))
                })?;

            let buf_data_layout = match self.lowerer.layout_of(pointee_type)? {
                TypeLayout::Handle(shapes::Handle::Buffer(_, buf)) => buf,
                _ => return Err(LowerError(Diag::bug(["non-Buffer pointee".into()]))),
            };

            let (field_offset, field_layout) = match &buf_data_layout.components {
                Components::Fields { offsets, layouts } => usize::try_from(field_idx)
                    .ok()
                    .and_then(|field_idx| {
                        Some((*offsets.get(field_idx)?, layouts.get(field_idx)?.clone()))
                    })
                    .ok_or_else(|| {
                        LowerError(Diag::bug([format!(
                            "field {field_idx} out of bounds (expected 0..{})",
                            offsets.len()
                        )
                        .into()]))
                    })?,

                _ => {
                    return Err(LowerError(Diag::bug(
                        ["buffer data not an `OpTypeStruct`".into()],
                    )));
                }
            };
            let array_stride = match field_layout.components {
                Components::Elements { stride, fixed_len: None, .. } => stride,

                _ => {
                    return Err(LowerError(Diag::bug([format!(
                        "buffer data field #{field_idx} not an `OpTypeRuntimeArray`"
                    )
                    .into()])));
                }
            };

            // Sanity-check layout invariants (should always hold given above checks).
            assert_eq!(field_layout.mem_layout.fixed_base.size, 0);
            assert_eq!(field_layout.mem_layout.dyn_unit_stride, Some(array_stride));
            assert_eq!(buf_data_layout.mem_layout.fixed_base.size, field_offset);
            assert_eq!(buf_data_layout.mem_layout.dyn_unit_stride, Some(array_stride));

            (
                QPtrOp::BufferDynLen {
                    fixed_base_size: field_offset,
                    dyn_unit_stride: array_stride,
                }
                .into(),
                data_inst_def.inputs.clone(),
            )
        } else if [
            wk.OpAccessChain,
            wk.OpInBoundsAccessChain,
            wk.OpPtrAccessChain,
            wk.OpInBoundsPtrAccessChain,
        ]
        .contains(&spv_inst.opcode)
        {
            if disaggregated_output_or_inputs_during_lowering {
                return Err(LowerError(Diag::bug([format!(
                    "unexpected aggregate types in `{}`",
                    spv_inst.opcode.name()
                )
                .into()])));
            }

            // FIXME(eddyb) avoid erasing the "inbounds" qualifier.
            let base_ptr = data_inst_def.inputs[0];
            let (_, base_pointee_type) =
                self.lowerer.as_spv_ptr_type(func.at(base_ptr).type_of(cx)).ok_or_else(|| {
                    LowerError(Diag::bug(["pointer input not an `OpTypePointer`".into()]))
                })?;

            // HACK(eddyb) for `OpPtrAccessChain`, this pretends to be indexing
            // a `OpTypeRuntimeArray`, with the original type as the element type.
            let access_chain_base_layout =
                if [wk.OpPtrAccessChain, wk.OpInBoundsPtrAccessChain].contains(&spv_inst.opcode) {
                    self.lowerer.layout_of(cx.intern(
                        spv::Inst::from(wk.OpTypeRuntimeArray).into_canonical_type_with(
                            cx,
                            [TypeOrConst::Type(base_pointee_type)].into_iter().collect(),
                        ),
                    ))?
                } else {
                    self.lowerer.layout_of(base_pointee_type)?
                };

            let mut ptr = base_ptr;
            let mut steps =
                self.try_lower_access_chain(access_chain_base_layout, &data_inst_def.inputs[1..])?;

            // Fold a previous `Offset` into an initial offset step, where possible.
            if let Some(QPtrChainStep { op: QPtrOp::Offset(first_offset), dyn_idx: None }) =
                steps.first_mut()
            {
                let (ptr_base_ptr, ptr_offset) = flatten_offsets(ptr);
                if let Some(new_first_offset) = first_offset.checked_add(ptr_offset) {
                    ptr = ptr_base_ptr;
                    *first_offset = new_first_offset;
                }
            }

            // HACK(eddyb) noop cases should probably not use any `DataInst`s at all,
            // but that would require the ability to replace all uses of a `Value`.
            let final_step =
                steps.pop().unwrap_or(QPtrChainStep { op: QPtrOp::Offset(0), dyn_idx: None });

            for step in steps {
                let (kind, inputs) = step.into_data_inst_kind_and_inputs(ptr);
                let step_data_inst = func_at_data_inst.reborrow().data_insts.define(
                    cx,
                    DataInstDef {
                        // FIXME(eddyb) filter attributes into debuginfo and
                        // semantic, and understand the semantic ones.
                        attrs,
                        form: cx.intern(DataInstFormDef {
                            kind,
                            output_types: [self.lowerer.qptr_type()].into_iter().collect(),
                        }),
                        inputs,
                    }
                    .into(),
                );

                // HACK(eddyb) can't really use helpers like `FuncAtMut::def`,
                // due to the need to borrow `control_nodes` and `data_insts`
                // at the same time - perhaps some kind of `FuncAtMut` position
                // types for "where a list is in a parent entity" could be used
                // to make this more ergonomic, although the potential need for
                // an actual list entity of its own, should be considered.
                let func = func_at_data_inst.reborrow().at(());
                match &mut func.control_nodes[parent_block].kind {
                    ControlNodeKind::Block { insts } => {
                        insts.insert_before(step_data_inst, data_inst, func.data_insts);

                        // HACK(eddyb) this tracking is kind of ad-hoc but should
                        // easily cover everything we care about for now.
                        self.remove_if_dead_inst_and_parent_block
                            .push((step_data_inst, parent_block));
                    }
                    _ => unreachable!(),
                }

                ptr = Value::DataInstOutput { inst: step_data_inst, output_idx: 0 };
            }
            final_step.into_data_inst_kind_and_inputs(ptr)
        } else if [wk.OpLoad, wk.OpStore].contains(&spv_inst.opcode) {
            let ptr = data_inst_def.inputs[0];

            // HACK(eddyb) only needed because of potentially invalid SPIR-V.
            let type_of_ptr = match &spv_inst_lowering.disaggregated_inputs[..] {
                [(range, _), ..] if range.start == 0 => None,
                _ => Some(func.at(ptr).type_of(cx)),
            };
            let (_, pointee_type) = type_of_ptr
                .and_then(|type_of_ptr| self.lowerer.as_spv_ptr_type(type_of_ptr))
                .ok_or_else(|| {
                    LowerError(Diag::bug(["pointer input not an `OpTypePointer`".into()]))
                })?;

            #[derive(Copy, Clone)]
            enum Access {
                Load(Type),
                Store(Value),
            }

            impl Access {
                fn to_data_inst_form_and_extra_input(
                    self,
                    cx: &Context,
                    offset: i32,
                ) -> (DataInstForm, Option<Value>) {
                    match self {
                        Access::Load(ty) => (
                            cx.intern(DataInstFormDef {
                                kind: QPtrOp::Load { offset }.into(),
                                output_types: [ty].into_iter().collect(),
                            }),
                            None,
                        ),
                        Access::Store(value) => (
                            cx.intern(DataInstFormDef {
                                kind: QPtrOp::Store { offset }.into(),
                                output_types: [].into_iter().collect(),
                            }),
                            Some(value),
                        ),
                    }
                }
            }

            enum Accesses<LLA: Iterator<Item = Access>> {
                Single(Access),
                AggregateLeaves { aggregate_type: Type, leaf_accesses: LLA },
            }

            let accesses = if spv_inst.opcode == wk.OpLoad {
                assert!(spv_inst_lowering.disaggregated_inputs.is_empty());
                assert_eq!(data_inst_def.inputs.len(), 1);

                match spv_inst_lowering.disaggregated_output {
                    None => Accesses::Single(Access::Load(output_types[0])),
                    Some(aggregate_type) => Accesses::AggregateLeaves {
                        aggregate_type,
                        leaf_accesses: Either::Left(
                            output_types.iter().map(|&ty| Access::Load(ty)),
                        ),
                    },
                }
            } else {
                assert!(spv_inst_lowering.disaggregated_output.is_none());

                match spv_inst_lowering.disaggregated_inputs[..] {
                    [] => {
                        assert_eq!(data_inst_def.inputs.len(), 2);

                        Accesses::Single(Access::Store(data_inst_def.inputs[1]))
                    }
                    [(ref range, aggregate_type)] => {
                        assert_eq!(*range, 1..u32::try_from(data_inst_def.inputs.len()).unwrap());

                        Accesses::AggregateLeaves {
                            aggregate_type,
                            leaf_accesses: Either::Right(
                                data_inst_def.inputs[1..].iter().map(|&v| Access::Store(v)),
                            ),
                        }
                    }
                    _ => unreachable!(),
                }
            };

            let type_of_access = |access| match access {
                Access::Load(ty) => ty,
                Access::Store(value) => func.at(value).type_of(cx),
            };

            let original_access_type = match accesses {
                Accesses::Single(access) => type_of_access(access),
                Accesses::AggregateLeaves { aggregate_type, .. } => aggregate_type,
            };

            if pointee_type != original_access_type {
                return Err(LowerError(Diag::bug([
                    "access type different from pointee type".into()
                ])));
            }

            let (ptr, base_offset) = flatten_offsets(ptr);

            // FIXME(eddyb) support memory operands somehow.
            if !spv_inst.imms.is_empty() {
                return Ok(Transformed::Unchanged);
            }

            match accesses {
                Accesses::Single(access) => {
                    let (form, extra_input) =
                        access.to_data_inst_form_and_extra_input(cx, base_offset);
                    return Ok(Transformed::Changed(DataInstDef {
                        attrs,
                        form,
                        inputs: [ptr].into_iter().chain(extra_input).collect(),
                    }));
                }

                // If this is an aggregate `OpLoad`/`OpStore`, we should generate
                // one instruction per leaf, instead.
                Accesses::AggregateLeaves { aggregate_type: _, mut leaf_accesses } => {
                    // FIXME(eddyb) this may need to automatically generate an
                    // intermediary `QPtrOp::BufferData` when accessing buffers.
                    let mem_data_layout = match self.lowerer.layout_of(pointee_type)? {
                        TypeLayout::Concrete(mem) => mem,
                        _ => {
                            return Err(LowerError(Diag::bug([
                                "by-value aggregate type without memory layout: ".into(),
                                pointee_type.into(),
                            ])));
                        }
                    };

                    // HACK(eddyb) we have to buffer the details of the new
                    // instructions because we're iterating over the original
                    // one, and can't allocate the new `DataInst`s as we go.
                    let mut leaf_forms_and_extra_inputs = SmallVec::<[_; 4]>::new();
                    mem_data_layout
                        .deeply_flatten_if(
                            base_offset,
                            // Whether `candidate_layout` is an aggregate (to recurse into).
                            &|candidate_layout| matches!(
                                &cx[candidate_layout.original_type].kind,
                                TypeKind::SpvInst { value_lowering: spv::ValueLowering::Disaggregate(_), .. }
                            ),
                            &mut |leaf_offset, leaf| {
                                let leaf_access = leaf_accesses.next().ok_or_else(|| {
                                    LayoutError(Diag::bug([
                                        "`spv::lower` and `qptr::layout` disagree on aggregate leaves of ".into(),
                                        pointee_type.into(),
                                    ]))
                                })?;
                                let leaf_type = type_of_access(leaf_access);
                                if leaf_type != leaf.original_type {
                                    return Err(LayoutError(Diag::bug([
                                        "aggregate leaf mismatch: `".into(),
                                        leaf_type.into(),
                                        "` vs `".into(),
                                        leaf.original_type.into(),
                                        "`".into()
                                    ])));
                                }
                                leaf_forms_and_extra_inputs.push(leaf_access.to_data_inst_form_and_extra_input(cx, leaf_offset));
                                Ok(())
                            },
                        )
                        .map_err(|LayoutError(err)| LowerError(err))?;

                    if leaf_accesses.next().is_some() {
                        return Err(LowerError(Diag::bug([
                            "`spv::lower` and `qptr::layout` disagree on aggregate leaves of "
                                .into(),
                            pointee_type.into(),
                        ])));
                    }

                    // HACK(eddyb) this is for `aggregate_load_to_leaf_loads`,
                    // which gets used later, to replace uses of one of the
                    // outputs ofthe original `OpLoad`, with uses of leaf loads.
                    let mut leaf_loads = if spv_inst.opcode == wk.OpLoad {
                        Some(SmallVec::with_capacity(leaf_forms_and_extra_inputs.len()))
                    } else {
                        None
                    };

                    // This is the point of no return: we're inserting several
                    // new instructions, and marking the old one for removal.
                    for (form, extra_input) in leaf_forms_and_extra_inputs {
                        let leaf_data_inst = func_at_data_inst.reborrow().data_insts.define(
                            cx,
                            DataInstDef {
                                // FIXME(eddyb) filter attributes into debuginfo and
                                // semantic, and understand the semantic ones.
                                attrs,
                                form,
                                inputs: [ptr].into_iter().chain(extra_input).collect(),
                            }
                            .into(),
                        );

                        // HACK(eddyb) can't really use helpers like `FuncAtMut::def`,
                        // due to the need to borrow `control_nodes` and `data_insts`
                        // at the same time - perhaps some kind of `FuncAtMut` position
                        // types for "where a list is in a parent entity" could be used
                        // to make this more ergonomic, although the potential need for
                        // an actual list entity of its own, should be considered.
                        let func = func_at_data_inst.reborrow().at(());
                        match &mut func.control_nodes[parent_block].kind {
                            ControlNodeKind::Block { insts } => {
                                insts.insert_before(leaf_data_inst, data_inst, func.data_insts);
                            }
                            _ => unreachable!(),
                        }

                        if let Some(leaf_loads) = &mut leaf_loads {
                            leaf_loads.push(leaf_data_inst);
                        }
                    }
                    self.remove_if_dead_inst_and_parent_block.push((data_inst, parent_block));
                    if let Some(leaf_loads) = leaf_loads {
                        self.aggregate_load_to_leaf_loads.insert(data_inst, leaf_loads);
                    }

                    // HACK(eddyb) this is a bit counter-intuitive (and wasteful),
                    // but we expect the original instruction to be removed as
                    // effectively unused, so this will only be kept *if that fails*.
                    return Err(LowerError(Diag::bug([
                        "disaggregation of `OpLoad`/`OpStore` should've \
                         removed the original instruction, but failed to"
                            .into(),
                    ])));
                }
            }
        } else if spv_inst.opcode == wk.OpCopyMemory {
            if disaggregated_output_or_inputs_during_lowering {
                return Err(LowerError(Diag::bug([format!(
                    "unexpected aggregate types in `{}`",
                    spv_inst.opcode.name()
                )
                .into()])));
            }

            assert_eq!(data_inst_def.inputs.len(), 2);

            let dst_ptr = data_inst_def.inputs[0];
            let src_ptr = data_inst_def.inputs[1];

            let (_, dst_pointee_type) =
                self.lowerer.as_spv_ptr_type(func.at(dst_ptr).type_of(cx)).ok_or_else(|| {
                    LowerError(Diag::bug([
                        "destination pointer input not an `OpTypePointer`".into()
                    ]))
                })?;
            let (_, src_pointee_type) =
                self.lowerer.as_spv_ptr_type(func.at(src_ptr).type_of(cx)).ok_or_else(|| {
                    LowerError(Diag::bug(["source pointer input not an `OpTypePointer`".into()]))
                })?;

            if dst_pointee_type != src_pointee_type {
                return Err(LowerError(Diag::bug([
                    "copy destination pointee type different from source pointee type".into(),
                ])));
            }

            // FIXME(eddyb) this may need to automatically generate an
            // intermediary `QPtrOp::BufferData` when accessing buffers.
            let mem_data_layout = match self.lowerer.layout_of(src_pointee_type)? {
                TypeLayout::Concrete(mem) => mem,
                _ => {
                    return Err(LowerError(Diag::bug([
                        "`OpCopyMemory` of data with non-memory type: ".into(),
                        src_pointee_type.into(),
                    ])));
                }
            };

            let (dst_ptr, dst_base_offset) = flatten_offsets(dst_ptr);
            let (src_ptr, src_base_offset) = flatten_offsets(src_ptr);

            // FIXME(eddyb) support memory operands somehow.
            if !spv_inst.imms.is_empty() {
                return Ok(Transformed::Unchanged);
            }

            // HACK(eddyb) this is speculative, so we just give up if we hit
            // some situation we don't currently support - ideally, there would
            // be an *untyped* `qptr.copy`, but that is harder to support overall.
            // HACK(eddyb) this is a `try {...}`-like use of a closure.
            let try_gather_leaf_offsets_and_types = || {
                struct UnsupportedLargeArray;
                let recurse_into_layout = |layout: &MemTypeLayout| {
                    let aggregate_shape = match &cx[layout.original_type].kind {
                        TypeKind::SpvInst {
                            value_lowering: spv::ValueLowering::Disaggregate(aggregate_shape),
                            ..
                        } => aggregate_shape,
                        _ => return Ok(false),
                    };
                    match *aggregate_shape {
                        spv::AggregateShape::Struct { .. } => Ok(true),

                        // HACK(eddyb) 16 leaves allows for a 4x4 matrix, even
                        // when represented as e.g. `[f32; 16]` or `[[f32; 4]; 4]`
                        // (this comparison gets more complex when accounting
                        // for vectors, e.g. `[f32x4; 4]`, which is only 4 leaves),
                        // but ideally most types accepted here will be even
                        // smaller arrays (which could've e.g. been structs).
                        // FIXME(eddyb) larger arrays should lower to loops that
                        // copy a small number of leaves per iteration, or even
                        // some general-purpose `qptr.copy`, to avoid generating
                        // amounts of IR that scale with the array length, which
                        // (unlike struct fields) can be arbitrarily large.
                        spv::AggregateShape::Array { total_leaf_count, .. } => {
                            if total_leaf_count <= 16 {
                                Ok(true)
                            } else {
                                Err(UnsupportedLargeArray)
                            }
                        }
                    }
                };

                // HACK(eddyb) buffering the details of the instructions we'll
                // be generating, because we don't know ahead of time whether we
                // even want to expand the `OpCopyMemory`, at all.
                let mut leaf_offsets_and_types = SmallVec::<[_; 8]>::new();
                mem_data_layout
                    .deeply_flatten_if(
                        0,
                        &|candidate_layout| recurse_into_layout(candidate_layout).unwrap_or(false),
                        &mut |leaf_offset, leaf| {
                            // FIMXE(eddyb) ideally this would not be computed twice.
                            recurse_into_layout(leaf).map_err(|UnsupportedLargeArray| {
                                // HACK(eddyb) not an error, just stopping traversal.
                                LayoutError(Diag::bug([]))
                            })?;

                            // HACK(eddyb) `deeply_flatten_if` takes a base offset,
                            // but we have two, so we need our own overflow checks.
                            if dst_base_offset.checked_add(leaf_offset).is_none()
                                || src_base_offset.checked_add(leaf_offset).is_none()
                            {
                                // HACK(eddyb) not an error, just stopping traversal.
                                return Err(LayoutError(Diag::bug([])));
                            }

                            leaf_offsets_and_types.push((leaf_offset, leaf.original_type));

                            Ok(())
                        },
                    )
                    .ok()?;
                Some(leaf_offsets_and_types)
            };
            let leaf_offsets_and_types = match try_gather_leaf_offsets_and_types() {
                Some(leaf_offsets_and_types) => leaf_offsets_and_types,
                None => return Ok(Transformed::Unchanged),
            };

            // This is the point of no return: we're inserting several
            // new instructions, and marking the old one for removal.
            for (leaf_offset, leaf_type) in leaf_offsets_and_types {
                let leaf_load_data_inst = func_at_data_inst.reborrow().data_insts.define(
                    cx,
                    DataInstDef {
                        // FIXME(eddyb) filter attributes into debuginfo and
                        // semantic, and understand the semantic ones.
                        attrs,
                        form: cx.intern(DataInstFormDef {
                            kind: QPtrOp::Load {
                                offset: src_base_offset.checked_add(leaf_offset).unwrap(),
                            }
                            .into(),
                            output_types: [leaf_type].into_iter().collect(),
                        }),
                        inputs: [src_ptr].into_iter().collect(),
                    }
                    .into(),
                );
                let leaf_store_data_inst = func_at_data_inst.reborrow().data_insts.define(
                    cx,
                    DataInstDef {
                        // FIXME(eddyb) filter attributes into debuginfo and
                        // semantic, and understand the semantic ones.
                        attrs,
                        form: cx.intern(DataInstFormDef {
                            kind: QPtrOp::Store {
                                offset: dst_base_offset.checked_add(leaf_offset).unwrap(),
                            }
                            .into(),
                            output_types: [].into_iter().collect(),
                        }),
                        inputs: [
                            dst_ptr,
                            Value::DataInstOutput { inst: leaf_load_data_inst, output_idx: 0 },
                        ]
                        .into_iter()
                        .collect(),
                    }
                    .into(),
                );

                // HACK(eddyb) can't really use helpers like `FuncAtMut::def`,
                // due to the need to borrow `control_nodes` and `data_insts`
                // at the same time - perhaps some kind of `FuncAtMut` position
                // types for "where a list is in a parent entity" could be used
                // to make this more ergonomic, although the potential need for
                // an actual list entity of its own, should be considered.
                let func = func_at_data_inst.reborrow().at(());
                match &mut func.control_nodes[parent_block].kind {
                    ControlNodeKind::Block { insts } => {
                        insts.insert_before(leaf_load_data_inst, data_inst, func.data_insts);
                        insts.insert_before(leaf_store_data_inst, data_inst, func.data_insts);
                    }
                    _ => unreachable!(),
                }
            }
            self.remove_if_dead_inst_and_parent_block.push((data_inst, parent_block));

            // HACK(eddyb) this is a bit counter-intuitive (and wasteful),
            // but we expect the original instruction to be removed as
            // effectively unused, so this will only be kept *if that fails*.
            return Err(LowerError(Diag::bug(["disaggregation of `OpCopyMemory` should've \
                 removed the original instruction, but failed to"
                .into()])));
        } else if spv_inst.opcode == wk.OpBitcast {
            if disaggregated_output_or_inputs_during_lowering {
                return Err(LowerError(Diag::bug([format!(
                    "unexpected aggregate types in `{}`",
                    spv_inst.opcode.name()
                )
                .into()])));
            }

            assert_eq!(output_types.len(), 1);
            assert_eq!(data_inst_def.inputs.len(), 1);

            let input = data_inst_def.inputs[0];
            // Pointer-to-pointer casts are noops on `qptr`.
            if self.lowerer.as_spv_ptr_type(func.at(input).type_of(cx)).is_some()
                && self.lowerer.as_spv_ptr_type(output_types[0]).is_some()
            {
                // HACK(eddyb) this will end added to `noop_offsets_to_base_ptr`,
                // which should replace all uses of this bitcast with its input.
                (QPtrOp::Offset(0).into(), data_inst_def.inputs.clone())
            } else {
                return Ok(Transformed::Unchanged);
            }
        } else {
            return Ok(Transformed::Unchanged);
        };
        // FIXME(eddyb) should the `if`-`else` chain above produce `DataInstDef`s?
        let (new_kind, new_inputs) = replacement_kind_and_inputs;
        Ok(Transformed::Changed(DataInstDef {
            attrs,
            // FIXME(eddyb) because this is now interned, it might be better to
            // temporarily track the old output types in a map, and not actually
            // intern the non-`qptr`-output `qptr.*` instructions.
            form: cx.intern(DataInstFormDef { kind: new_kind, output_types: output_types.clone() }),
            inputs: new_inputs,
        }))
    }

    fn add_fallback_attrs_to_data_inst_def(
        &self,
        mut func_at_data_inst: FuncAtMut<'_, DataInst>,
        extra_error: Option<LowerError>,
    ) {
        let cx = &self.lowerer.cx;

        let func_at_data_inst_frozen = func_at_data_inst.reborrow().freeze();
        let data_inst_def = func_at_data_inst_frozen.def();
        let data_inst_form_def = &cx[data_inst_def.form];

        // FIXME(eddyb) is this a good convention?
        let func = func_at_data_inst_frozen.at(());

        let spv_inst_lowering = match &data_inst_form_def.kind {
            // Known semantics, no need to preserve SPIR-V pointer information.
            DataInstKind::Scalar(_)
            | DataInstKind::Vector(_)
            | DataInstKind::FuncCall(_)
            | DataInstKind::QPtr(_) => return,

            DataInstKind::SpvInst(_, lowering) | DataInstKind::SpvExtInst { lowering, .. } => {
                lowering
            }
        };

        let mut old_and_new_attrs = None;
        let get_old_attrs = || AttrSetDef { attrs: cx[data_inst_def.attrs].attrs.clone() };

        if let Some(LowerError(e)) = extra_error {
            old_and_new_attrs.get_or_insert_with(get_old_attrs).push_diag(e);
        }

        for (input_idx, &v) in data_inst_def.inputs.iter().enumerate() {
            if let Some((_, pointee)) = self.lowerer.as_spv_ptr_type(func.at(v).type_of(cx)) {
                old_and_new_attrs.get_or_insert_with(get_old_attrs).attrs.insert(
                    QPtrAttr::ToSpvPtrInput {
                        input_idx: input_idx.try_into().unwrap(),
                        pointee: OrdAssertEq(pointee),
                    }
                    .into(),
                );
            }
        }
        for (output_idx, &ty) in data_inst_form_def.output_types.iter().enumerate() {
            if let Some((addr_space, pointee)) = self.lowerer.as_spv_ptr_type(ty) {
                // FIXME(eddyb) make this impossible by lowering all instructions
                // that may produce aggregates with pointer leaves.
                if output_idx != 0 || spv_inst_lowering.disaggregated_output.is_some() {
                    old_and_new_attrs.get_or_insert_with(get_old_attrs).push_diag(Diag::bug([
                        format!("unsupported pointer as aggregate leaf (output #{output_idx})")
                            .into(),
                    ]));
                    continue;
                }

                old_and_new_attrs.get_or_insert_with(get_old_attrs).attrs.insert(
                    QPtrAttr::FromSpvPtrOutput {
                        addr_space: OrdAssertEq(addr_space),
                        pointee: OrdAssertEq(pointee),
                    }
                    .into(),
                );
            }
        }

        if let Some(attrs) = old_and_new_attrs {
            func_at_data_inst.def().attrs = cx.intern(attrs);
        }
    }

    // FIXME(eddyb) these are only this whacky because an `u32` is being
    // encoded as `Option<NonZeroU32>` for (dense) map entry reasons.
    fn add_value_uses(&mut self, values: &[Value]) {
        for &v in values {
            if let Value::DataInstOutput { inst, .. } = v {
                let count = self.data_inst_use_counts.entry(inst);
                *count = Some(
                    NonZeroU32::new(count.map_or(0, |c| c.get()).checked_add(1).unwrap()).unwrap(),
                );
            }
        }
    }
    fn remove_value_uses(&mut self, values: &[Value]) {
        for &v in values {
            if let Value::DataInstOutput { inst, .. } = v {
                let count = self.data_inst_use_counts.entry(inst);
                *count = NonZeroU32::new(count.unwrap().get() - 1);
            }
        }
    }

    // HACK(eddyb) this is a helper *only* for `transform_value_use` and
    // `in_place_transform_control_node_def`, and should not be used elsewhere.
    fn apply_value_replacements(&self, mut value: Value) -> Value {
        while let Value::DataInstOutput { inst, output_idx } = value {
            value = if let Some(&base_ptr) = self.noop_offsets_to_base_ptr.get(&inst) {
                assert_eq!(output_idx, 0);
                base_ptr
            } else if let Some(leaf_loads) = self.aggregate_load_to_leaf_loads.get(&inst) {
                Value::DataInstOutput { inst: leaf_loads[output_idx as usize], output_idx: 0 }
            } else {
                break;
            };
        }
        value
    }
}

impl Transformer for LowerFromSpvPtrInstsInFunc<'_> {
    // NOTE(eddyb) it's important that this only gets invoked on already lowered
    // `Value`s, so we can rely on e.g. `noop_offsets_to_base_ptr` being filled.
    fn transform_value_use(&mut self, v: &Value) -> Transformed<Value> {
        let new_v = self.apply_value_replacements(*v);

        self.add_value_uses(&[new_v]);

        if *v == new_v { Transformed::Unchanged } else { Transformed::Changed(new_v) }
    }

    // HACK(eddyb) while we want to transform `DataInstDef`s, we can't inject
    // adjacent instructions without access to the parent `ControlNodeKind::Block`,
    // and to fix this would likely require list nodes to carry some handle to
    // the list they're part of, either the whole semantic parent, or something
    // more contrived, where lists are actually allocated entities of their own,
    // perhaps something where an `EntityListDefs<DataInstDef>` contains both:
    // - an `EntityDefs<EntityListNode<DataInstDef>>` (keyed by `DataInst`)
    // - an `EntityDefs<EntityListDef<DataInst>>` (keyed by `EntityList<DataInst>`)
    fn in_place_transform_control_node_def(
        &mut self,
        mut func_at_control_node: FuncAtMut<'_, ControlNode>,
    ) {
        let control_node = func_at_control_node.position;
        if let ControlNodeKind::Block { insts } = func_at_control_node.reborrow().def().kind {
            let mut func_at_inst_iter = func_at_control_node.reborrow().at(insts).into_iter();
            while let Some(mut func_at_inst) = func_at_inst_iter.next() {
                match self.try_lower_data_inst_def(func_at_inst.reborrow(), control_node) {
                    Ok(Transformed::Changed(new_def)) => {
                        // HACK(eddyb) this tracking is kind of ad-hoc but should
                        // easily cover everything we care about for now.
                        if let DataInstKind::QPtr(op) = &self.lowerer.cx[new_def.form].kind {
                            match op {
                                QPtrOp::HandleArrayIndex
                                | QPtrOp::BufferData
                                | QPtrOp::BufferDynLen { .. }
                                | QPtrOp::Offset(_)
                                | QPtrOp::DynOffset { .. } => {
                                    self.remove_if_dead_inst_and_parent_block
                                        .push((func_at_inst.position, control_node));
                                }

                                QPtrOp::FuncLocalVar(_)
                                | QPtrOp::Load { .. }
                                | QPtrOp::Store { .. } => {}
                            }

                            if let QPtrOp::Offset(0) = op {
                                let base_ptr = self.apply_value_replacements(new_def.inputs[0]);
                                self.noop_offsets_to_base_ptr
                                    .insert(func_at_inst.position, base_ptr);
                            }
                        }

                        *func_at_inst.def() = new_def;
                    }
                    result @ (Ok(Transformed::Unchanged) | Err(_)) => {
                        self.add_fallback_attrs_to_data_inst_def(func_at_inst, result.err());
                    }
                }
            }
        }

        // NOTE(eddyb) this is done last so that `transform_value_use` only sees
        // the lowered `Value`s, not the original ones.
        func_at_control_node.reborrow().inner_in_place_transform_with(self);
    }

    fn in_place_transform_func_decl(&mut self, func_decl: &mut FuncDecl) {
        func_decl.inner_in_place_transform_with(self);

        // Apply all `remove_if_dead_inst_and_parent_block` removals, that are truly unused.
        if let DeclDef::Present(func_def_body) = &mut func_decl.def {
            let remove_if_dead_inst_and_parent_block =
                mem::take(&mut self.remove_if_dead_inst_and_parent_block);
            // NOTE(eddyb) reverse order is important, as each removal can reduce
            // use counts of an earlier definition, allowing further removal.
            for (inst, parent_block) in remove_if_dead_inst_and_parent_block.into_iter().rev() {
                if self.data_inst_use_counts.get(inst).is_none() {
                    // HACK(eddyb) can't really use helpers like `FuncAtMut::def`,
                    // due to the need to borrow `control_nodes` and `data_insts`
                    // at the same time - perhaps some kind of `FuncAtMut` position
                    // types for "where a list is in a parent entity" could be used
                    // to make this more ergonomic, although the potential need for
                    // an actual list entity of its own, should be considered.
                    match &mut func_def_body.control_nodes[parent_block].kind {
                        ControlNodeKind::Block { insts } => {
                            insts.remove(inst, &mut func_def_body.data_insts);
                        }
                        _ => unreachable!(),
                    }

                    self.remove_value_uses(&func_def_body.at(inst).def().inputs);
                }
            }
        }
    }
}
