// FIXME(eddyb) layouts are a bit tricky: this recomputes them from several passes.

use crate::qptr::shapes;
use crate::{
    scalar, spv, AddrSpace, Attr, Const, Context, Diag, FxIndexMap, Type, TypeKind, TypeOrConst,
};
use itertools::Either;
use smallvec::SmallVec;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::num::NonZeroU32;
use std::ops::Range;
use std::rc::Rc;

/// Various toggles for layout-related behavior that is not unambiguous from the
/// SPIR-V alone, or involves intermediary illegal SPIR-V (during legalization).
//
// FIXME(eddyb) use proper newtypes (and log2 for align!).
pub struct LayoutConfig {
    pub ignore_legacy_align: bool,
    pub min_aggregate_legacy_align: u32,

    /// Assumed size and alignment for `OpTypeBool`, even if unusable
    /// with externally-visible concrete memory (i.e. buffers).
    ///
    /// This is only useful for accurate handling of illegal SPIR-V relying on
    /// e.g. pointer casts, and as such defaults to `(1, 1)`, to merely ensure
    /// unique offsets and guarantee `qptr::lift` can tell fields apart.
    //
    // FIXME(eddyb) might be nice to default to an "offsets/sizes are abstract"
    // mode, which disallows reinterpretation on the basis that the precise
    // offsets/sizes may not match between types (but that's its own nightmare).
    pub abstract_bool_size_align: (u32, u32),

    /// Assumed size and alignment for logical `OpTypePointer`s, even if unusable
    /// with externally-visible concrete memory (i.e. buffers).
    ///
    /// This is only useful for accurate handling of illegal SPIR-V relying on
    /// e.g. pointer casts, and as such defaults to `(1, 1)`, to merely ensure
    /// unique offsets and guarantee `qptr::lift` can tell fields apart.
    //
    // FIXME(eddyb) might be nice to default to an "offsets/sizes are abstract"
    // mode, which disallows reinterpretation on the basis that the precise
    // offsets/sizes may not match between types (but that's its own nightmare).
    pub logical_ptr_size_align: (u32, u32),
}

impl LayoutConfig {
    pub const VULKAN_SCALAR_LAYOUT: Self = Self {
        ignore_legacy_align: true,
        min_aggregate_legacy_align: 1,

        abstract_bool_size_align: (1, 1),
        logical_ptr_size_align: (1, 1),
    };
    pub const VULKAN_STANDARD_LAYOUT: Self =
        Self { ignore_legacy_align: false, ..Self::VULKAN_SCALAR_LAYOUT };
    // FIXME(eddyb) is this even useful? (all the storage classes that have any
    // kind of alignment requirements, require explicit offsets)
    pub const VULKAN_EXTENDED_ALIGN_UBO_LAYOUT: Self =
        Self { min_aggregate_legacy_align: 16, ..Self::VULKAN_STANDARD_LAYOUT };
}

pub(super) struct LayoutError(pub(super) Diag);

#[derive(Clone)]
pub(super) enum TypeLayout {
    Handle(HandleLayout),
    HandleArray(HandleLayout, Option<NonZeroU32>),

    // FIXME(eddyb) unify terminology around "concrete"/"memory"/"untyped (data)".
    Concrete(Rc<MemTypeLayout>),
}

// NOTE(eddyb) `Handle` is parameterized over the `Buffer` layout.
pub(super) type HandleLayout = shapes::Handle<Rc<MemTypeLayout>>;

pub(super) struct MemTypeLayout {
    pub(super) original_type: Type,
    pub(super) mem_layout: shapes::MaybeDynMemLayout,
    pub(super) components: Components,
}

// FIXME(eddyb) use proper newtypes for byte sizes.
pub(super) enum Components {
    Scalar,

    /// Vector and array elements (all of them having the same `elem` layout).
    Elements {
        stride: NonZeroU32,
        elem: Rc<MemTypeLayout>,
        fixed_len: Option<NonZeroU32>,
    },

    Fields {
        // FIXME(eddyb) should these be fused? (but `u32` is smaller than `Rc`)
        offsets: SmallVec<[u32; 4]>,
        layouts: SmallVec<[Rc<MemTypeLayout>; 4]>,
    },
}

impl Components {
    /// Return all components (by index), which completely contain `offset_range`.
    ///
    /// If `offset_range` is zero-sized (`offset_range.start == offset_range.end`),
    /// this can return multiple components, with at most one ever being non-ZST.
    //
    // FIXME(eddyb) be more aggressive in pruning ZSTs so this can be simpler.
    pub(super) fn find_components_containing(
        &self,
        // FIXME(eddyb) consider renaming such offset ranges to "extent".
        offset_range: Range<u32>,
    ) -> impl Iterator<Item = usize> + '_ {
        match self {
            Components::Scalar => Either::Left(None.into_iter()),
            Components::Elements { stride, elem, fixed_len } => {
                Either::Left(
                    Some(offset_range.start / stride.get())
                        .and_then(|elem_idx| {
                            let elem_idx_vs_len = fixed_len
                                .map_or(Ordering::Less, |fixed_len| elem_idx.cmp(&fixed_len.get()));
                            let elem_size = match elem_idx_vs_len {
                                Ordering::Less => elem.mem_layout.fixed_base.size,

                                // HACK(eddyb) this allows one-past-the-end pointers.
                                Ordering::Equal => 0,

                                Ordering::Greater => return None,
                            };
                            let elem_start = elem_idx * stride.get();
                            Some((elem_idx, elem_start..elem_start.checked_add(elem_size)?))
                        })
                        .filter(|(_, elem_range)| offset_range.end <= elem_range.end)
                        .and_then(|(elem_idx, _)| usize::try_from(elem_idx).ok())
                        .into_iter(),
                )
            }
            // FIXME(eddyb) this is inefficient, we should be doing binary search
            // on offsets if they're ordered (with an optional `BTreeMap<offset, idx>`?)
            // - ideally this needs an abstraction tho, some kind of "binary-searchable array"?
            Components::Fields { offsets, layouts } => Either::Right(
                offsets
                    .iter()
                    .zip(layouts)
                    .map(|(&field_offset, field)| {
                        // HACK(eddyb) really need a maybe-open-ended range type.
                        if field.mem_layout.dyn_unit_stride.is_some() {
                            Err(field_offset..)
                        } else {
                            Ok(field_offset
                                ..field_offset
                                    .checked_add(field.mem_layout.fixed_base.size)
                                    .unwrap())
                        }
                    })
                    .enumerate()
                    .filter(move |(_, field_range)| match field_range {
                        Ok(field_range) => {
                            field_range.start <= offset_range.start
                                && offset_range.end <= field_range.end
                        }
                        Err(field_range) => field_range.start <= offset_range.start,
                    })
                    .map(|(field_idx, _)| field_idx),
            ),
        }
    }
}

/// Context for computing `TypeLayout`s from `Type`s (with caching).
pub(super) struct LayoutCache<'a> {
    cx: Rc<Context>,
    wk: &'static spv::spec::WellKnown,

    config: &'a LayoutConfig,

    cache: RefCell<FxIndexMap<Type, TypeLayout>>,
}

impl<'a> LayoutCache<'a> {
    pub(super) fn new(cx: Rc<Context>, config: &'a LayoutConfig) -> Self {
        Self { cx, wk: &spv::spec::Spec::get().well_known, config, cache: Default::default() }
    }

    fn const_as_u32(&self, ct: Const) -> Option<u32> {
        // HACK(eddyb) lossless roundtrip through `i32` is most conservative
        // option (only `0..=i32::MAX`, i.e. `0 <= x < 2**32, is allowed).
        u32::try_from(ct.as_scalar(&self.cx)?.int_as_i32()?).ok()
    }

    /// Attempt to compute a `TypeLayout` for a given (SPIR-V) `Type`.
    pub(super) fn layout_of(&self, ty: Type) -> Result<TypeLayout, LayoutError> {
        if let Some(cached) = self.cache.borrow().get(&ty).cloned() {
            return Ok(cached);
        }

        let layout = self.layout_of_uncached(ty)?;
        self.cache.borrow_mut().insert(ty, layout.clone());
        Ok(layout)
    }

    fn layout_of_uncached(&self, ty: Type) -> Result<TypeLayout, LayoutError> {
        let cx = &self.cx;
        let wk = self.wk;

        let ty_def = &cx[ty];

        let scalar_with_size_and_align = |(size, align)| {
            TypeLayout::Concrete(Rc::new(MemTypeLayout {
                original_type: ty,
                mem_layout: shapes::MaybeDynMemLayout {
                    fixed_base: shapes::MemLayout { align, legacy_align: align, size },
                    dyn_unit_stride: None,
                },
                components: Components::Scalar,
            }))
        };
        let scalar = |width: u32| {
            assert!(width.is_power_of_two());
            let size = width / 8;
            assert_eq!(size * 8, width);
            scalar_with_size_and_align((size, size))
        };
        let align_to = |size: u32, align: u32| {
            assert!(align.is_power_of_two() && align > 0);
            Ok(size.checked_add(align - 1).ok_or_else(|| {
                LayoutError(Diag::bug([
                    format!("`align_to({size}, {align})` overflowed `u32`").into()
                ]))
            })? & !(align - 1))
        };
        // HACK(eddyb) named arguments for the `array` closure.
        struct ArrayParams {
            fixed_len: Option<u32>,
            known_stride: Option<u32>,
            min_legacy_align: u32,
            legacy_align_multiplier: u32,
        }
        let array = |elem_type: Type,
                     ArrayParams {
                         fixed_len,
                         known_stride,
                         min_legacy_align,
                         legacy_align_multiplier,
                     }| {
            let fixed_len = fixed_len
                .map(|x| {
                    NonZeroU32::new(x).ok_or_else(|| {
                        LayoutError(Diag::err(["SPIR-V disallows arrays of `0` length".into()]))
                    })
                })
                .transpose()?;
            match self.layout_of(elem_type)? {
                TypeLayout::Handle(handle) => Ok(TypeLayout::HandleArray(handle, fixed_len)),
                TypeLayout::HandleArray(..) => Err(LayoutError(Diag::err([
                    "handle array `".into(),
                    elem_type.into(),
                    "` cannot be further wrapped in an array".into(),
                ]))),
                TypeLayout::Concrete(elem) => {
                    if elem.mem_layout.dyn_unit_stride.is_some() {
                        return Err(LayoutError(Diag::err([
                            "dynamically sized type `".into(),
                            elem_type.into(),
                            "` cannot be further wrapped in an array".into(),
                        ])));
                    }
                    let stride = match known_stride {
                        Some(stride) => stride,
                        None => {
                            let shapes::MemLayout { align, legacy_align, size } =
                                elem.mem_layout.fixed_base;
                            let (stride, legacy_stride) =
                                (align_to(size, align)?, align_to(size, legacy_align)?);

                            // FIXME(eddyb) this whole ambiguity mechanism is strange and
                            // maybe unnecessary? (all the storage classes that have any
                            // kind of alignment requirements, require explicit offsets)
                            if !self.config.ignore_legacy_align && stride != legacy_stride {
                                return Err(LayoutError(Diag::bug([format!(
                                    "ambiguous stride: \
                                    {stride} (scalar) vs {legacy_stride} (legacy), \
                                     due to alignment differences \
                                     ({align} scalar vs {legacy_align} legacy)",
                                )
                                .into()])));
                            }
                            stride
                        }
                    };
                    let stride = NonZeroU32::new(stride).ok_or_else(|| {
                        LayoutError(Diag::err(["SPIR-V disallows arrays of `0` stride".into()]))
                    })?;
                    Ok(TypeLayout::Concrete(Rc::new(MemTypeLayout {
                        original_type: ty,
                        mem_layout: shapes::MaybeDynMemLayout {
                            fixed_base: shapes::MemLayout {
                                align: elem.mem_layout.fixed_base.align,
                                legacy_align: elem
                                    .mem_layout
                                    .fixed_base
                                    .legacy_align
                                    .checked_mul(legacy_align_multiplier)
                                    .unwrap()
                                    .max(min_legacy_align),
                                size: fixed_len
                                    .map(|len| {
                                        stride.checked_mul(len).ok_or_else(|| {
                                            LayoutError(Diag::bug([format!(
                                                "`{stride} * {len}` overflowed `u32`"
                                            )
                                            .into()]))
                                        })
                                    })
                                    .transpose()?
                                    .map_or(0, |size| size.get()),
                            },
                            dyn_unit_stride: if fixed_len.is_none() { Some(stride) } else { None },
                        },
                        components: Components::Elements { stride, elem, fixed_len },
                    })))
                }
            }
        };

        // FIXME(eddyb) !!! what if... types had a min/max size and then...
        // that would allow surrounding offsets to limit their size... but... ugh...
        // ugh this doesn't make any sense. maybe if the front-end specifies
        // offsets with "abstract types", it must configure `qptr::layout`?

        let (spv_inst, type_and_const_inputs) = match &ty_def.kind {
            TypeKind::Scalar(scalar::Type::Bool) => {
                // FIXME(eddyb) make this properly abstract instead of only configurable.
                return Ok(scalar_with_size_and_align(self.config.abstract_bool_size_align));
            }
            TypeKind::Scalar(ty) => return Ok(scalar(ty.bit_width())),

            TypeKind::Vector(ty) => {
                let len = u32::from(ty.elem_count.get());
                return array(
                    cx.intern(ty.elem),
                    ArrayParams {
                        fixed_len: Some(len),
                        known_stride: None,

                        // NOTE(eddyb) this is specifically Vulkan "base alignment".
                        min_legacy_align: 1,
                        legacy_align_multiplier: if len <= 2 { 2 } else { 4 },
                    },
                );
            }

            // FIXME(eddyb) treat `QPtr`s as scalars.
            TypeKind::QPtr => {
                return Err(LayoutError(Diag::bug(
                    ["`layout_of(qptr)` (already lowered?)".into()],
                )));
            }
            TypeKind::SpvInst { spv_inst, type_and_const_inputs } => {
                (spv_inst, type_and_const_inputs)
            }
            TypeKind::SpvStringLiteralForExtInst => {
                return Err(LayoutError(Diag::bug([
                    "`layout_of(type_of(OpString<\"...\">))`".into()
                ])));
            }
        };
        let short_imm_at = |i| match spv_inst.imms[i] {
            spv::Imm::Short(_, x) => x,
            _ => unreachable!(),
        };
        Ok(if spv_inst.opcode == wk.OpTypePointer {
            // FIXME(eddyb) make this properly abstract instead of only configurable.
            // FIXME(eddyb) categorize `OpTypePointer` by storage class and split on
            // logical vs physical here.
            scalar_with_size_and_align(self.config.logical_ptr_size_align)
        } else if spv_inst.opcode == wk.OpTypeMatrix {
            // NOTE(eddyb) `RowMajor` is disallowed on `OpTypeStruct` members below.
            array(
                match type_and_const_inputs[..] {
                    [TypeOrConst::Type(elem_type)] => elem_type,
                    _ => unreachable!(),
                },
                ArrayParams {
                    fixed_len: Some(short_imm_at(0)),
                    known_stride: None,
                    min_legacy_align: self.config.min_aggregate_legacy_align,
                    legacy_align_multiplier: 1,
                },
            )?
        } else if [wk.OpTypeArray, wk.OpTypeRuntimeArray].contains(&spv_inst.opcode) {
            let len = type_and_const_inputs
                .get(1)
                .map(|&len| {
                    let len = match len {
                        TypeOrConst::Const(len) => len,
                        TypeOrConst::Type(_) => unreachable!(),
                    };
                    self.const_as_u32(len).ok_or_else(|| {
                        LayoutError(Diag::bug(
                            ["specialization constants not supported yet".into()],
                        ))
                    })
                })
                .transpose()?;
            let mut stride_decoration = None;
            for attr in &cx[ty_def.attrs].attrs {
                match attr {
                    Attr::SpvAnnotation(attr_spv_inst)
                        if attr_spv_inst.opcode == wk.OpDecorate
                            && attr_spv_inst.imms[0]
                                == spv::Imm::Short(wk.Decoration, wk.ArrayStride) =>
                    {
                        stride_decoration = Some(match attr_spv_inst.imms[1] {
                            spv::Imm::Short(_, x) => x,
                            _ => unreachable!(),
                        });
                        break;
                    }
                    _ => {}
                }
            }
            array(
                match type_and_const_inputs[0] {
                    TypeOrConst::Type(elem_type) => elem_type,
                    TypeOrConst::Const(_) => unreachable!(),
                },
                ArrayParams {
                    fixed_len: len,
                    known_stride: stride_decoration,
                    min_legacy_align: self.config.min_aggregate_legacy_align,
                    legacy_align_multiplier: 1,
                },
            )?
        } else if spv_inst.opcode == wk.OpTypeStruct {
            let field_layouts: SmallVec<[_; 4]> = type_and_const_inputs
                .iter()
                .map(|&ty_or_ct| match ty_or_ct {
                    TypeOrConst::Type(field_type) => field_type,
                    TypeOrConst::Const(_) => unreachable!(),
                })
                .map(|field_type| match self.layout_of(field_type)? {
                    TypeLayout::Handle(_) | TypeLayout::HandleArray(..) => {
                        Err(LayoutError(Diag::bug([
                            "handles cannot be placed in a struct field".into()
                        ])))
                    }
                    TypeLayout::Concrete(field_layout) => Ok(field_layout),
                })
                .collect::<Result<_, _>>()?;

            let mut field_offsets: SmallVec<[_; 4]> = SmallVec::with_capacity(field_layouts.len());
            for attr in &cx[ty_def.attrs].attrs {
                match attr {
                    Attr::SpvAnnotation(attr_spv_inst)
                        if attr_spv_inst.opcode == wk.OpMemberDecorate
                            && attr_spv_inst.imms[1]
                                == spv::Imm::Short(wk.Decoration, wk.RowMajor) =>
                    {
                        return Err(LayoutError(Diag::bug([
                            "`RowMajor` matrix types unsupported".into(),
                        ])));
                    }
                    Attr::SpvAnnotation(attr_spv_inst)
                        if attr_spv_inst.opcode == wk.OpMemberDecorate
                            && attr_spv_inst.imms[1]
                                == spv::Imm::Short(wk.Decoration, wk.Offset) =>
                    {
                        let (field_idx, field_offset) = match attr_spv_inst.imms[..] {
                            [spv::Imm::Short(_, idx), _, spv::Imm::Short(_, offset)] => {
                                (idx, offset)
                            }
                            _ => unreachable!(),
                        };
                        let field_idx = usize::try_from(field_idx).unwrap();
                        match field_idx.cmp(&field_offsets.len()) {
                            Ordering::Less => {
                                return Err(LayoutError(Diag::bug([
                                    "a struct field cannot have more than one explicit offset"
                                        .into(),
                                ])));
                            }
                            Ordering::Greater => {
                                return Err(LayoutError(Diag::bug([
                                    "structs with explicit offsets must provide them for all fields"
                                        .into(),
                                ])));
                            }
                            Ordering::Equal => {
                                field_offsets.push(field_offset);
                            }
                        }
                    }
                    _ => {}
                }
            }
            let mut mem_layout = shapes::MaybeDynMemLayout {
                fixed_base: shapes::MemLayout {
                    align: 1,
                    legacy_align: self.config.min_aggregate_legacy_align,
                    size: 0,
                },
                dyn_unit_stride: None,
            };
            if !field_offsets.is_empty() {
                if field_offsets.len() != field_layouts.len() {
                    return Err(LayoutError(Diag::bug([
                        "structs with explicit offsets must provide them for all fields".into(),
                    ])));
                }

                // HACK(eddyb) this treats the struct more like an union, but
                // it shold nevertheless work (the other approach would be to
                // search for the "last field (in offset order)", and/or iterate
                // all fields in offset order, to validate the lack of overlap),
                // and also "last field (in offset order)" approaches would still
                // have to look at all the fields in order to compute alignment.
                for (&field_offset, field_layout) in field_offsets.iter().zip(&field_layouts) {
                    let field = field_layout.mem_layout;

                    mem_layout.fixed_base.align =
                        mem_layout.fixed_base.align.max(field.fixed_base.align);
                    mem_layout.fixed_base.legacy_align =
                        mem_layout.fixed_base.legacy_align.max(field.fixed_base.legacy_align);
                    mem_layout.fixed_base.size = mem_layout.fixed_base.size.max(
                        field_offset.checked_add(field.fixed_base.size).ok_or_else(|| {
                            LayoutError(Diag::bug([format!(
                                "`{} + {}` overflowed `u32`",
                                field_offset, field.fixed_base.size
                            )
                            .into()]))
                        })?,
                    );

                    // FIXME(eddyb) validate sized-vs-unsized fields, too.
                    if let Some(field_dyn_unit_stride) = field.dyn_unit_stride {
                        if mem_layout.dyn_unit_stride.is_some() {
                            return Err(LayoutError(Diag::bug([
                                "only one field of a struct can have a dynamically sized type"
                                    .into(),
                            ])));
                        }
                        mem_layout.dyn_unit_stride = Some(field_dyn_unit_stride);
                    }
                }
            } else {
                for field_layout in &field_layouts {
                    if mem_layout.dyn_unit_stride.is_some() {
                        return Err(LayoutError(Diag::bug([
                            "only the last field of a struct can have a dynamically sized type"
                                .into(),
                        ])));
                    }

                    let field = field_layout.mem_layout;

                    let (offset, legacy_offset) = (
                        align_to(mem_layout.fixed_base.size, field.fixed_base.align)?,
                        align_to(mem_layout.fixed_base.size, field.fixed_base.legacy_align)?,
                    );
                    // FIXME(eddyb) this whole ambiguity mechanism is strange and
                    // maybe unnecessary? (all the storage classes that have any
                    // kind of alignment requirements, require explicit offsets)
                    if !self.config.ignore_legacy_align && offset != legacy_offset {
                        return Err(LayoutError(Diag::bug([format!(
                            "ambiguous offset: {offset} (scalar) vs {legacy_offset} (legacy), \
                             due to alignment differences ({} scalar vs {} legacy)",
                            field.fixed_base.align, field.fixed_base.legacy_align
                        )
                        .into()])));
                    }

                    field_offsets.push(offset);

                    mem_layout.fixed_base.align =
                        mem_layout.fixed_base.align.max(field.fixed_base.align);
                    mem_layout.fixed_base.legacy_align =
                        mem_layout.fixed_base.legacy_align.max(field.fixed_base.legacy_align);
                    mem_layout.fixed_base.size =
                        offset.checked_add(field.fixed_base.size).ok_or_else(|| {
                            LayoutError(Diag::bug([format!(
                                "`{} + {}` overflowed `u32`",
                                offset, field.fixed_base.size
                            )
                            .into()]))
                        })?;

                    assert!(mem_layout.dyn_unit_stride.is_none());
                    mem_layout.dyn_unit_stride = field.dyn_unit_stride;
                }
            }
            // FIXME(eddyb) how should the fixed base be aligned in unsized structs?
            if mem_layout.dyn_unit_stride.is_none() {
                mem_layout.fixed_base.size =
                    align_to(mem_layout.fixed_base.size, mem_layout.fixed_base.align)?;
            }

            let concrete = Rc::new(MemTypeLayout {
                original_type: ty,
                mem_layout,
                components: Components::Fields { offsets: field_offsets, layouts: field_layouts },
            });
            let mut is_interface_block = false;
            for attr in &cx[ty_def.attrs].attrs {
                match attr {
                    Attr::SpvAnnotation(attr_spv_inst)
                        if attr_spv_inst.opcode == wk.OpDecorate
                            && attr_spv_inst.imms[0]
                                == spv::Imm::Short(wk.Decoration, wk.Block) =>
                    {
                        is_interface_block = true;
                        break;
                    }
                    _ => {}
                }
            }
            // FIXME(eddyb) not all "interface blocks" imply buffers, so this may
            // need to be ignored based on the SPIR-V storage class of a `GlobalVar`.
            //
            // FIXME(eddyb) but the lowering of operations on pointers depend on
            // whether the pointer is to a buffer or a data type - without the
            // way Rust-GPU uses `Generic`, it should at least be possible to
            // determine from the pointer type itself, at the op lowering time,
            // but with storage class inference this isn't knowable...
            //
            // OTOH, Rust-GPU doesn't really use `Block` outside of buffers, so
            // it's plausible there could be `qptr` customization options which
            // Rust-GPU uses to unambiguously communicate its (mis)use of SPIR-V
            // (long-term it should probably have different Rust types per
            // storage class, or even represent buffers as Rust pointers?)
            if is_interface_block {
                // HACK(eddyb) we need an `AddrSpace` but it's not known yet.
                TypeLayout::Handle(shapes::Handle::Buffer(AddrSpace::Handles, concrete))
            } else {
                TypeLayout::Concrete(concrete)
            }
        } else if [
            wk.OpTypeImage,
            wk.OpTypeSampler,
            wk.OpTypeSampledImage,
            wk.OpTypeAccelerationStructureKHR,
        ]
        .contains(&spv_inst.opcode)
        {
            TypeLayout::Handle(shapes::Handle::Opaque(ty))
        } else {
            return Err(LayoutError(Diag::bug([format!(
                "unknown/unsupported SPIR-V type `{}`",
                spv_inst.opcode.name()
            )
            .into()])));
        })
    }
}
