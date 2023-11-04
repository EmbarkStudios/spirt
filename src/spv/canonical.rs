//! Bidirectional (SPIR-V <-> SPIR-T) "canonical mappings".
//!
//! Both directions are defined close together as much as possible, to:
//! - limit code duplication, making it easy to add more mappings
//! - limit how much they could even go out of sync over time
//! - prevent naming e.g. SPIR-V opcodes, outside canonicalization
//
// FIXME(eddyb) should interning attempts check/apply these canonicalizations?

use crate::spv::{self, spec};
use crate::{scalar, vector, Const, ConstKind, Context, DataInstKind, Type, TypeKind, TypeOrConst};
use lazy_static::lazy_static;
use smallvec::SmallVec;

// FIXME(eddyb) these ones could maybe make use of build script generation.
macro_rules! def_mappable_ops {
    (
        type { $($ty_op:ident),+ $(,)? }
        const { $($ct_op:ident),+ $(,)? }
        $($enum_path:path { $($variant_op:ident <=> $variant:ident$(($($variant_args:tt)*))?),+ $(,)? })*
    ) => {
        #[allow(non_snake_case)]
        struct MappableOps {
            $($ty_op: spec::Opcode,)+
            $($ct_op: spec::Opcode,)+
            $($($variant_op: spec::Opcode,)+)*
        }
        impl MappableOps {
            #[inline(always)]
            #[must_use]
            pub fn get() -> &'static MappableOps {
                lazy_static! {
                    static ref MAPPABLE_OPS: MappableOps = {
                        let spv_spec = spec::Spec::get();
                        MappableOps {
                            $($ty_op: spv_spec.instructions.lookup(stringify!($ty_op)).unwrap(),)+
                            $($ct_op: spv_spec.instructions.lookup(stringify!($ct_op)).unwrap(),)+
                            $($($variant_op: spv_spec.instructions.lookup(stringify!($variant_op)).unwrap(),)+)*
                        }
                    };
                }
                &MAPPABLE_OPS
            }
        }
        // NOTE(eddyb) these should stay private, hence not implementing `TryFrom`.
        $(impl $enum_path {
            fn try_from_opcode(opcode: spec::Opcode) -> Option<Self> {
                let mo = MappableOps::get();
                $(if opcode == mo.$variant_op {
                    return Some(Self::$variant$(($($variant_args)*))?);
                })+
                None
            }
            fn to_opcode(self) -> spec::Opcode {
                let mo = MappableOps::get();
                match self {
                    $(Self::$variant$(($($variant_args)*))? => mo.$variant_op,)+
                }
            }
        })*
    };
}
def_mappable_ops! {
    // FIXME(eddyb) these categories don't actually do anything right now
    type {
        OpTypeBool,
        OpTypeInt,
        OpTypeFloat,
        OpTypeVector,
    }
    const {
        OpUndef,
        OpConstantFalse,
        OpConstantTrue,
        OpConstant,
    }
    scalar::BoolUnOp {
        OpLogicalNot <=> Not,
    }
    scalar::BoolBinOp {
        OpLogicalEqual <=> Eq,
        OpLogicalNotEqual <=> Ne,
        OpLogicalOr <=> Or,
        OpLogicalAnd <=> And,
    }
    scalar::IntUnOp {
        OpSNegate <=> Neg,
        OpNot <=> Not,
        OpBitCount <=> CountOnes,

        OpUConvert <=> TruncOrZeroExtend,
        OpSConvert <=> TruncOrSignExtend,
    }
    scalar::IntBinOp {
        // I×I→I
        OpIAdd <=> Add,
        OpISub <=> Sub,
        OpIMul <=> Mul,
        OpUDiv <=> DivU,
        OpSDiv <=> DivS,
        OpUMod <=> ModU,
        OpSRem <=> RemS,
        OpSMod <=> ModS,
        OpShiftRightLogical <=> ShrU,
        OpShiftRightArithmetic <=> ShrS,
        OpShiftLeftLogical <=> Shl,
        OpBitwiseOr <=> Or,
        OpBitwiseXor <=> Xor,
        OpBitwiseAnd <=> And,

        // I×I→I×I
        OpIAddCarry <=> CarryingAdd,
        OpISubBorrow <=> BorrowingSub,
        OpUMulExtended <=> WideningMulU,
        OpSMulExtended <=> WideningMulS,

        // I×I→B
        OpIEqual <=> Eq,
        OpINotEqual <=> Ne,
        OpUGreaterThan <=> GtU,
        OpSGreaterThan <=> GtS,
        OpUGreaterThanEqual <=> GeU,
        OpSGreaterThanEqual <=> GeS,
        OpULessThan <=> LtU,
        OpSLessThan <=> LtS,
        OpULessThanEqual <=> LeU,
        OpSLessThanEqual <=> LeS,
    }
    scalar::FloatUnOp {
        // F→F
        OpFNegate <=> Neg,

        // F→B
        OpIsNan <=> IsNan,
        OpIsInf <=> IsInf,

        OpConvertUToF <=> FromUInt,
        OpConvertSToF <=> FromSInt,
        OpConvertFToU <=> ToUInt,
        OpConvertFToS <=> ToSInt,
        OpFConvert <=> Convert,
        OpQuantizeToF16 <=> QuantizeAsF16,
    }
    scalar::FloatBinOp {
        // F×F→F
        OpFAdd <=> Add,
        OpFSub <=> Sub,
        OpFMul <=> Mul,
        OpFDiv <=> Div,
        OpFRem <=> Rem,
        OpFMod <=> Mod,

        // F×F→B
        OpFOrdEqual <=> Cmp(scalar::FloatCmp::Eq),
        OpFOrdNotEqual <=> Cmp(scalar::FloatCmp::Ne),
        OpFOrdLessThan <=> Cmp(scalar::FloatCmp::Lt),
        OpFOrdGreaterThan <=> Cmp(scalar::FloatCmp::Gt),
        OpFOrdLessThanEqual <=> Cmp(scalar::FloatCmp::Le),
        OpFOrdGreaterThanEqual <=> Cmp(scalar::FloatCmp::Ge),
        OpFUnordEqual <=> CmpOrUnord(scalar::FloatCmp::Eq),
        OpFUnordNotEqual <=> CmpOrUnord(scalar::FloatCmp::Ne),
        OpFUnordLessThan <=> CmpOrUnord(scalar::FloatCmp::Lt),
        OpFUnordGreaterThan <=> CmpOrUnord(scalar::FloatCmp::Gt),
        OpFUnordLessThanEqual <=> CmpOrUnord(scalar::FloatCmp::Le),
        OpFUnordGreaterThanEqual <=> CmpOrUnord(scalar::FloatCmp::Ge),
    }
}

impl scalar::Const {
    // HACK(eddyb) this is not private so `spv::lower` can use it for `OpSwitch`.
    pub(super) fn try_decode_from_spv_imms(
        ty: scalar::Type,
        imms: &[spv::Imm],
    ) -> Option<scalar::Const> {
        // FIXME(eddyb) don't hardcode the 128-bit limitation,
        // but query `scalar::Const` somehow instead.
        if ty.bit_width() > 128 {
            return None;
        }
        let imm_words = usize::try_from(ty.bit_width().div_ceil(32)).unwrap();
        if imms.len() != imm_words {
            return None;
        }
        let mut bits = 0;
        for (i, &imm) in imms.iter().enumerate() {
            let w = match imm {
                spv::Imm::Short(_, w) if imm_words == 1 => w,
                spv::Imm::LongStart(_, w) if i == 0 && imm_words > 1 => w,
                spv::Imm::LongCont(_, w) if i > 0 => w,
                _ => return None,
            };
            bits |= (w as u128) << (i * 32);
        }

        // HACK(eddyb) signed integers are encoded sign-extended into immediates.
        if let scalar::Type::SInt(_) = ty {
            let imm_width = imm_words * 32;
            scalar::Const::int_try_from_i128(
                ty,
                (bits as i128) << (128 - imm_width) >> (128 - imm_width),
            )
        } else {
            scalar::Const::try_from_bits(ty, bits)
        }
    }

    // HACK(eddyb) this is not private so `spv::lift` can use it for `OpSwitch`.
    pub(super) fn encode_as_spv_imms(&self) -> impl Iterator<Item = spv::Imm> {
        let wk = &spec::Spec::get().well_known;

        let ty = self.ty();
        let imm_words = ty.bit_width().div_ceil(32);

        let bits = self.bits();

        // HACK(eddyb) signed integers are encoded sign-extended into immediates.
        let bits = if let scalar::Type::SInt(_) = ty {
            let imm_width = imm_words * 32;
            (self.int_as_i128().unwrap() as u128) & (!0 >> (128 - imm_width))
        } else {
            bits
        };

        (0..imm_words).map(move |i| {
            let k = wk.LiteralContextDependentNumber;
            let w = (bits >> (i * 32)) as u32;
            if imm_words == 1 {
                spv::Imm::Short(k, w)
            } else if i == 0 {
                spv::Imm::LongStart(k, w)
            } else {
                spv::Imm::LongCont(k, w)
            }
        })
    }
}

// FIXME(eddyb) decide on a visibility scope - `pub(super)` avoids some mistakes
// (using these methods outside of `spv::{lower,lift}`), but may be too restrictive.
impl spv::Inst {
    // HACK(eddyb) exported only for `spv::read`/`LiteralContextDependentNumber`.
    pub(super) fn int_or_float_type_bit_width(&self) -> Option<u32> {
        let mo = MappableOps::get();

        match self.imms[..] {
            [spv::Imm::Short(_, bit_width), _] if self.opcode == mo.OpTypeInt => Some(bit_width),
            [spv::Imm::Short(_, bit_width)] if self.opcode == mo.OpTypeFloat => Some(bit_width),
            _ => None,
        }
    }

    // FIXME(eddyb) automate bidirectional mappings more (although the need
    // for conditional, i.e. "partial", mappings, adds a lot of complexity).
    pub(super) fn as_canonical_type(
        &self,
        cx: &Context,
        type_and_const_inputs: &[TypeOrConst],
    ) -> Option<TypeKind> {
        let Self { opcode, imms } = self;
        let (&opcode, imms) = (opcode, &imms[..]);

        let mo = MappableOps::get();

        let int_width = || scalar::IntWidth::try_from_bits(self.int_or_float_type_bit_width()?);
        match (imms, type_and_const_inputs) {
            ([], []) if opcode == mo.OpTypeBool => Some(scalar::Type::Bool.into()),
            (&[_, spv::Imm::Short(_, 0)], []) if opcode == mo.OpTypeInt => {
                Some(scalar::Type::UInt(int_width()?).into())
            }
            (&[_, spv::Imm::Short(_, 1)], []) if opcode == mo.OpTypeInt => {
                Some(scalar::Type::SInt(int_width()?).into())
            }
            ([_], []) if opcode == mo.OpTypeFloat => Some(
                scalar::Type::Float(scalar::FloatWidth::try_from_bits(
                    self.int_or_float_type_bit_width()?,
                )?)
                .into(),
            ),
            (&[spv::Imm::Short(_, elem_count)], &[TypeOrConst::Type(elem_type)])
                if opcode == mo.OpTypeVector =>
            {
                Some(
                    vector::Type {
                        elem: elem_type.as_scalar(cx)?,
                        elem_count: u8::try_from(elem_count).ok()?.try_into().ok()?,
                    }
                    .into(),
                )
            }
            _ => None,
        }
    }

    pub(super) fn from_canonical_type(
        cx: &Context,
        type_kind: &TypeKind,
    ) -> Option<(Self, SmallVec<[TypeOrConst; 2]>)> {
        let wk = &spec::Spec::get().well_known;
        let mo = MappableOps::get();

        match type_kind {
            &TypeKind::Scalar(ty) => Some((
                match ty {
                    scalar::Type::Bool => mo.OpTypeBool.into(),
                    scalar::Type::SInt(w) | scalar::Type::UInt(w) => spv::Inst {
                        opcode: mo.OpTypeInt,
                        imms: [
                            spv::Imm::Short(wk.LiteralInteger, w.bits()),
                            spv::Imm::Short(
                                wk.LiteralInteger,
                                matches!(ty, scalar::Type::SInt(_)) as u32,
                            ),
                        ]
                        .into_iter()
                        .collect(),
                    },
                    scalar::Type::Float(w) => spv::Inst {
                        opcode: mo.OpTypeFloat,
                        imms: [spv::Imm::Short(wk.LiteralInteger, w.bits())].into_iter().collect(),
                    },
                },
                [].into_iter().collect(),
            )),

            TypeKind::Vector(ty) => Some((
                spv::Inst {
                    opcode: mo.OpTypeVector,
                    imms: [spv::Imm::Short(wk.LiteralInteger, ty.elem_count.get().into())]
                        .into_iter()
                        .collect(),
                },
                [TypeOrConst::Type(cx.intern(ty.elem))].into_iter().collect(),
            )),

            TypeKind::QPtr | TypeKind::SpvInst { .. } | TypeKind::SpvStringLiteralForExtInst => {
                None
            }
        }
    }

    // HACK(eddyb) this only exists as a helper for `spv::lower`.
    pub(super) fn always_lower_as_const(&self) -> bool {
        let mo = MappableOps::get();
        mo.OpUndef == self.opcode
    }

    // FIXME(eddyb) automate bidirectional mappings more (although the need
    // for conditional, i.e. "partial", mappings, adds a lot of complexity).
    pub(super) fn as_canonical_const(
        &self,
        cx: &Context,
        ty: Type,
        const_inputs: &[Const],
    ) -> Option<ConstKind> {
        let Self { opcode, imms } = self;
        let (&opcode, imms) = (opcode, &imms[..]);

        let wk = &spec::Spec::get().well_known;
        let mo = MappableOps::get();

        match (imms, const_inputs) {
            ([], []) if opcode == mo.OpUndef => Some(ConstKind::Undef),
            ([], []) if opcode == mo.OpConstantFalse => Some(scalar::Const::FALSE.into()),
            ([], []) if opcode == mo.OpConstantTrue => Some(scalar::Const::TRUE.into()),
            (_, []) if opcode == mo.OpConstant => {
                Some(scalar::Const::try_decode_from_spv_imms(ty.as_scalar(cx)?, imms)?.into())
            }
            _ if opcode == wk.OpConstantComposite => {
                let ty = ty.as_vector(cx)?;
                let elems = (const_inputs.len() == usize::from(ty.elem_count.get())
                    && const_inputs.iter().all(|ct| ct.as_scalar(cx).is_some()))
                .then(|| const_inputs.iter().map(|ct| *ct.as_scalar(cx).unwrap()))?;
                Some(vector::Const::from_elems(ty, elems).into())
            }
            _ => None,
        }
    }

    pub(super) fn from_canonical_const(
        cx: &Context,
        const_kind: &ConstKind,
    ) -> Option<(Self, SmallVec<[Const; 4]>)> {
        let wk = &spec::Spec::get().well_known;
        let mo = MappableOps::get();

        match const_kind {
            ConstKind::Undef => Some((mo.OpUndef.into(), [].into_iter().collect())),
            &ConstKind::Scalar(ct) => Some((
                match ct {
                    scalar::Const::FALSE => mo.OpConstantFalse.into(),
                    scalar::Const::TRUE => mo.OpConstantTrue.into(),
                    _ => {
                        spv::Inst { opcode: mo.OpConstant, imms: ct.encode_as_spv_imms().collect() }
                    }
                },
                [].into_iter().collect(),
            )),

            ConstKind::Vector(ct) => Some((
                wk.OpConstantComposite.into(),
                ct.elems().map(|elem| cx.intern(elem)).collect(),
            )),

            ConstKind::PtrToGlobalVar(_)
            | ConstKind::SpvInst { .. }
            | ConstKind::SpvStringLiteralForExtInst(_) => None,
        }
    }

    pub(super) fn as_canonical_data_inst_kind(
        &self,
        cx: &Context,
        output_types: &[Type],
    ) -> Option<DataInstKind> {
        let Self { opcode, imms } = self;
        let (&opcode, imms) = (opcode, &imms[..]);

        let scalar_op = (scalar::BoolUnOp::try_from_opcode(opcode).map(scalar::Op::from))
            .or_else(|| scalar::BoolBinOp::try_from_opcode(opcode).map(scalar::Op::from))
            .or_else(|| scalar::IntUnOp::try_from_opcode(opcode).map(scalar::Op::from))
            .or_else(|| scalar::IntBinOp::try_from_opcode(opcode).map(scalar::Op::from))
            .or_else(|| scalar::FloatUnOp::try_from_opcode(opcode).map(scalar::Op::from))
            .or_else(|| scalar::FloatBinOp::try_from_opcode(opcode).map(scalar::Op::from));
        if let Some(op) = scalar_op {
            assert_eq!(imms.len(), 0);

            // FIXME(eddyb) support vector versions of these ops as well.
            if output_types.len() == op.output_count()
                && output_types.iter().all(|ty| ty.as_scalar(cx).is_some())
            {
                Some(op.into())
            } else {
                None
            }
        } else {
            None
        }
    }

    pub(super) fn from_canonical_data_inst_kind(data_inst_kind: &DataInstKind) -> Option<Self> {
        match data_inst_kind {
            &DataInstKind::Scalar(op) => Some(match op {
                scalar::Op::BoolUnary(op) => op.to_opcode().into(),
                scalar::Op::BoolBinary(op) => op.to_opcode().into(),
                scalar::Op::IntUnary(op) => op.to_opcode().into(),
                scalar::Op::IntBinary(op) => op.to_opcode().into(),
                scalar::Op::FloatUnary(op) => op.to_opcode().into(),
                scalar::Op::FloatBinary(op) => op.to_opcode().into(),
            }),
            _ => None,
        }
    }
}
