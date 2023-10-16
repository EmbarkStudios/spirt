//! Bidirectional (SPIR-V <-> SPIR-T) "canonical mappings".
//!
//! Both directions are defined close together as much as possible, to:
//! - limit code duplication, making it easy to add more mappings
//! - limit how much they could even go out of sync over time
//! - prevent naming e.g. SPIR-V opcodes, outside canonicalization
//
// FIXME(eddyb) should interning attempts check/apply these canonicalizations?

use crate::spv::{self, spec};
use crate::{scalar, ConstKind, Context, Type, TypeKind};
use lazy_static::lazy_static;

// FIXME(eddyb) these ones could maybe make use of build script generation.
macro_rules! def_mappable_ops {
    ($($op:ident),+ $(,)?) => {
        #[allow(non_snake_case)]
        struct MappableOps {
            $($op: spec::Opcode,)+
        }
        impl MappableOps {
            #[inline(always)]
            #[must_use]
            pub fn get() -> &'static MappableOps {
                lazy_static! {
                    static ref MAPPABLE_OPS: MappableOps = {
                        let spv_spec = spec::Spec::get();
                        MappableOps {
                            $($op: spv_spec.instructions.lookup(stringify!($op)).unwrap(),)+
                        }
                    };
                }
                &MAPPABLE_OPS
            }
        }
    };
}
def_mappable_ops! {
    OpTypeBool,
    OpTypeInt,
    OpTypeFloat,

    OpUndef,
    OpConstantFalse,
    OpConstantTrue,
    OpConstant,
}

impl scalar::Const {
    fn try_decode_from_spv_imms(ty: scalar::Type, imms: &[spv::Imm]) -> Option<scalar::Const> {
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

    fn encode_as_spv_imms(&self) -> impl Iterator<Item = spv::Imm> {
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
    pub(super) fn as_canonical_type(&self) -> Option<TypeKind> {
        let Self { opcode, imms } = self;
        let (&opcode, imms) = (opcode, &imms[..]);

        let mo = MappableOps::get();

        let int_width = || scalar::IntWidth::try_from_bits(self.int_or_float_type_bit_width()?);
        match imms {
            [] if opcode == mo.OpTypeBool => Some(scalar::Type::Bool.into()),
            &[_, spv::Imm::Short(_, 0)] if opcode == mo.OpTypeInt => {
                Some(scalar::Type::UInt(int_width()?).into())
            }
            &[_, spv::Imm::Short(_, 1)] if opcode == mo.OpTypeInt => {
                Some(scalar::Type::SInt(int_width()?).into())
            }
            [_] if opcode == mo.OpTypeFloat => Some(
                scalar::Type::Float(scalar::FloatWidth::try_from_bits(
                    self.int_or_float_type_bit_width()?,
                )?)
                .into(),
            ),
            _ => None,
        }
    }

    pub(super) fn from_canonical_type(type_kind: &TypeKind) -> Option<Self> {
        let wk = &spec::Spec::get().well_known;
        let mo = MappableOps::get();

        match type_kind {
            &TypeKind::Scalar(ty) => match ty {
                scalar::Type::Bool => Some(mo.OpTypeBool.into()),
                scalar::Type::SInt(w) | scalar::Type::UInt(w) => Some(spv::Inst {
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
                }),
                scalar::Type::Float(w) => Some(spv::Inst {
                    opcode: mo.OpTypeFloat,
                    imms: [spv::Imm::Short(wk.LiteralInteger, w.bits())].into_iter().collect(),
                }),
            },

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
    pub(super) fn as_canonical_const(&self, cx: &Context, ty: Type) -> Option<ConstKind> {
        let Self { opcode, imms } = self;
        let (&opcode, imms) = (opcode, &imms[..]);

        let mo = MappableOps::get();

        match imms {
            [] if opcode == mo.OpUndef => Some(ConstKind::Undef),
            [] if opcode == mo.OpConstantFalse => Some(scalar::Const::FALSE.into()),
            [] if opcode == mo.OpConstantTrue => Some(scalar::Const::TRUE.into()),
            _ if opcode == mo.OpConstant => {
                Some(scalar::Const::try_decode_from_spv_imms(ty.as_scalar(cx)?, imms)?.into())
            }
            _ => None,
        }
    }

    pub(super) fn from_canonical_const(const_kind: &ConstKind) -> Option<Self> {
        let mo = MappableOps::get();

        match const_kind {
            ConstKind::Undef => Some(mo.OpUndef.into()),
            ConstKind::Scalar(scalar::Const::FALSE) => Some(mo.OpConstantFalse.into()),
            ConstKind::Scalar(scalar::Const::TRUE) => Some(mo.OpConstantTrue.into()),
            ConstKind::Scalar(ct) => {
                Some(spv::Inst { opcode: mo.OpConstant, imms: ct.encode_as_spv_imms().collect() })
            }

            ConstKind::PtrToGlobalVar(_)
            | ConstKind::SpvInst { .. }
            | ConstKind::SpvStringLiteralForExtInst(_) => None,
        }
    }
}
