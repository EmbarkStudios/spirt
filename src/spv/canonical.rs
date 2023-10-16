//! Bidirectional (SPIR-V <-> SPIR-T) "canonical mappings".
//!
//! Both directions are defined close together as much as possible, to:
//! - limit code duplication, making it easy to add more mappings
//! - limit how much they could even go out of sync over time
//! - prevent naming e.g. SPIR-V opcodes, outside canonicalization
//
// FIXME(eddyb) should interning attempts check/apply these canonicalizations?

use crate::spv::{self, spec};
use crate::ConstKind;
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
    OpUndef,
}

// FIXME(eddyb) decide on a visibility scope - `pub(super)` avoids some mistakes
// (using these methods outside of `spv::{lower,lift}`), but may be too restrictive.
impl spv::Inst {
    pub(super) fn as_canonical_const(&self) -> Option<ConstKind> {
        let Self { opcode, imms } = self;
        let (&opcode, imms) = (opcode, &imms[..]);

        let mo = MappableOps::get();

        if opcode == mo.OpUndef {
            assert_eq!(imms.len(), 0);
            Some(ConstKind::Undef)
        } else {
            None
        }
    }

    pub(super) fn from_canonical_const(const_kind: &ConstKind) -> Option<Self> {
        let mo = MappableOps::get();

        match const_kind {
            ConstKind::Undef => Some(mo.OpUndef.into()),

            ConstKind::PtrToGlobalVar(_)
            | ConstKind::SpvInst { .. }
            | ConstKind::SpvStringLiteralForExtInst(_) => None,
        }
    }
}
