//! SPIR-V to SPIR-T lowering.

use crate::spv::{self, spec};
use std::io;
use std::path::Path;

// FIXME(eddyb) stop abusing `io::Error` for error reporting.
fn invalid(reason: &str) -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        format!("malformed SPIR-V module ({})", reason),
    )
}

impl crate::Module {
    pub fn lower_from_spv_file(path: impl AsRef<Path>) -> io::Result<Self> {
        Self::lower_from_spv_module_parser(crate::spv::read::ModuleParser::read_from_spv_file(
            path,
        )?)
    }

    pub fn lower_from_spv_module_parser(
        mut parser: crate::spv::read::ModuleParser,
    ) -> io::Result<Self> {
        let spv_spec = spec::Spec::get();

        let mut layout = {
            let [magic, version, generator_magic, id_bound, reserved_inst_schema] = parser.header;

            // Ensure above (this is the value after any endianness swapping).
            assert_eq!(magic, spv_spec.magic);

            if reserved_inst_schema != 0 {
                return Err(invalid("unknown instruction schema - only 0 is supported"));
            }

            spv::ModuleLayout {
                header_version: version,

                original_generator_magic: generator_magic,
                original_id_bound: id_bound,

                capabilities: vec![],
            }
        };

        #[derive(Copy, Clone, Debug, PartialEq, PartialOrd)]
        enum Seq {
            Capability,
            Other,
        }
        let mut seq = None;

        let mut top_level = vec![];
        while let Some(inst) = parser.next().transpose()? {
            let opcode = inst.opcode;

            let invalid = |msg: &str| {
                let inst_name = spv_spec.instructions.get_named(opcode).unwrap().0;
                invalid(&format!("in {}: {}", inst_name, msg))
            };

            let next_seq = if opcode == spv_spec.well_known.op_capability {
                assert!(inst.result_type_id.is_none() && inst.result_id.is_none());
                match inst.operands[..] {
                    [spv::Operand::ShortImm(kind, cap)] => {
                        assert!(kind == spv_spec.well_known.capability);
                        layout.capabilities.push(cap);
                    }
                    _ => unreachable!(),
                }
                Seq::Capability
            } else {
                top_level.push(crate::TopLevel::SpvInst(inst));
                Seq::Other
            };
            if !(seq <= Some(next_seq)) {
                return Err(invalid(&format!(
                    "out of order: {:?} instructions must precede {:?} instructions",
                    next_seq, seq
                )));
            }
            seq = Some(next_seq);
        }

        Ok(Self {
            layout: crate::ModuleLayout::Spv(layout),
            top_level,
        })
    }
}
