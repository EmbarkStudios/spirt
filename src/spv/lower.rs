//! SPIR-V to SPIR-T lowering.

use crate::spv::{self, spec};
use std::collections::BTreeSet;
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
        Self::lower_from_spv_module_parser(spv::read::ModuleParser::read_from_spv_file(path)?)
    }

    pub fn lower_from_spv_module_parser(mut parser: spv::read::ModuleParser) -> io::Result<Self> {
        let spv_spec = spec::Spec::get();

        let mut dialect = {
            let [magic, version, generator_magic, id_bound, reserved_inst_schema] = parser.header;

            // Ensured above (this is the value after any endianness swapping).
            assert_eq!(magic, spv_spec.magic);

            let [version_reserved_hi, version_major, version_minor, version_reserved_lo] =
                version.to_be_bytes();

            if (version_reserved_lo, version_reserved_hi) != (0, 0) {
                return Err(invalid(&format!(
                    "version 0x{:08x} is not in expected (0.major.minor.0) form",
                    version
                )));
            }

            if reserved_inst_schema != 0 {
                return Err(invalid(&format!(
                    "unknown instruction schema {} - only 0 is supported",
                    reserved_inst_schema
                )));
            }

            spv::Dialect {
                version_major,
                version_minor,

                original_generator_magic: generator_magic,
                original_id_bound: id_bound,

                capabilities: BTreeSet::new(),
                extensions: BTreeSet::new(),
            }
        };

        #[derive(Copy, Clone, Debug, PartialEq, PartialOrd)]
        enum Seq {
            Capability,
            Extension,
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
                    [spv::Operand::Imm(spv::Imm::Short(kind, cap))] => {
                        assert!(kind == spv_spec.well_known.capability);
                        dialect.capabilities.insert(cap);
                    }
                    _ => unreachable!(),
                }
                Seq::Capability
            } else if opcode == spv_spec.well_known.op_extension {
                assert!(inst.result_type_id.is_none() && inst.result_id.is_none());
                let ext = spv::extract_literal_string(&inst.operands)
                    .map_err(|e| invalid(&format!("{} in {:?}", e, e.as_bytes())))?;
                dialect.extensions.insert(ext);
                Seq::Extension
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
            dialect: crate::ModuleDialect::Spv(dialect),
            top_level,
        })
    }
}
