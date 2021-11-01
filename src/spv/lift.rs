//! SPIR-T to SPIR-V lifting.

use crate::spv::{self, spec};
use std::path::Path;
use std::{io, iter};

impl spv::Dialect {
    pub fn capability_insts(&self) -> impl Iterator<Item = spv::Inst> + '_ {
        let spec::WellKnown {
            op_capability,
            capability,
            ..
        } = spec::Spec::get().well_known;
        self.capabilities.iter().map(move |&cap| spv::Inst {
            opcode: op_capability,
            result_type_id: None,
            result_id: None,
            operands: iter::once(spv::Operand::Imm(spv::Imm::Short(capability, cap))).collect(),
        })
    }

    pub fn extension_insts(&self) -> impl Iterator<Item = spv::Inst> + '_ {
        let spec::WellKnown { op_extension, .. } = spec::Spec::get().well_known;
        self.extensions.iter().map(move |ext| spv::Inst {
            opcode: op_extension,
            result_type_id: None,
            result_id: None,
            operands: spv::encode_literal_string(ext).collect(),
        })
    }
}

impl crate::Module {
    pub fn lift_to_spv_file(&self, path: impl AsRef<Path>) -> io::Result<()> {
        self.lift_to_spv_module_emitter()?.write_to_spv_file(path)
    }

    pub fn lift_to_spv_module_emitter(&self) -> io::Result<spv::write::ModuleEmitter> {
        let spv_spec = spec::Spec::get();

        let dialect = match &self.dialect {
            crate::ModuleDialect::Spv(dialect) => dialect,

            // FIXME(eddyb) support by computing some valid "minimum viable"
            // `spv::Dialect`, or by taking it as additional input.
            #[allow(unreachable_patterns)]
            _ => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "not a SPIR-V module",
                ));
            }
        };
        let reserved_inst_schema = 0;
        let header = [
            spv_spec.magic,
            (u32::from(dialect.version_major) << 16) | (u32::from(dialect.version_minor) << 8),
            dialect.original_generator_magic,
            // FIXME(eddyb) update this if the module has been modified.
            dialect.original_id_bound,
            reserved_inst_schema,
        ];

        let mut emitter = spv::write::ModuleEmitter::with_header(header);

        for cap_inst in dialect.capability_insts() {
            emitter.push_inst(&cap_inst)?;
        }
        for ext_inst in dialect.extension_insts() {
            emitter.push_inst(&ext_inst)?;
        }
        for top_level in &self.top_level {
            let inst = match top_level {
                crate::TopLevel::Misc(misc) => spv::Inst {
                    opcode: match misc.kind {
                        crate::MiscKind::SpvInst { opcode } => opcode,
                    },
                    result_type_id: misc.output.as_ref().and_then(|output| match *output {
                        crate::MiscOutput::SpvResult { result_type_id, .. } => result_type_id,
                    }),
                    result_id: misc.output.as_ref().map(|output| match *output {
                        crate::MiscOutput::SpvResult { result_id, .. } => result_id,
                    }),
                    operands: misc
                        .inputs
                        .iter()
                        .map(|input| match *input {
                            crate::MiscInput::SpvImm(imm) => spv::Operand::Imm(imm),
                            crate::MiscInput::SpvUntrackedId(id) => {
                                spv::Operand::Id(spv_spec.well_known.id_ref, id)
                            }
                        })
                        .collect(),
                },
            };
            emitter.push_inst(&inst)?;
        }

        Ok(emitter)
    }
}
