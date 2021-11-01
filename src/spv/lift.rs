//! SPIR-T to SPIR-V lifting.

use crate::spv::{self, spec};
use std::collections::{BTreeMap, BTreeSet};
use std::num::NonZeroU32;
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

        // Collect uses scattered throughout the module, that require def IDs.
        let mut ext_inst_imports = BTreeSet::new();
        for top_level in &self.top_level {
            match top_level {
                crate::TopLevel::Misc(misc) => {
                    for input in &misc.inputs {
                        match input {
                            crate::MiscInput::SpvImm(_) | crate::MiscInput::SpvUntrackedId(_) => {}
                            crate::MiscInput::SpvExtInstImport(name) => {
                                ext_inst_imports.insert(name.clone());
                            }
                        }
                    }
                }
            }
        }

        // FIXME(eddyb) recompute this based on the module.
        let mut id_bound = dialect.original_id_bound;
        let mut id_bound_overflowed = false;
        let mut alloc_id = || {
            let id = id_bound;

            // FIXME(eddyb) use `id_bound.checked_add(1)` once that's stabilized.
            match id_bound.get().checked_add(1).and_then(NonZeroU32::new) {
                Some(new_bound) => id_bound = new_bound,
                None => {
                    id_bound_overflowed = true;
                }
            }

            id
        };

        // IDs can be allocated once we have the full *sorted* sets needing them.
        let ext_inst_import_ids: BTreeMap<_, _> = ext_inst_imports
            .into_iter()
            .map(|name| (name, alloc_id()))
            .collect();

        if id_bound_overflowed {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "ID bound of SPIR-V module doesn't fit in 32 bits",
            ));
        }

        let reserved_inst_schema = 0;
        let header = [
            spv_spec.magic,
            (u32::from(dialect.version_major) << 16) | (u32::from(dialect.version_minor) << 8),
            dialect.original_generator_magic,
            id_bound.get(),
            reserved_inst_schema,
        ];

        let mut emitter = spv::write::ModuleEmitter::with_header(header);

        for cap_inst in dialect.capability_insts() {
            emitter.push_inst(&cap_inst)?;
        }
        for ext_inst in dialect.extension_insts() {
            emitter.push_inst(&ext_inst)?;
        }
        for (name, &id) in &ext_inst_import_ids {
            emitter.push_inst(&spv::Inst {
                opcode: spv_spec.well_known.op_ext_inst_import,
                result_type_id: None,
                result_id: Some(id),
                operands: spv::encode_literal_string(name).collect(),
            })?;
        }
        emitter.push_inst(&spv::Inst {
            opcode: spv_spec.well_known.op_memory_model,
            result_type_id: None,
            result_id: None,
            operands: [
                spv::Operand::Imm(spv::Imm::Short(
                    spv_spec.well_known.addressing_model,
                    dialect.addressing_model,
                )),
                spv::Operand::Imm(spv::Imm::Short(
                    spv_spec.well_known.memory_model,
                    dialect.memory_model,
                )),
            ]
            .into_iter()
            .collect(),
        })?;
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
                            crate::MiscInput::SpvExtInstImport(ref name) => spv::Operand::Id(
                                spv_spec.well_known.id_ref,
                                ext_inst_import_ids[name],
                            ),
                        })
                        .collect(),
                },
            };
            emitter.push_inst(&inst)?;
        }

        Ok(emitter)
    }
}
