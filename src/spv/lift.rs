//! SPIR-T to SPIR-V lifting.

use crate::spv::{self, spec};
use std::collections::{BTreeMap, BTreeSet};
use std::num::NonZeroU32;
use std::path::Path;
use std::{io, iter};

impl spv::Dialect {
    pub fn capability_insts(&self) -> impl Iterator<Item = spv::Inst> + '_ {
        let wk = &spec::Spec::get().well_known;
        self.capabilities.iter().map(move |&cap| spv::Inst {
            opcode: wk.OpCapability,
            result_type_id: None,
            result_id: None,
            operands: iter::once(spv::Operand::Imm(spv::Imm::Short(wk.Capability, cap))).collect(),
        })
    }

    pub fn extension_insts(&self) -> impl Iterator<Item = spv::Inst> + '_ {
        let wk = &spec::Spec::get().well_known;
        self.extensions.iter().map(move |ext| spv::Inst {
            opcode: wk.OpExtension,
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
        let wk = &spv_spec.well_known;

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
        let mut debug_strings = BTreeSet::new();
        for top_level in &self.top_level {
            match top_level {
                crate::TopLevel::Misc(misc) => {
                    for input in &misc.inputs {
                        match input {
                            crate::MiscInput::SpvImm(_) | crate::MiscInput::SpvUntrackedId(_) => {}
                            crate::MiscInput::SpvExtInstImport(name) => {
                                ext_inst_imports.insert(name.clone());
                            }
                            crate::MiscInput::SpvDebugString(name) => {
                                debug_strings.insert(name.clone());
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
        let debug_string_ids: BTreeMap<_, _> =
            debug_strings.into_iter().map(|s| (s, alloc_id())).collect();

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
                opcode: wk.OpExtInstImport,
                result_type_id: None,
                result_id: Some(id),
                operands: spv::encode_literal_string(name).collect(),
            })?;
        }
        emitter.push_inst(&spv::Inst {
            opcode: wk.OpMemoryModel,
            result_type_id: None,
            result_id: None,
            operands: [
                spv::Operand::Imm(spv::Imm::Short(
                    wk.AddressingModel,
                    dialect.addressing_model,
                )),
                spv::Operand::Imm(spv::Imm::Short(wk.MemoryModel, dialect.memory_model)),
            ]
            .into_iter()
            .collect(),
        })?;

        // Collect the various sources of attributes.
        let mut entry_point_insts = vec![];
        let mut execution_mode_insts = vec![];
        let mut debug_name_insts = vec![];
        let mut decoration_insts = vec![];

        let mut push_attr = |target_id, attr: &crate::Attr| match attr {
            crate::Attr::SpvEntryPoint {
                params,
                interface_ids,
            } => {
                entry_point_insts.push(spv::Inst {
                    opcode: wk.OpEntryPoint,
                    result_type_id: None,
                    result_id: None,
                    operands: [
                        spv::Operand::Imm(params[0]),
                        spv::Operand::ForwardIdRef(wk.IdRef, target_id),
                    ]
                    .into_iter()
                    .chain(params[1..].iter().map(|&imm| spv::Operand::Imm(imm)))
                    .chain(
                        interface_ids
                            .iter()
                            .map(|&id| spv::Operand::ForwardIdRef(wk.IdRef, id)),
                    )
                    .collect(),
                });
            }
            crate::Attr::SpvAnnotation { opcode, params } => {
                let inst = spv::Inst {
                    opcode: *opcode,
                    result_type_id: None,
                    result_id: None,
                    operands: iter::once(spv::Operand::ForwardIdRef(wk.IdRef, target_id))
                        .chain(params.iter().map(|&imm| spv::Operand::Imm(imm)))
                        .collect(),
                };

                if [wk.OpExecutionMode, wk.OpExecutionModeId].contains(&opcode) {
                    execution_mode_insts.push(inst);
                } else if [wk.OpName, wk.OpMemberName].contains(&opcode) {
                    debug_name_insts.push(inst);
                } else {
                    decoration_insts.push(inst);
                }
            }
        };
        for top_level in &self.top_level {
            match top_level {
                crate::TopLevel::Misc(misc) => {
                    if let Some(attrs) = &misc.attrs {
                        let target_id = match misc.output {
                            Some(crate::MiscOutput::SpvResult { result_id, .. }) => result_id,
                            None => unreachable!(
                                "FIXME: it shouldn't be possible to attach \
                                attributes to instructions without an output"
                            ),
                        };
                        for attr in attrs.iter() {
                            push_attr(target_id, attr);
                        }
                    }
                }
            }
        }

        // FIXME(eddyb) maybe make a helper for `push_inst` with an iterator?
        for entry_point_inst in entry_point_insts {
            emitter.push_inst(&entry_point_inst)?;
        }
        for execution_mode_inst in execution_mode_insts {
            emitter.push_inst(&execution_mode_inst)?;
        }

        for (s, &id) in &debug_string_ids {
            emitter.push_inst(&spv::Inst {
                opcode: wk.OpString,
                result_type_id: None,
                result_id: Some(id),
                operands: spv::encode_literal_string(s).collect(),
            })?;
        }

        // TODO(eddyb) this is where `OpSource*`s should go.

        for debug_name_inst in debug_name_insts {
            emitter.push_inst(&debug_name_inst)?;
        }

        // TODO(eddyb) this is where `OpModuleProcessed`s should go.

        for decoration_inst in decoration_insts {
            emitter.push_inst(&decoration_inst)?;
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
                            crate::MiscInput::SpvUntrackedId(id) => spv::Operand::Id(wk.IdRef, id),
                            crate::MiscInput::SpvExtInstImport(ref name) => {
                                spv::Operand::Id(wk.IdRef, ext_inst_import_ids[name])
                            }
                            crate::MiscInput::SpvDebugString(ref s) => {
                                spv::Operand::Id(wk.IdRef, debug_string_ids[s])
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
