//! SPIR-V to SPIR-T lowering.

use crate::spv::{self, spec};
use crate::{Context, InternedStr};
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use std::collections::{BTreeMap, BTreeSet};
use std::num::NonZeroU32;
use std::path::Path;
use std::rc::Rc;
use std::{io, iter, mem};

/// SPIR-T definition of a SPIR-V ID.
enum IdDef {
    SpvExtInstImport(InternedStr),
    SpvDebugString(InternedStr),
}

// FIXME(eddyb) stop abusing `io::Error` for error reporting.
fn invalid(reason: &str) -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        format!("malformed SPIR-V module ({})", reason),
    )
}

impl crate::Module {
    pub fn lower_from_spv_file(cx: Rc<Context>, path: impl AsRef<Path>) -> io::Result<Self> {
        Self::lower_from_spv_module_parser(cx, spv::read::ModuleParser::read_from_spv_file(path)?)
    }

    pub fn lower_from_spv_module_parser(
        cx: Rc<Context>,
        parser: spv::read::ModuleParser,
    ) -> io::Result<Self> {
        let spv_spec = spec::Spec::get();
        let wk = &spv_spec.well_known;

        // HACK(eddyb) used to quickly check whether an `OpVariable` is global.
        let storage_class_function_operand =
            spv::Operand::Imm(spv::Imm::Short(wk.StorageClass, wk.Function));

        let mut module = {
            let [
                magic,
                version,
                generator_magic,
                id_bound,
                reserved_inst_schema,
            ] = parser.header;

            // Ensured above (this is the value after any endianness swapping).
            assert_eq!(magic, spv_spec.magic);

            let [
                version_reserved_hi,
                version_major,
                version_minor,
                version_reserved_lo,
            ] = version.to_be_bytes();

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

            Self::new(
                cx.clone(),
                crate::ModuleDialect::Spv(spv::Dialect {
                    version_major,
                    version_minor,

                    original_id_bound: NonZeroU32::new(id_bound)
                        .ok_or_else(|| invalid("ID bound 0"))?,

                    capabilities: BTreeSet::new(),
                    extensions: BTreeSet::new(),

                    addressing_model: 0,
                    memory_model: 0,
                }),
                crate::ModuleDebugInfo::Spv(spv::ModuleDebugInfo {
                    original_generator_magic: NonZeroU32::new(generator_magic),

                    source_languages: BTreeMap::new(),
                    source_extensions: vec![],
                    module_processes: vec![],
                }),
            )
        };

        #[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
        enum Seq {
            Capability,
            Extension,
            ExtInstImport,
            MemoryModel,
            EntryPoint,
            ExecutionMode,
            DebugStringAndSource,
            DebugName,
            DebugModuleProcessed,
            Decoration,

            // NOTE(eddyb) not its own section, but only a "checkpoint", forcing
            // instructions following `OpLine`/`OpNoLine` into later sections.
            DebugLine,

            Globals,
            Functions,
        }
        let mut seq = None;

        let mut has_memory_model = false;
        let mut pending_attr_sets = FxHashMap::<spv::Id, crate::AttrSetDef>::default();
        let mut current_debug_line = None;
        let mut current_block_id = None; // HACK(eddyb) for `current_debug_line` resets.
        let mut id_defs = FxHashMap::default();
        let mut current_func = None;

        let mut spv_insts = parser.peekable();
        while let Some(inst) = spv_insts.next().transpose()? {
            let opcode = inst.opcode;

            let invalid = |msg: &str| {
                let inst_name = spv_spec.instructions.get_named(opcode).unwrap().0;
                invalid(&format!("in {}: {}", inst_name, msg))
            };

            // Handle line debuginfo early, as it doesn't have its own section,
            // but rather can go almost anywhere among globals and functions.
            if [wk.OpLine, wk.OpNoLine].contains(&opcode) {
                assert!(inst.result_type_id.is_none() && inst.result_id.is_none());

                current_debug_line = if opcode == wk.OpLine {
                    match inst.operands[..] {
                        [
                            spv::Operand::Id(fp_kind, file_path_id),
                            spv::Operand::Imm(spv::Imm::Short(l_kind, line)),
                            spv::Operand::Imm(spv::Imm::Short(c_kind, col)),
                        ] => {
                            assert!(
                                fp_kind == wk.IdRef && [l_kind, c_kind] == [wk.LiteralInteger; 2]
                            );
                            let file_path = match id_defs.get(&file_path_id) {
                                Some(&IdDef::SpvDebugString(s)) => s,
                                _ => {
                                    return Err(invalid(&format!(
                                        "%{} is not an OpString",
                                        file_path_id
                                    )));
                                }
                            };
                            Some((file_path, line, col))
                        }
                        _ => unreachable!(),
                    }
                } else {
                    assert!(inst.operands.is_empty());
                    None
                };

                // Advance to `Seq::DebugLine` if we're not there yet, forcing
                // any following instructions to not be in earlier sections.
                seq = seq.max(Some(Seq::DebugLine));
                continue;
            }

            // Reset line debuginfo when crossing/leaving blocks.
            let new_block_id = if opcode == wk.OpLabel {
                Some(inst.result_id.unwrap())
            } else if opcode == wk.OpFunctionEnd {
                None
            } else {
                current_block_id
            };
            if current_block_id != new_block_id {
                current_debug_line = None;
            }
            current_block_id = new_block_id;

            let mut attr_set = inst
                .result_id
                .and_then(|id| pending_attr_sets.remove(&id))
                .unwrap_or_default();

            if let Some((file_path, line, col)) = current_debug_line {
                // FIXME(eddyb) use `get_or_insert_default` once that's stabilized.
                attr_set.attrs.insert(crate::Attr::SpvDebugLine {
                    file_path,
                    line,
                    col,
                });
            }

            let mut attr_set = cx.intern(attr_set);

            let next_seq = if opcode == wk.OpCapability {
                assert!(inst.result_type_id.is_none() && inst.result_id.is_none());
                let cap = match inst.operands[..] {
                    [spv::Operand::Imm(spv::Imm::Short(kind, cap))] => {
                        assert!(kind == wk.Capability);
                        cap
                    }
                    _ => unreachable!(),
                };

                match &mut module.dialect {
                    crate::ModuleDialect::Spv(dialect) => {
                        dialect.capabilities.insert(cap);
                    }
                }

                Seq::Capability
            } else if opcode == wk.OpExtension {
                assert!(inst.result_type_id.is_none() && inst.result_id.is_none());
                let ext = spv::extract_literal_string(&inst.operands)
                    .map_err(|e| invalid(&format!("{} in {:?}", e, e.as_bytes())))?;

                match &mut module.dialect {
                    crate::ModuleDialect::Spv(dialect) => {
                        dialect.extensions.insert(ext);
                    }
                }

                Seq::Extension
            } else if opcode == wk.OpExtInstImport {
                assert!(inst.result_type_id.is_none());
                let id = inst.result_id.unwrap();
                let name = spv::extract_literal_string(&inst.operands)
                    .map_err(|e| invalid(&format!("{} in {:?}", e, e.as_bytes())))?;

                id_defs.insert(id, IdDef::SpvExtInstImport(cx.intern(name)));

                Seq::ExtInstImport
            } else if opcode == wk.OpMemoryModel {
                assert!(inst.result_type_id.is_none() && inst.result_id.is_none());
                let (addressing_model, memory_model) = match inst.operands[..] {
                    [
                        spv::Operand::Imm(spv::Imm::Short(am_kind, am)),
                        spv::Operand::Imm(spv::Imm::Short(mm_kind, mm)),
                    ] => {
                        assert!(am_kind == wk.AddressingModel && mm_kind == wk.MemoryModel);
                        (am, mm)
                    }
                    _ => unreachable!(),
                };

                if has_memory_model {
                    return Err(invalid("duplicate OpMemoryModel"));
                }
                has_memory_model = true;

                match &mut module.dialect {
                    crate::ModuleDialect::Spv(dialect) => {
                        dialect.addressing_model = addressing_model;
                        dialect.memory_model = memory_model;
                    }
                }

                Seq::MemoryModel
            } else if opcode == wk.OpString {
                assert!(inst.result_type_id.is_none());
                let id = inst.result_id.unwrap();
                let s = spv::extract_literal_string(&inst.operands)
                    .map_err(|e| invalid(&format!("{} in {:?}", e, e.as_bytes())))?;

                id_defs.insert(id, IdDef::SpvDebugString(cx.intern(s)));

                // NOTE(eddyb) debug instructions are handled earlier in the code
                // for organizatory purposes, see `Seq` for the in-module order.
                Seq::DebugStringAndSource
            } else if opcode == wk.OpSource {
                assert!(inst.result_type_id.is_none() && inst.result_id.is_none());
                let (lang, version) = match inst.operands[..] {
                    [
                        spv::Operand::Imm(spv::Imm::Short(l_kind, lang)),
                        spv::Operand::Imm(spv::Imm::Short(v_kind, version)),
                        ..,
                    ] => {
                        assert!(l_kind == wk.SourceLanguage && v_kind == wk.LiteralInteger);
                        (lang, version)
                    }
                    _ => unreachable!(),
                };

                let debug_sources = match &mut module.debug_info {
                    crate::ModuleDebugInfo::Spv(debug_info) => debug_info
                        .source_languages
                        .entry(spv::DebugSourceLang { lang, version })
                        .or_default(),
                };

                match inst.operands[2..] {
                    [spv::Operand::Id(fp_kind, file_path_id), ref contents @ ..] => {
                        assert!(fp_kind == wk.IdRef);
                        let file_path = match id_defs.get(&file_path_id) {
                            Some(&IdDef::SpvDebugString(s)) => s,
                            _ => {
                                return Err(invalid(&format!(
                                    "%{} is not an OpString",
                                    file_path_id
                                )));
                            }
                        };
                        let mut contents = if contents.is_empty() {
                            String::new()
                        } else {
                            spv::extract_literal_string(contents)
                                .map_err(|e| invalid(&format!("{} in {:?}", e, e.as_bytes())))?
                        };

                        // Absorb all following `OpSourceContinued` into `contents`.
                        while let Some(Ok(cont_inst)) = spv_insts.peek() {
                            if cont_inst.opcode != wk.OpSourceContinued {
                                break;
                            }
                            let cont_inst = spv_insts.next().unwrap().unwrap();

                            assert!(
                                cont_inst.result_type_id.is_none() && cont_inst.result_id.is_none()
                            );
                            let cont_contents = spv::extract_literal_string(&cont_inst.operands)
                                .map_err(|e| invalid(&format!("{} in {:?}", e, e.as_bytes())))?;
                            contents += &cont_contents;
                        }

                        debug_sources.file_contents.insert(file_path, contents);
                    }
                    [] => {}
                    _ => unreachable!(),
                }

                // NOTE(eddyb) debug instructions are handled earlier in the code
                // for organizatory purposes, see `Seq` for the in-module order.
                Seq::DebugStringAndSource
            } else if opcode == wk.OpSourceContinued {
                return Err(invalid("must follow OpSource"));
            } else if opcode == wk.OpSourceExtension {
                assert!(inst.result_type_id.is_none() && inst.result_id.is_none());
                let ext = spv::extract_literal_string(&inst.operands)
                    .map_err(|e| invalid(&format!("{} in {:?}", e, e.as_bytes())))?;

                match &mut module.debug_info {
                    crate::ModuleDebugInfo::Spv(debug_info) => {
                        debug_info.source_extensions.push(ext);
                    }
                }

                // NOTE(eddyb) debug instructions are handled earlier in the code
                // for organizatory purposes, see `Seq` for the in-module order.
                Seq::DebugStringAndSource
            } else if opcode == wk.OpModuleProcessed {
                assert!(inst.result_type_id.is_none() && inst.result_id.is_none());
                let proc = spv::extract_literal_string(&inst.operands)
                    .map_err(|e| invalid(&format!("{} in {:?}", e, e.as_bytes())))?;

                match &mut module.debug_info {
                    crate::ModuleDebugInfo::Spv(debug_info) => {
                        debug_info.module_processes.push(proc);
                    }
                }

                // NOTE(eddyb) debug instructions are handled earlier in the code
                // for organizatory purposes, see `Seq` for the in-module order.
                Seq::DebugModuleProcessed
            } else if opcode == wk.OpEntryPoint {
                assert!(inst.result_type_id.is_none() && inst.result_id.is_none());

                let target_id = match inst.operands[1] {
                    spv::Operand::Id(kind, id) => {
                        assert!(kind == wk.IdRef);
                        id
                    }
                    _ => unreachable!(),
                };

                let mut params = SmallVec::new();
                let mut interface_ids = SmallVec::new();
                for operand in iter::once(&inst.operands[0]).chain(&inst.operands[2..]) {
                    match *operand {
                        spv::Operand::Imm(imm) => {
                            assert!(interface_ids.is_empty());
                            params.push(imm);
                        }
                        spv::Operand::Id(kind, id) => {
                            assert!(kind == wk.IdRef);
                            interface_ids.push(id);
                        }
                    }
                }

                pending_attr_sets
                    .entry(target_id)
                    .or_default()
                    .attrs
                    .insert(crate::Attr::SpvEntryPoint {
                        params,
                        interface_ids,
                    });

                Seq::EntryPoint
            } else if [
                wk.OpExecutionMode,
                wk.OpExecutionModeId, // FIXME(eddyb) not actually supported
                wk.OpName,
                wk.OpMemberName,
                wk.OpDecorate,
                wk.OpMemberDecorate,
                wk.OpDecorateId, // FIXME(eddyb) not actually supported
                wk.OpDecorateString,
                wk.OpMemberDecorateString,
            ]
            .contains(&opcode)
            {
                assert!(inst.result_type_id.is_none() && inst.result_id.is_none());

                let target_id = match inst.operands[0] {
                    spv::Operand::Id(kind, id) => {
                        assert!(kind == wk.IdRef);
                        id
                    }
                    _ => unreachable!(),
                };
                let params = inst.operands[1..]
                    .iter()
                    .map(|operand| match *operand {
                        spv::Operand::Imm(imm) => Ok(imm),
                        spv::Operand::Id(..) => Err(invalid("unsupported decoration with ID")),
                    })
                    .collect::<Result<_, _>>()?;
                pending_attr_sets
                    .entry(target_id)
                    .or_default()
                    .attrs
                    .insert(crate::Attr::SpvAnnotation { opcode, params });

                if [wk.OpExecutionMode, wk.OpExecutionModeId].contains(&opcode) {
                    Seq::ExecutionMode
                } else if [wk.OpName, wk.OpMemberName].contains(&opcode) {
                    Seq::DebugName
                } else {
                    Seq::Decoration
                }
            } else if opcode == wk.OpFunction {
                if current_func.is_some() {
                    return Err(invalid("nested OpFunction while still in a function"));
                }

                let func_id = inst.result_id.unwrap();
                // FIXME(eddyb) hide this from SPIR-T, it's the function return
                // type, *not* the function type, which is in `func_type_id`.
                let func_ret_type_id = inst.result_type_id.unwrap();

                let (func_ctrl, func_type_id) = match inst.operands[..] {
                    [
                        spv::Operand::Imm(spv::Imm::Short(fc_kind, func_ctrl)),
                        spv::Operand::Id(ft_kind, func_type_id),
                    ] => {
                        assert!(fc_kind == wk.FunctionControl && ft_kind == wk.IdRef);
                        (func_ctrl, func_type_id)
                    }
                    _ => unreachable!(),
                };

                // FIXME(eddyb) pull out this information from the first entry
                // in the `insts` field, into new fields of `Func`.
                let func_inst = crate::Misc {
                    kind: crate::MiscKind::SpvInst {
                        opcode: inst.opcode,
                    },
                    output: Some(crate::MiscOutput::SpvResult {
                        result_type_id: Some(func_ret_type_id),
                        result_id: func_id,
                    }),
                    inputs: [
                        crate::MiscInput::SpvImm(spv::Imm::Short(wk.FunctionControl, func_ctrl)),
                        crate::MiscInput::SpvUntrackedId(func_type_id),
                    ]
                    .into_iter()
                    .collect(),
                    attrs: mem::take(&mut attr_set),
                };

                current_func = Some(crate::Func {
                    insts: vec![func_inst],
                });

                Seq::Functions
            } else if opcode == wk.OpFunctionEnd {
                assert!(inst.result_type_id.is_none() && inst.result_id.is_none());
                assert!(inst.operands.is_empty());

                let mut func = current_func
                    .take()
                    .ok_or_else(|| invalid("nested OpFunction while still in a function"))?;

                // FIXME(eddyb) don't keep this instruction explicitly.
                func.insts.push(crate::Misc {
                    kind: crate::MiscKind::SpvInst {
                        opcode: inst.opcode,
                    },
                    output: None,
                    inputs: [].into_iter().collect(),
                    attrs: crate::AttrSet::default(),
                });

                module.funcs.push(func);

                Seq::Functions
            } else {
                let misc = crate::Misc {
                    kind: crate::MiscKind::SpvInst {
                        opcode: inst.opcode,
                    },
                    output: inst
                        .result_id
                        .map(|result_id| crate::MiscOutput::SpvResult {
                            result_type_id: inst.result_type_id,
                            result_id,
                        }),
                    inputs: inst
                        .operands
                        .iter()
                        .map(|operand| {
                            Ok(match *operand {
                                spv::Operand::Imm(imm) => crate::MiscInput::SpvImm(imm),
                                spv::Operand::Id(_, id) => match id_defs.get(&id) {
                                    Some(&IdDef::SpvExtInstImport(name)) => {
                                        crate::MiscInput::SpvExtInstImport(name)
                                    }
                                    Some(&IdDef::SpvDebugString(s)) => {
                                        return Err(invalid(&format!(
                                            "unsupported use of `OpString {:?}` \
                                             outside `OpSource` or `OpLine`",
                                            &cx[s]
                                        )));
                                    }
                                    None => crate::MiscInput::SpvUntrackedId(id),
                                },
                            })
                        })
                        .collect::<Result<_, _>>()?,
                    attrs: mem::take(&mut attr_set),
                };

                match &mut current_func {
                    Some(func) => {
                        assert_eq!(seq, Some(Seq::Functions));
                        func.insts.push(misc)
                    }
                    None => module.globals.push(crate::Global::Misc(misc)),
                }

                match spv_spec.instructions[opcode].category {
                    spec::InstructionCategory::Type | spec::InstructionCategory::Const => {
                        Seq::Globals
                    }

                    // Where `OpVariable` belongs depends on its `StorageClass`
                    // operand is `Function` (function-local) or not (global).
                    _ if opcode == wk.OpVariable
                        && inst.operands[0] != storage_class_function_operand =>
                    {
                        Seq::Globals
                    }

                    // `OpUndef` can appear either among constants, or in a
                    // function, so at most advance `seq` to globals.
                    _ if opcode == wk.OpUndef => seq.max(Some(Seq::Globals)).unwrap(),

                    spec::InstructionCategory::Other => Seq::Functions,
                }
            };
            if !(seq <= Some(next_seq)) {
                return Err(invalid(&format!(
                    "out of order: {:?} instructions must precede {:?} instructions",
                    next_seq, seq
                )));
            }
            seq = Some(next_seq);

            if attr_set != Default::default() {
                return Err(invalid("unused decorations / line debuginfo"));
            }
        }

        if !has_memory_model {
            return Err(invalid("missing OpMemoryModel"));
        }

        if !pending_attr_sets.is_empty() {
            let ids = pending_attr_sets.keys().collect::<BTreeSet<_>>();
            return Err(invalid(&format!("decorated IDs never defined: {:?}", ids)));
        }

        if current_func.is_some() {
            return Err(invalid("OpFunction without matching OpFunctionEnd"));
        }

        Ok(module)
    }
}
