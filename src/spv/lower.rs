//! SPIR-V to SPIR-T lowering.

use crate::spv::{self, spec};
// FIXME(eddyb) import more to avoid `crate::` everywhere.
use crate::{
    Const, ConstCtor, ConstCtorArg, ConstDef, Context, InternedStr, Module, Type, TypeCtor,
    TypeCtorArg, TypeDef,
};
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use std::collections::{BTreeMap, BTreeSet};
use std::num::NonZeroU32;
use std::path::Path;
use std::rc::Rc;
use std::{io, iter, mem};

/// SPIR-T definition of a SPIR-V ID.
enum IdDef {
    Type(Type),
    Const(Const),

    UnknownGlobal(spec::Opcode),

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

// FIXME(eddyb) provide more information about any normalization that happened:
// * stats about deduplication that occured through interning
// * sets of unused global vars and functions (and types+consts only they use)
impl Module {
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

            // FIXME(eddyb) maybe use this somehow? (e.g. check IDs against it)
            let _ = id_bound;

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

            TypeConstOrGlobalVar,
            Function,
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

            let invalid = |msg: &str| invalid(&format!("in {}: {}", opcode.name(), msg));

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
                    file_path: crate::OrdAssertEq(file_path),
                    line,
                    col,
                });
            }

            let mut attr_set = cx.intern(attr_set);

            // FIXME(eddyb) move this kind of lookup into methods on some sort
            // of "lowering context" type.
            let result_type = inst
                .result_type_id
                .map(|type_id| match id_defs.get(&type_id) {
                    Some(&IdDef::Type(ty)) => Ok(ty),
                    Some(_) => Err(invalid(&format!("result type %{} not an OpType*", type_id))),
                    None => Err(invalid(&format!("result type %{} not defined", type_id))),
                })
                .transpose()?;

            let inst_category = spv_spec.instructions[opcode].category;

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
            } else if opcode == wk.OpTypeForwardPointer {
                assert!(inst.result_type_id.is_none() && inst.result_id.is_none());
                let (id, sc) = match inst.operands[..] {
                    [spv::Operand::Id(kind, id), spv::Operand::Imm(sc)] => {
                        assert!(kind == wk.IdRef);
                        (id, sc)
                    }
                    _ => unreachable!(),
                };

                // HACK(eddyb) this is not a proper implementation - one would
                // require fixpoint (aka "μ" aka "mu") types - but for now this
                // serves as a first approximation for a "deferred error".
                let ty = cx.intern(TypeDef {
                    ctor: TypeCtor::SpvInst(opcode),
                    ctor_args: [TypeCtorArg::SpvImm(sc)].into_iter().collect(),
                    attrs: mem::take(&mut attr_set),
                });
                id_defs.insert(id, IdDef::Type(ty));

                Seq::TypeConstOrGlobalVar
            } else if inst_category == spec::InstructionCategory::Type {
                assert!(inst.result_type_id.is_none());
                let id = inst.result_id.unwrap();
                let type_ctor_args = inst
                    .operands
                    .iter()
                    .map(|operand| match *operand {
                        spv::Operand::Id(_, id) => match id_defs.get(&id) {
                            // FIXME(eddyb) deduplicate these descriptions.
                            Some(&IdDef::Type(ty)) => Ok(TypeCtorArg::Type(ty)),
                            Some(&IdDef::Const(ct)) => Ok(TypeCtorArg::Const(ct)),
                            Some(&IdDef::UnknownGlobal(opcode)) => {
                                Err(format!("`{}`", opcode.name()))
                            }
                            Some(&IdDef::SpvExtInstImport(name)) => {
                                Err(format!("`OpExtInstImport {:?}`", &cx[name]))
                            }
                            Some(&IdDef::SpvDebugString(s)) => {
                                Err(format!("`OpString {:?}`", &cx[s]))
                            }
                            None => Err(format!("a forward reference to %{}", id)),
                        },
                        spv::Operand::Imm(imm) => Ok(TypeCtorArg::SpvImm(imm)),
                    })
                    .map(|result| {
                        result.map_err(|descr| {
                            invalid(&format!("unsupported use of {} in a type", descr))
                        })
                    })
                    .collect::<Result<_, _>>()?;

                let ty = cx.intern(TypeDef {
                    ctor: TypeCtor::SpvInst(opcode),
                    ctor_args: type_ctor_args,
                    attrs: mem::take(&mut attr_set),
                });
                id_defs.insert(id, IdDef::Type(ty));

                Seq::TypeConstOrGlobalVar
            } else if inst_category == spec::InstructionCategory::Const || opcode == wk.OpUndef {
                let id = inst.result_id.unwrap();
                let const_ctor_args = inst
                    .operands
                    .iter()
                    .map(|operand| match *operand {
                        spv::Operand::Id(_, id) => match id_defs.get(&id) {
                            // FIXME(eddyb) deduplicate these descriptions.
                            Some(&IdDef::Type(_)) => Err("a type".into()),
                            Some(&IdDef::Const(ct)) => Ok(ConstCtorArg::Const(ct)),
                            Some(&IdDef::UnknownGlobal(opcode)) => {
                                if opcode == wk.OpVariable {
                                    Ok(ConstCtorArg::SpvUntrackedGlobalVarId(id))
                                } else {
                                    Err(format!("`{}`", opcode.name()))
                                }
                            }
                            Some(&IdDef::SpvExtInstImport(name)) => {
                                Err(format!("`OpExtInstImport {:?}`", &cx[name]))
                            }
                            Some(&IdDef::SpvDebugString(s)) => {
                                Err(format!("`OpString {:?}`", &cx[s]))
                            }
                            None => Err(format!("a forward reference to %{}", id)),
                        },
                        spv::Operand::Imm(imm) => Ok(ConstCtorArg::SpvImm(imm)),
                    })
                    .map(|result| {
                        result.map_err(|descr| {
                            invalid(&format!("unsupported use of {} in a constant", descr))
                        })
                    })
                    .collect::<Result<_, _>>()?;

                let ct = cx.intern(ConstDef {
                    ty: result_type.unwrap(),
                    ctor: ConstCtor::SpvInst(opcode),
                    ctor_args: const_ctor_args,
                    attrs: mem::take(&mut attr_set),
                });
                id_defs.insert(id, IdDef::Const(ct));

                if opcode == wk.OpUndef {
                    // `OpUndef` can appear either among constants, or in a
                    // function, so at most advance `seq` to globals.
                    seq.max(Some(Seq::TypeConstOrGlobalVar)).unwrap()
                } else {
                    Seq::TypeConstOrGlobalVar
                }
            } else if opcode == wk.OpFunction {
                if current_func.is_some() {
                    return Err(invalid("nested OpFunction while still in a function"));
                }

                let func_id = inst.result_id.unwrap();
                // FIXME(eddyb) hide this from SPIR-T, it's the function return
                // type, *not* the function type, which is in `func_type`.
                let func_ret_type = result_type.unwrap();

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

                // FIXME(eddyb) move this kind of lookup into methods on some sort
                // of "lowering context" type.
                let func_type = match id_defs.get(&func_type_id) {
                    Some(&IdDef::Type(ty)) => ty,
                    Some(_) => {
                        return Err(invalid(&format!(
                            "function type %{} not an OpType*",
                            func_type_id
                        )));
                    }
                    None => {
                        return Err(invalid(&format!(
                            "function type %{} not defined",
                            func_type_id
                        )));
                    }
                };

                // FIXME(eddyb) pull out this information from the first entry
                // in the `insts` field, into new fields of `Func`.
                let func_inst = crate::Misc {
                    kind: crate::MiscKind::SpvInst(opcode),
                    output: Some(crate::MiscOutput::SpvResult {
                        result_type: Some(func_ret_type),
                        result_id: func_id,
                    }),
                    inputs: [
                        crate::MiscInput::SpvImm(spv::Imm::Short(wk.FunctionControl, func_ctrl)),
                        crate::MiscInput::Type(func_type),
                    ]
                    .into_iter()
                    .collect(),
                    attrs: mem::take(&mut attr_set),
                };

                current_func = Some(crate::Func {
                    insts: vec![func_inst],
                });

                Seq::Function
            } else if opcode == wk.OpFunctionEnd {
                assert!(inst.result_type_id.is_none() && inst.result_id.is_none());
                assert!(inst.operands.is_empty());

                let mut func = current_func
                    .take()
                    .ok_or_else(|| invalid("nested OpFunction while still in a function"))?;

                // FIXME(eddyb) don't keep this instruction explicitly.
                func.insts.push(crate::Misc {
                    kind: crate::MiscKind::SpvInst(opcode),
                    output: None,
                    inputs: [].into_iter().collect(),
                    attrs: crate::AttrSet::default(),
                });

                module.funcs.push(func);

                Seq::Function
            } else {
                let misc = crate::Misc {
                    kind: crate::MiscKind::SpvInst(opcode),
                    output: inst
                        .result_id
                        .map(|result_id| crate::MiscOutput::SpvResult {
                            result_type,
                            result_id,
                        }),
                    inputs: inst
                        .operands
                        .iter()
                        .map(|operand| {
                            Ok(match *operand {
                                spv::Operand::Imm(imm) => crate::MiscInput::SpvImm(imm),
                                spv::Operand::Id(_, id) => match id_defs.get(&id) {
                                    Some(&IdDef::Type(ty)) => crate::MiscInput::Type(ty),
                                    Some(&IdDef::Const(ct)) => crate::MiscInput::Const(ct),
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
                                    Some(IdDef::UnknownGlobal(_)) | None => {
                                        crate::MiscInput::SpvUntrackedId(id)
                                    }
                                },
                            })
                        })
                        .collect::<Result<_, _>>()?,
                    attrs: mem::take(&mut attr_set),
                };

                match &mut current_func {
                    Some(func) => {
                        assert_eq!(seq, Some(Seq::Function));
                        func.insts.push(misc);
                    }
                    None => {
                        if let Some(id) = inst.result_id {
                            id_defs.insert(id, IdDef::UnknownGlobal(opcode));
                        }
                        module.globals.push(crate::Global::Misc(misc));
                    }
                }

                // Where `OpVariable` belongs depends on its `StorageClass`
                // operand is `Function` (function-local) or not (global).
                if opcode == wk.OpVariable && inst.operands[0] != storage_class_function_operand {
                    Seq::TypeConstOrGlobalVar
                } else {
                    Seq::Function
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
