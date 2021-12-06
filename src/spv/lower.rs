//! SPIR-V to SPIR-T lowering.

use crate::spv::{self, spec};
// FIXME(eddyb) import more to avoid `crate::` everywhere.
use crate::{
    print, AddrSpace, Attr, AttrSet, Block, Const, ConstCtor, ConstCtorArg, ConstDef, Context,
    ControlInst, ControlInstInput, ControlInstKind, DataInstDef, DataInstInput, DataInstKind,
    DeclDef, ExportKey, Exportee, Func, FuncDecl, FuncDefBody, FuncParam, GlobalVarDecl,
    GlobalVarDefBody, Import, InternedStr, Module, Type, TypeCtor, TypeCtorArg, TypeDef, Value,
};
use indexmap::IndexMap;
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

    Func(Func),

    SpvExtInstImport(InternedStr),
    SpvDebugString(InternedStr),
}

impl IdDef {
    fn descr(&self, cx: &Context) -> String {
        match *self {
            // FIXME(eddyb) print these with some kind of "maximum depth",
            // instead of just describing the kind of definition.
            IdDef::Type(_) => "a type".into(),
            IdDef::Const(_) => "a constant".into(),

            IdDef::Func(_) => "a function".into(),

            IdDef::SpvExtInstImport(name) => {
                format!("`OpExtInstImport {:?}`", &cx[name])
            }
            IdDef::SpvDebugString(s) => format!("`OpString {:?}`", &cx[s]),
        }
    }
}

/// Deferred export, needed because the IDs are initially forward refs.
enum Export {
    Linkage {
        name: InternedStr,
        target_id: spv::Id,
    },
    EntryPoint {
        func_id: spv::Id,
        params: SmallVec<[spv::Imm; 2]>,
        interface_ids: SmallVec<[spv::Id; 4]>,
    },
}

/// Deferred `FuncDefBody`, needed because some IDs are initially forward refs.
struct FuncBody {
    func_id: spv::Id,
    func: Func,
    insts: Vec<IntraFuncInst>,
}

struct IntraFuncInst {
    // Instruction aspects that can be pre-lowered:
    attrs: AttrSet,
    result_type: Option<Type>,

    // Instruction aspects that cannot be lowered initially (due to forward refs):
    opcode: spec::Opcode,
    result_id: Option<spv::Id>,

    // FIXME(eddyb) change the inline size of this to fit most instructions.
    operands: SmallVec<[spv::Operand; 2]>,
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
        let mut pending_attrs = FxHashMap::<spv::Id, crate::AttrSetDef>::default();
        let mut pending_imports = FxHashMap::<spv::Id, Import>::default();
        let mut pending_exports = vec![];
        let mut current_debug_line = None;
        let mut current_block_id = None; // HACK(eddyb) for `current_debug_line` resets.
        let mut id_defs = FxHashMap::default();
        let mut pending_func_bodies = vec![];
        let mut current_func_body = None;

        let mut spv_insts = parser.peekable();
        while let Some(mut inst) = spv_insts.next().transpose()? {
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

            let mut attrs = inst
                .result_id
                .and_then(|id| pending_attrs.remove(&id))
                .unwrap_or_default();

            if let Some((file_path, line, col)) = current_debug_line {
                // FIXME(eddyb) use `get_or_insert_default` once that's stabilized.
                attrs.attrs.insert(Attr::SpvDebugLine {
                    file_path: crate::OrdAssertEq(file_path),
                    line,
                    col,
                });
            }

            // Take certain bitflags operands out of the instruction and rewrite
            // them into attributes instead.
            inst.operands.retain(|operand| match *operand {
                spv::Operand::Imm(imm @ spv::Imm::Short(kind, word))
                    if kind == wk.FunctionControl =>
                {
                    if word != 0 {
                        attrs.attrs.insert(Attr::SpvBitflagsOperand(imm));
                    }
                    false
                }
                _ => true,
            });

            let mut attrs = cx.intern(attrs);

            // FIXME(eddyb) move this kind of lookup into methods on some sort
            // of "lowering context" type.
            let result_type = inst
                .result_type_id
                .map(|type_id| match id_defs.get(&type_id) {
                    Some(&IdDef::Type(ty)) => Ok(ty),
                    Some(id_def) => Err(invalid(&format!(
                        "result type %{} should be a type, not a {}",
                        type_id,
                        id_def.descr(&cx)
                    ))),
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

                pending_exports.push(Export::EntryPoint {
                    func_id: target_id,
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

                match inst.operands[1..] {
                    // Special-case `OpDecorate LinkageAttributes ... Import|Export`.
                    [
                        spv::Operand::Imm(decoration @ spv::Imm::Short(..)),
                        ref name @ ..,
                        spv::Operand::Imm(spv::Imm::Short(lt_kind, linkage_type)),
                    ] if opcode == wk.OpDecorate
                        && decoration == spv::Imm::Short(wk.Decoration, wk.LinkageAttributes)
                        && lt_kind == wk.LinkageType
                        && [wk.Import, wk.Export].contains(&linkage_type) =>
                    {
                        let name = spv::extract_literal_string(name)
                            .map_err(|e| invalid(&format!("{} in {:?}", e, e.as_bytes())))?;
                        let name = cx.intern(name);

                        if linkage_type == wk.Import {
                            pending_imports.insert(target_id, Import::LinkName(name));
                        } else {
                            pending_exports.push(Export::Linkage { name, target_id });
                        }
                    }

                    _ => {
                        let params = inst.operands[1..]
                            .iter()
                            .map(|operand| match *operand {
                                spv::Operand::Imm(imm) => Ok(imm),
                                spv::Operand::Id(..) => {
                                    Err(invalid("unsupported decoration with ID"))
                                }
                            })
                            .collect::<Result<_, _>>()?;
                        pending_attrs
                            .entry(target_id)
                            .or_default()
                            .attrs
                            .insert(Attr::SpvAnnotation { opcode, params });
                    }
                };

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
                    attrs: mem::take(&mut attrs),
                    ctor: TypeCtor::SpvInst(opcode),
                    ctor_args: [TypeCtorArg::SpvImm(sc)].into_iter().collect(),
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
                            Some(&IdDef::Type(ty)) => Ok(TypeCtorArg::Type(ty)),
                            Some(&IdDef::Const(ct)) => Ok(TypeCtorArg::Const(ct)),
                            Some(id_def) => Err(id_def.descr(&cx)),
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
                    attrs: mem::take(&mut attrs),
                    ctor: TypeCtor::SpvInst(opcode),
                    ctor_args: type_ctor_args,
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
                            Some(&IdDef::Const(ct)) => Ok(ConstCtorArg::Const(ct)),
                            Some(id_def) => Err(id_def.descr(&cx)),
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
                    attrs: mem::take(&mut attrs),
                    ty: result_type.unwrap(),
                    ctor: ConstCtor::SpvInst(opcode),
                    ctor_args: const_ctor_args,
                });
                id_defs.insert(id, IdDef::Const(ct));

                if opcode == wk.OpUndef {
                    // `OpUndef` can appear either among constants, or in a
                    // function, so at most advance `seq` to globals.
                    seq.max(Some(Seq::TypeConstOrGlobalVar)).unwrap()
                } else {
                    Seq::TypeConstOrGlobalVar
                }
            } else if opcode == wk.OpVariable && current_func_body.is_none() {
                let global_var_id = inst.result_id.unwrap();
                let type_of_ptr_to_global_var = result_type.unwrap();

                if inst.operands[0] == storage_class_function_operand {
                    return Err(invalid("`Function` storage class outside function"));
                }

                let storage_class = match inst.operands[0] {
                    spv::Operand::Imm(spv::Imm::Short(kind, storage_class)) => {
                        assert!(kind == wk.StorageClass);
                        storage_class
                    }
                    _ => unreachable!(),
                };
                let initializer = match inst.operands[1..] {
                    [spv::Operand::Id(kind, initializer)] => {
                        assert!(kind == wk.IdRef);
                        Some(initializer)
                    }
                    [] => None,
                    _ => unreachable!(),
                };

                let initializer = initializer
                    .map(|id| match id_defs.get(&id) {
                        Some(&IdDef::Const(ct)) => Ok(ct),
                        Some(id_def) => Err(id_def.descr(&cx)),
                        None => Err(format!("a forward reference to %{}", id)),
                    })
                    .transpose()
                    .map_err(|descr| {
                        invalid(&format!(
                            "unsupported use of {} as the initializer of a global variable",
                            descr
                        ))
                    })?;

                let def = match pending_imports.remove(&global_var_id) {
                    Some(import @ Import::LinkName(name)) => {
                        if initializer.is_some() {
                            return Err(invalid(&format!(
                                "global variable with initializer decorated as `Import` of {:?}",
                                &cx[name]
                            )));
                        }
                        DeclDef::Imported(import)
                    }
                    None => DeclDef::Present(GlobalVarDefBody { initializer }),
                };

                let global_var = module.global_vars.insert(
                    &cx,
                    GlobalVarDecl {
                        attrs: mem::take(&mut attrs),
                        type_of_ptr_to: type_of_ptr_to_global_var,
                        addr_space: AddrSpace::SpvStorageClass(storage_class),
                        def,
                    },
                );
                let ptr_to_global_var = cx.intern(ConstDef {
                    attrs: AttrSet::default(),
                    ty: type_of_ptr_to_global_var,
                    ctor: ConstCtor::PtrToGlobalVar(global_var),
                    ctor_args: [].into_iter().collect(),
                });
                id_defs.insert(global_var_id, IdDef::Const(ptr_to_global_var));

                Seq::TypeConstOrGlobalVar
            } else if opcode == wk.OpFunction {
                if current_func_body.is_some() {
                    return Err(invalid("nested OpFunction while still in a function"));
                }

                let func_id = inst.result_id.unwrap();
                // FIXME(eddyb) hide this from SPIR-T, it's the function return
                // type, *not* the function type, which is in `func_type`.
                let func_ret_type = result_type.unwrap();

                let func_type_id = match inst.operands[..] {
                    // NOTE(eddyb) the `FunctionControl` operand is already gone,
                    // having been converted into an attribute above.
                    [spv::Operand::Id(kind, func_type_id)] => {
                        assert!(kind == wk.IdRef);
                        func_type_id
                    }
                    _ => unreachable!(),
                };

                let (func_type_ret_type, func_type_param_types) =
                    match id_defs.get(&func_type_id) {
                        Some(&IdDef::Type(ty)) => {
                            let ty_def = &cx[ty];
                            if ty_def.ctor == TypeCtor::SpvInst(wk.OpTypeFunction) {
                                let mut types = ty_def.ctor_args.iter().map(|&arg| match arg {
                                    TypeCtorArg::Type(ty) => ty,
                                    _ => unreachable!(),
                                });
                                Some((types.next().unwrap(), types))
                            } else {
                                None
                            }
                        }
                        _ => None,
                    }
                    .ok_or_else(|| {
                        invalid(&format!(
                            "function type %{} not an `OpTypeFunction`",
                            func_type_id
                        ))
                    })?;

                if func_ret_type != func_type_ret_type {
                    // FIXME(remove) embed IDs in errors by moving them to the
                    // `let invalid = |...| ...;` closure that wraps insts.
                    return Err(invalid(&format!(
                        "in %{}, return type differs between `OpFunction` (expected) \
                         and `OpTypeFunction` (found):\n\n{}",
                        func_id,
                        print::Plan::for_root_outside_module(
                            &cx,
                            &print::ExpectedVsFound {
                                expected: func_ret_type,
                                found: func_type_ret_type,
                            }
                        )
                    )));
                }

                let def = match pending_imports.remove(&func_id) {
                    Some(import) => DeclDef::Imported(import),
                    None => DeclDef::Present(FuncDefBody {
                        data_insts: Default::default(),
                        blocks: vec![],
                    }),
                };

                let func = module.funcs.insert(
                    &cx,
                    FuncDecl {
                        attrs: mem::take(&mut attrs),
                        ret_type: func_ret_type,
                        params: func_type_param_types
                            .map(|ty| FuncParam {
                                attrs: AttrSet::default(),
                                ty,
                            })
                            .collect(),
                        def,
                    },
                );
                id_defs.insert(func_id, IdDef::Func(func));

                current_func_body = Some(FuncBody {
                    func_id,
                    func,
                    insts: vec![],
                });

                Seq::Function
            } else if opcode == wk.OpFunctionEnd {
                assert!(inst.result_type_id.is_none() && inst.result_id.is_none());
                assert!(inst.operands.is_empty());

                let func_body = current_func_body
                    .take()
                    .ok_or_else(|| invalid("nested OpFunction while still in a function"))?;

                pending_func_bodies.push(func_body);

                Seq::Function
            } else {
                let func_body = current_func_body
                    .as_mut()
                    .ok_or_else(|| invalid("expected only inside a function"))?;
                assert_eq!(seq, Some(Seq::Function));

                func_body.insts.push(IntraFuncInst {
                    attrs: mem::take(&mut attrs),
                    result_type,

                    opcode,
                    result_id: inst.result_id,
                    operands: inst.operands,
                });

                Seq::Function
            };
            if !(seq <= Some(next_seq)) {
                return Err(invalid(&format!(
                    "out of order: {:?} instructions must precede {:?} instructions",
                    next_seq, seq
                )));
            }
            seq = Some(next_seq);

            if attrs != Default::default() {
                return Err(invalid("unused decorations / line debuginfo"));
            }
        }

        if !has_memory_model {
            return Err(invalid("missing OpMemoryModel"));
        }

        if !pending_attrs.is_empty() {
            let ids = pending_attrs.keys().collect::<BTreeSet<_>>();
            return Err(invalid(&format!("decorated IDs never defined: {:?}", ids)));
        }

        if current_func_body.is_some() {
            return Err(invalid("OpFunction without matching OpFunctionEnd"));
        }

        // Process function bodies, having seen the whole module.
        for func_body in pending_func_bodies {
            let FuncBody {
                func_id,
                func,
                insts: raw_insts,
            } = func_body;

            let func_decl = &mut module.funcs[func];

            #[derive(Copy, Clone)]
            enum LocalIdDef {
                Value(Value),
                BlockLabel { idx: u32 },
            }

            // Index IDs declared within the function, first.
            let mut local_id_defs = IndexMap::new();
            let mut has_blocks = false;
            {
                let mut next_param_idx = 0u32;
                let mut next_block_idx = 0u32;
                for raw_inst in &raw_insts {
                    let IntraFuncInst {
                        opcode, result_id, ..
                    } = *raw_inst;

                    if let Some(id) = result_id {
                        let local_id_def = if opcode == wk.OpFunctionParameter {
                            let idx = next_param_idx;
                            next_param_idx = idx.checked_add(1).unwrap();
                            LocalIdDef::Value(Value::FuncParam { idx })
                        } else if opcode == wk.OpLabel {
                            has_blocks = true;

                            let idx = next_block_idx;
                            next_block_idx = idx.checked_add(1).unwrap();
                            LocalIdDef::BlockLabel { idx }
                        } else {
                            has_blocks = true;

                            // HACK(eddyb) can't generate the `DataInst` unique
                            // index without inserting (a dummy) first.
                            let func_def_body = match &mut func_decl.def {
                                // Error will be emitted later, below.
                                DeclDef::Imported(_) => continue,
                                DeclDef::Present(def) => def,
                            };
                            let inst = func_def_body.data_insts.insert(
                                &cx,
                                DataInstDef {
                                    attrs: AttrSet::default(),
                                    kind: DataInstKind::SpvInst(wk.OpNop),
                                    output_type: None,
                                    inputs: [].into_iter().collect(),
                                },
                            );
                            LocalIdDef::Value(Value::DataInstOutput(inst))
                        };
                        local_id_defs.insert(id, local_id_def);
                    }
                }
            }

            let mut params = vec![];

            let mut func_def_body = if has_blocks {
                match &mut func_decl.def {
                    DeclDef::Imported(Import::LinkName(name)) => {
                        return Err(invalid(&format!(
                            "non-empty function %{} decorated as `Import` of {:?}",
                            func_id, &cx[*name]
                        )));
                    }
                    DeclDef::Present(def) => {
                        assert!(def.blocks.is_empty());
                        Some(def)
                    }
                }
            } else {
                None
            };

            for (raw_inst_idx, raw_inst) in raw_insts.iter().enumerate() {
                let lookahead_raw_inst = |dist| {
                    raw_inst_idx
                        .checked_add(dist)
                        .and_then(|i| raw_insts.get(i))
                };

                let IntraFuncInst {
                    attrs,
                    result_type,
                    opcode,
                    result_id,
                    ref operands,
                } = *raw_inst;

                let invalid = |msg: &str| invalid(&format!("in {}: {}", opcode.name(), msg));

                // FIXME(eddyb) find a more compact name and/or make this a method.
                // FIXME(eddyb) this returns `LocalIdDef` even for global values.
                let lookup_global_or_local_id_for_data_or_control_inst_input =
                    |id| match id_defs.get(&id) {
                        Some(&IdDef::Const(ct)) => Ok(LocalIdDef::Value(Value::Const(ct))),
                        Some(id_def @ IdDef::Type(_)) => Err(invalid(&format!(
                            "unsupported use of {} as an operand for \
                             an instruction in a function",
                            id_def.descr(&cx),
                        ))),
                        Some(id_def @ IdDef::Func(_)) => Err(invalid(&format!(
                            "unsupported use of {} outside `OpFunctionCall`",
                            id_def.descr(&cx),
                        ))),
                        Some(id_def @ IdDef::SpvDebugString(_)) => Err(invalid(&format!(
                            "unsupported use of {} outside `OpSource` or `OpLine`",
                            id_def.descr(&cx),
                        ))),
                        Some(id_def @ IdDef::SpvExtInstImport(_)) => Err(invalid(&format!(
                            "unsupported use of {} outside `OpExtInst`",
                            id_def.descr(&cx),
                        ))),
                        None => local_id_defs
                            .get(&id)
                            .copied()
                            .ok_or_else(|| invalid(&format!("undefined ID %{}", id,))),
                    };

                if opcode == wk.OpFunctionParameter {
                    if let Some(func_def_body) = &func_def_body {
                        if !func_def_body.blocks.is_empty() {
                            return Err(invalid(
                                "out of order: `OpFunctionParameter`s should come \
                                 before the function's blocks",
                            ));
                        }
                    }

                    assert!(operands.is_empty());
                    params.push(FuncParam {
                        attrs,
                        ty: result_type.unwrap(),
                    });
                    continue;
                }
                let func_def_body = func_def_body.as_deref_mut().unwrap();

                let is_last_in_block = lookahead_raw_inst(1)
                    .map_or(true, |next_raw_inst| next_raw_inst.opcode == wk.OpLabel);

                if opcode == wk.OpLabel {
                    if is_last_in_block {
                        return Err(invalid("block lacks terminator instruction"));
                    }

                    // HACK(eddyb) can't push the `Block` without a dummy terminator.
                    func_def_body.blocks.push(Block {
                        insts: vec![],
                        terminator: ControlInst {
                            attrs: AttrSet::default(),
                            kind: ControlInstKind::SpvInst(wk.OpNop),
                            inputs: [].into_iter().collect(),
                        },
                    });
                    continue;
                }
                let current_block = func_def_body.blocks.last_mut().ok_or_else(|| {
                    invalid("out of order: not expected before the function's blocks")
                })?;

                if is_last_in_block {
                    if opcode.def().category != spec::InstructionCategory::ControlFlow {
                        return Err(invalid(
                            "non-control-flow instruction cannot be used \
                             as the terminator instruction of a block",
                        ));
                    }

                    current_block.terminator = ControlInst {
                        attrs,
                        kind: ControlInstKind::SpvInst(opcode),
                        inputs: operands
                            .iter()
                            .map(|operand| match *operand {
                                spv::Operand::Imm(imm) => Ok(ControlInstInput::SpvImm(imm)),
                                spv::Operand::Id(_, id) => Ok(
                                    match lookup_global_or_local_id_for_data_or_control_inst_input(
                                        id,
                                    )? {
                                        LocalIdDef::Value(v) => ControlInstInput::Value(v),
                                        LocalIdDef::BlockLabel { idx } => {
                                            ControlInstInput::TargetBlock { idx }
                                        }
                                    },
                                ),
                            })
                            .collect::<io::Result<_>>()?,
                    };
                } else {
                    let mut operands = &operands[..];
                    let kind = if opcode == wk.OpFunctionCall {
                        let callee_id = match operands[0] {
                            spv::Operand::Id(kind, id) => {
                                assert!(kind == wk.IdRef);
                                id
                            }
                            _ => unreachable!(),
                        };
                        let maybe_callee = id_defs
                            .get(&callee_id)
                            .map(|id_def| match *id_def {
                                IdDef::Func(func) => Ok(func),
                                _ => Err(id_def.descr(&cx)),
                            })
                            .transpose()
                            .map_err(|descr| {
                                invalid(&format!(
                                    "unsupported use of {} as the `OpFunctionCall` callee",
                                    descr
                                ))
                            })?;

                        match maybe_callee {
                            Some(callee) => {
                                operands = &operands[1..];
                                DataInstKind::FuncCall(callee)
                            }

                            // HACK(eddyb) this should be an error, but it shows
                            // up in Rust-GPU output (likely a zombie?).
                            None => DataInstKind::SpvInst(opcode),
                        }
                    } else if opcode == wk.OpExtInst {
                        let (ext_set_id, inst) = match operands[..2] {
                            [
                                spv::Operand::Id(es_kind, ext_set_id),
                                spv::Operand::Imm(spv::Imm::Short(i_kind, inst)),
                            ] => {
                                assert!(es_kind == wk.IdRef && i_kind == wk.LiteralExtInstInteger);
                                (ext_set_id, inst)
                            }
                            _ => unreachable!(),
                        };
                        operands = &operands[2..];

                        let ext_set = match id_defs.get(&ext_set_id) {
                            Some(&IdDef::SpvExtInstImport(name)) => Ok(name),
                            Some(id_def) => Err(id_def.descr(&cx)),
                            None => Err(format!("unknown ID %{}", ext_set_id)),
                        }
                        .map_err(|descr| {
                            invalid(&format!(
                                "unsupported use of {} as the `OpExtInst` \
                                 extended instruction set ID",
                                descr
                            ))
                        })?;

                        DataInstKind::SpvExtInst { ext_set, inst }
                    } else {
                        DataInstKind::SpvInst(opcode)
                    };

                    let data_inst_def = DataInstDef {
                        attrs,
                        kind,
                        output_type: result_id
                            .map(|_| {
                                result_type.ok_or_else(|| {
                                    invalid(
                                        "expected value-producing instruction, with a result type",
                                    )
                                })
                            })
                            .transpose()?,
                        inputs: operands
                            .iter()
                            .map(|operand| match *operand {
                                spv::Operand::Imm(imm) => Ok(DataInstInput::SpvImm(imm)),
                                spv::Operand::Id(_, id) => Ok(
                                    match lookup_global_or_local_id_for_data_or_control_inst_input(
                                        id,
                                    )? {
                                        LocalIdDef::Value(v) => DataInstInput::Value(v),
                                        LocalIdDef::BlockLabel { idx } => {
                                            DataInstInput::Block { idx }
                                        }
                                    },
                                ),
                            })
                            .collect::<io::Result<_>>()?,
                    };
                    let inst = match result_id {
                        Some(id) => match local_id_defs[&id] {
                            LocalIdDef::Value(Value::DataInstOutput(inst)) => {
                                // A dummy was inserted earlier, to be able to
                                // have an entry in `local_id_defs`.
                                func_def_body.data_insts[inst] = data_inst_def;

                                inst
                            }
                            _ => unreachable!(),
                        },
                        None => func_def_body.data_insts.insert(&cx, data_inst_def),
                    };
                    current_block.insts.push(inst);
                }
            }

            // FIXME(eddyb) all functions should have the appropriate number of
            // `OpFunctionParameter`, even imports.
            if !params.is_empty() {
                if func_decl.params.len() != params.len() {
                    // FIXME(remove) embed IDs in errors by moving them to the
                    // `let invalid = |...| ...;` closure that wraps insts.
                    return Err(invalid(&format!(
                        "in %{}, param count differs between `OpTypeFunction` ({}) \
                         and `OpFunctionParameter`s ({})",
                        func_id,
                        func_decl.params.len(),
                        params.len(),
                    )));
                }

                for (i, (func_type_param, param)) in
                    func_decl.params.iter_mut().zip(params).enumerate()
                {
                    if func_type_param.ty != param.ty {
                        // FIXME(remove) embed IDs in errors by moving them to the
                        // `let invalid = |...| ...;` closure that wraps insts.
                        return Err(invalid(&format!(
                            "in %{}, param {}'s type differs between \
                             `OpTypeFunction` (expected) and \
                             `OpFunctionParameter` (found):\n\n{}",
                            func_id,
                            i,
                            print::Plan::for_root_outside_module(
                                &cx,
                                &print::ExpectedVsFound {
                                    expected: func_type_param.ty,
                                    found: param.ty,
                                }
                            )
                        )));
                    }
                }
            }
        }

        assert!(module.exports.is_empty());
        module.exports = pending_exports
            .into_iter()
            .map(|export| match export {
                Export::Linkage { name, target_id } => {
                    let exportee = match id_defs.get(&target_id) {
                        Some(id_def @ &IdDef::Const(ct)) => match cx[ct].ctor {
                            ConstCtor::PtrToGlobalVar(gv) => Ok(Exportee::GlobalVar(gv)),
                            _ => Err(id_def.descr(&cx)),
                        },
                        Some(&IdDef::Func(func)) => Ok(Exportee::Func(func)),
                        Some(id_def) => Err(id_def.descr(&cx)),
                        None => Err(format!("unknown ID %{}", target_id)),
                    }
                    .map_err(|descr| {
                        invalid(&format!(
                            "unsupported use of {} as the `LinkageAttributes` target",
                            descr
                        ))
                    })?;

                    Ok((ExportKey::LinkName(name), exportee))
                }

                Export::EntryPoint {
                    func_id,
                    params,
                    interface_ids,
                } => {
                    let func = match id_defs.get(&func_id) {
                        Some(&IdDef::Func(func)) => Ok(func),
                        Some(id_def) => Err(id_def.descr(&cx)),
                        None => Err(format!("unknown ID %{}", func_id)),
                    }
                    .map_err(|descr| {
                        invalid(&format!(
                            "unsupported use of {} as the `OpEntryPoint` target",
                            descr
                        ))
                    })?;
                    let interface_global_vars = interface_ids
                        .into_iter()
                        .map(|id| match id_defs.get(&id) {
                            Some(id_def @ &IdDef::Const(ct)) => match cx[ct].ctor {
                                ConstCtor::PtrToGlobalVar(gv) => Ok(gv),
                                _ => Err(id_def.descr(&cx)),
                            },
                            Some(id_def) => Err(id_def.descr(&cx)),
                            None => Err(format!("unknown ID %{}", id)),
                        })
                        .map(|result| {
                            result.map_err(|descr| {
                                invalid(&format!(
                                    "unsupported use of {} as an `OpEntryPoint` interface variable",
                                    descr
                                ))
                            })
                        })
                        .collect::<Result<_, _>>()?;
                    Ok((
                        ExportKey::SpvEntryPoint {
                            params,
                            interface_global_vars,
                        },
                        Exportee::Func(func),
                    ))
                }
            })
            .collect::<io::Result<_>>()?;

        Ok(module)
    }
}
