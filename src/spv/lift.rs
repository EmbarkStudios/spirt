//! SPIR-T to SPIR-V lifting.

use crate::spv::{self, spec};
use crate::visit::{InnerVisit, Visitor};
use crate::{
    Attr, AttrSet, Const, ConstCtor, ConstCtorArg, Context, Global, MiscInput, MiscKind,
    MiscOutput, Module, ModuleDebugInfo, ModuleDialect, Type, TypeCtor, TypeCtorArg,
};
use indexmap::{IndexMap, IndexSet};
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

impl spv::ModuleDebugInfo {
    pub fn source_extension_insts(&self) -> impl Iterator<Item = spv::Inst> + '_ {
        let wk = &spec::Spec::get().well_known;
        self.source_extensions.iter().map(move |ext| spv::Inst {
            opcode: wk.OpSourceExtension,
            result_type_id: None,
            result_id: None,
            operands: spv::encode_literal_string(ext).collect(),
        })
    }

    pub fn module_processed_insts(&self) -> impl Iterator<Item = spv::Inst> + '_ {
        let wk = &spec::Spec::get().well_known;
        self.module_processes.iter().map(move |proc| spv::Inst {
            opcode: wk.OpModuleProcessed,
            result_type_id: None,
            result_id: None,
            operands: spv::encode_literal_string(proc).collect(),
        })
    }
}

struct NeedsIdsCollector<'a> {
    cx: &'a Context,

    ext_inst_imports: BTreeSet<&'a str>,
    debug_strings: BTreeSet<&'a str>,

    interned_globals: IndexSet<InternedGlobal>,

    old_outputs: IndexSet<spv::Id>,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
enum InternedGlobal {
    Type(Type),
    Const(Const),
}

impl Visitor<'_> for NeedsIdsCollector<'_> {
    fn visit_attr_set_use(&mut self, attrs: AttrSet) {
        self.visit_attr_set_def(&self.cx[attrs]);
    }
    fn visit_type_use(&mut self, ty: Type) {
        let global = InternedGlobal::Type(ty);
        if self.interned_globals.contains(&global) {
            return;
        }
        self.visit_type_def(&self.cx[ty]);
        self.interned_globals.insert(global);
    }
    fn visit_const_use(&mut self, ct: Const) {
        let global = InternedGlobal::Const(ct);
        if self.interned_globals.contains(&global) {
            return;
        }
        self.visit_const_def(&self.cx[ct]);
        self.interned_globals.insert(global);
    }

    fn visit_spv_module_debug_info(&mut self, debug_info: &spv::ModuleDebugInfo) {
        for sources in debug_info.source_languages.values() {
            // The file operand of `OpSource` has to point to an `OpString`.
            self.debug_strings
                .extend(sources.file_contents.keys().copied().map(|s| &self.cx[s]));
        }
    }
    fn visit_misc_output(&mut self, output: &MiscOutput) {
        match *output {
            MiscOutput::SpvResult { result_id, .. } => {
                self.old_outputs.insert(result_id);
            }
        }
        output.inner_visit_with(self);
    }
    fn visit_misc_input(&mut self, input: &MiscInput) {
        match *input {
            MiscInput::Type(_)
            | MiscInput::Const(_)
            | MiscInput::SpvImm(_)
            | MiscInput::SpvUntrackedId(_) => {}
            MiscInput::SpvExtInstImport(name) => {
                self.ext_inst_imports.insert(&self.cx[name]);
            }
        }
        input.inner_visit_with(self);
    }
    fn visit_attr(&mut self, attr: &Attr) {
        match *attr {
            Attr::SpvEntryPoint { .. } | Attr::SpvAnnotation { .. } => {}
            Attr::SpvDebugLine { file_path, .. } => {
                self.debug_strings.insert(&self.cx[file_path.0]);
            }
        }
    }
}

struct AllocatedIds<'a> {
    ext_inst_imports: BTreeMap<&'a str, spv::Id>,
    debug_strings: BTreeMap<&'a str, spv::Id>,

    interned_globals: IndexMap<InternedGlobal, spv::Id>,

    old_outputs: IndexMap<spv::Id, spv::Id>,
}

impl<'a> NeedsIdsCollector<'a> {
    fn alloc_ids<E>(
        self,
        mut alloc_id: impl FnMut() -> Result<spv::Id, E>,
    ) -> Result<AllocatedIds<'a>, E> {
        let Self {
            cx: _,
            ext_inst_imports,
            debug_strings,
            interned_globals,
            old_outputs,
        } = self;

        Ok(AllocatedIds {
            ext_inst_imports: ext_inst_imports
                .into_iter()
                .map(|name| Ok((name, alloc_id()?)))
                .collect::<Result<_, _>>()?,
            debug_strings: debug_strings
                .into_iter()
                .map(|s| Ok((s, alloc_id()?)))
                .collect::<Result<_, _>>()?,
            interned_globals: interned_globals
                .into_iter()
                .map(|g| Ok((g, alloc_id()?)))
                .collect::<Result<_, _>>()?,
            old_outputs: old_outputs
                .into_iter()
                .map(|old_id| Ok((old_id, alloc_id()?)))
                .collect::<Result<_, _>>()?,
        })
    }
}

impl Module {
    pub fn lift_to_spv_file(&self, path: impl AsRef<Path>) -> io::Result<()> {
        self.lift_to_spv_module_emitter()?.write_to_spv_file(path)
    }

    pub fn lift_to_spv_module_emitter(&self) -> io::Result<spv::write::ModuleEmitter> {
        let spv_spec = spec::Spec::get();
        let wk = &spv_spec.well_known;

        let cx = self.cx();
        let (dialect, debug_info) = match (&self.dialect, &self.debug_info) {
            (ModuleDialect::Spv(dialect), ModuleDebugInfo::Spv(debug_info)) => {
                (dialect, debug_info)
            }

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
        let mut needs_ids_collector = NeedsIdsCollector {
            cx: &cx,
            ext_inst_imports: BTreeSet::new(),
            debug_strings: BTreeSet::new(),
            interned_globals: IndexSet::new(),
            old_outputs: IndexSet::new(),
        };
        needs_ids_collector.visit_module(self);

        // IDs can be allocated once we have the full sets needing them, whether
        // sorted by contents, or ordered by the first occurence in the module.
        let mut id_bound = NonZeroU32::new(1).unwrap();
        let ids = needs_ids_collector.alloc_ids(|| {
            let id = id_bound;

            // FIXME(eddyb) use `id_bound.checked_add(1)` once that's stabilized.
            match id_bound.get().checked_add(1).and_then(NonZeroU32::new) {
                Some(new_bound) => {
                    id_bound = new_bound;
                    Ok(id)
                }
                None => Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "ID bound of SPIR-V module doesn't fit in 32 bits",
                )),
            }
        })?;

        // HACK(eddyb) allow `move` closures below to reference `cx` or `ids`
        // without causing unwanted moves out of them.
        let (cx, ids) = (&*cx, &ids);

        // Set up iterators for the bulk of the module's instructions, to make
        // it easier to generate decorations, `OpName`s, etc. for them.
        // To avoid wastefully recomputing the unneeded parts of `Inst`, or
        // having to allocate all of the `Inst`s ahead of time, the `mk_inst`
        // field of each `InstGen` is a closure that should only be called when
        // the `Inst` is eventually needed, but can be cheaply ignored before.
        struct InstGen<MI: FnOnce() -> spv::Inst> {
            attrs: AttrSet,
            result_id: Option<spv::Id>,
            mk_inst: MI,
        }
        let interned_globals_inst_gens =
            ids.interned_globals
                .iter()
                .map(|(&global, &result_id)| InstGen {
                    attrs: match global {
                        InternedGlobal::Type(ty) => cx[ty].attrs,
                        InternedGlobal::Const(ct) => cx[ct].attrs,
                    },
                    result_id: Some(result_id),
                    mk_inst: move || match global {
                        InternedGlobal::Type(ty) => {
                            let ty_def = &cx[ty];
                            spv::Inst {
                                opcode: match ty_def.ctor {
                                    TypeCtor::SpvInst(opcode) => opcode,
                                },
                                result_type_id: None,
                                result_id: Some(result_id),
                                operands: ty_def
                                    .ctor_args
                                    .iter()
                                    .map(|&arg| match arg {
                                        TypeCtorArg::Type(ty) => spv::Operand::Id(
                                            wk.IdRef,
                                            ids.interned_globals[&InternedGlobal::Type(ty)],
                                        ),
                                        TypeCtorArg::Const(ct) => spv::Operand::Id(
                                            wk.IdRef,
                                            ids.interned_globals[&InternedGlobal::Const(ct)],
                                        ),
                                        TypeCtorArg::SpvImm(imm) => spv::Operand::Imm(imm),
                                    })
                                    .collect(),
                            }
                        }
                        InternedGlobal::Const(ct) => {
                            let ct_def = &cx[ct];
                            spv::Inst {
                                opcode: match ct_def.ctor {
                                    ConstCtor::SpvInst(opcode) => opcode,
                                },
                                result_type_id: Some(
                                    ids.interned_globals[&InternedGlobal::Type(ct_def.ty)],
                                ),
                                result_id: Some(result_id),
                                operands: ct_def
                                    .ctor_args
                                    .iter()
                                    .map(|&arg| match arg {
                                        ConstCtorArg::Const(ct) => spv::Operand::Id(
                                            wk.IdRef,
                                            ids.interned_globals[&InternedGlobal::Const(ct)],
                                        ),
                                        ConstCtorArg::SpvImm(imm) => spv::Operand::Imm(imm),
                                        ConstCtorArg::SpvUntrackedGlobalVarId(old_id) => {
                                            spv::Operand::Id(wk.IdRef, ids.old_outputs[&old_id])
                                        }
                                    })
                                    .collect(),
                            }
                        }
                    },
                });
        let misc_inst_gens = self
            .globals
            .iter()
            .map(|global| match global {
                Global::Misc(misc) => misc,
            })
            .chain(self.funcs.iter().flat_map(|func| &func.insts))
            .map(|misc| {
                let result_id = misc.output.as_ref().map(|old_output| match *old_output {
                    MiscOutput::SpvResult {
                        result_id: old_result_id,
                        ..
                    } => ids.old_outputs[&old_result_id],
                });
                InstGen {
                    attrs: misc.attrs,
                    result_id,
                    mk_inst: move || spv::Inst {
                        opcode: match misc.kind {
                            MiscKind::SpvInst(opcode) => opcode,
                        },
                        result_type_id: misc.output.as_ref().and_then(
                            |old_output| match *old_output {
                                MiscOutput::SpvResult { result_type, .. } => result_type
                                    .map(|ty| ids.interned_globals[&InternedGlobal::Type(ty)]),
                            },
                        ),
                        result_id,
                        operands: misc
                            .inputs
                            .iter()
                            .map(|input| match *input {
                                MiscInput::Type(ty) => spv::Operand::Id(
                                    wk.IdRef,
                                    ids.interned_globals[&InternedGlobal::Type(ty)],
                                ),
                                MiscInput::Const(ct) => spv::Operand::Id(
                                    wk.IdRef,
                                    ids.interned_globals[&InternedGlobal::Const(ct)],
                                ),
                                MiscInput::SpvImm(imm) => spv::Operand::Imm(imm),
                                MiscInput::SpvUntrackedId(old_id) => {
                                    spv::Operand::Id(wk.IdRef, ids.old_outputs[&old_id])
                                }
                                MiscInput::SpvExtInstImport(name) => {
                                    spv::Operand::Id(wk.IdRef, ids.ext_inst_imports[&cx[name]])
                                }
                            })
                            .collect(),
                    },
                }
            });

        let reserved_inst_schema = 0;
        let header = [
            spv_spec.magic,
            (u32::from(dialect.version_major) << 16) | (u32::from(dialect.version_minor) << 8),
            debug_info.original_generator_magic.map_or(0, |x| x.get()),
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
        for (&name, &id) in &ids.ext_inst_imports {
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

        let mut push_attr = |target_id, attr: &Attr| match attr {
            Attr::SpvEntryPoint {
                params,
                interface_ids,
            } => {
                entry_point_insts.push(spv::Inst {
                    opcode: wk.OpEntryPoint,
                    result_type_id: None,
                    result_id: None,
                    operands: [
                        spv::Operand::Imm(params[0]),
                        spv::Operand::Id(wk.IdRef, target_id),
                    ]
                    .into_iter()
                    .chain(params[1..].iter().map(|&imm| spv::Operand::Imm(imm)))
                    .chain(
                        interface_ids
                            .iter()
                            .map(|&old_id| spv::Operand::Id(wk.IdRef, ids.old_outputs[&old_id])),
                    )
                    .collect(),
                });
            }
            Attr::SpvAnnotation { opcode, params } => {
                let inst = spv::Inst {
                    opcode: *opcode,
                    result_type_id: None,
                    result_id: None,
                    operands: iter::once(spv::Operand::Id(wk.IdRef, target_id))
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
            Attr::SpvDebugLine { .. } => unreachable!(),
        };
        let result_ids_with_attrs = interned_globals_inst_gens
            .clone()
            .map(|gen| (gen.result_id, gen.attrs))
            .chain(misc_inst_gens.clone().map(|gen| (gen.result_id, gen.attrs)));
        for (result_id, attrs) in result_ids_with_attrs {
            for attr in cx[attrs].attrs.iter() {
                if let Attr::SpvDebugLine { .. } = attr {
                    continue;
                }

                let target_id = result_id.expect(
                    "FIXME: it shouldn't be possible to attach \
                         attributes to instructions without an output",
                );
                push_attr(target_id, attr);
            }
        }

        // FIXME(eddyb) maybe make a helper for `push_inst` with an iterator?
        for entry_point_inst in entry_point_insts {
            emitter.push_inst(&entry_point_inst)?;
        }
        for execution_mode_inst in execution_mode_insts {
            emitter.push_inst(&execution_mode_inst)?;
        }

        for (&s, &id) in &ids.debug_strings {
            emitter.push_inst(&spv::Inst {
                opcode: wk.OpString,
                result_type_id: None,
                result_id: Some(id),
                operands: spv::encode_literal_string(s).collect(),
            })?;
        }
        for (lang, sources) in &debug_info.source_languages {
            let lang_operands = || {
                [
                    spv::Operand::Imm(spv::Imm::Short(wk.SourceLanguage, lang.lang)),
                    spv::Operand::Imm(spv::Imm::Short(wk.LiteralInteger, lang.version)),
                ]
                .into_iter()
            };
            if sources.file_contents.is_empty() {
                emitter.push_inst(&spv::Inst {
                    opcode: wk.OpSource,
                    result_type_id: None,
                    result_id: None,
                    operands: lang_operands().collect(),
                })?;
            } else {
                for (&file, contents) in &sources.file_contents {
                    // The maximum word count is `2**16 - 1`, the first word is
                    // taken up by the opcode & word count, and one extra byte is
                    // taken up by the nil byte at the end of the LiteralString.
                    const MAX_OP_SOURCE_CONT_CONTENTS_LEN: usize = (0xffff - 1) * 4 - 1;

                    // `OpSource` has 3 more operands than `OpSourceContinued`,
                    // and each of them take up exactly one word.
                    const MAX_OP_SOURCE_CONTENTS_LEN: usize =
                        MAX_OP_SOURCE_CONT_CONTENTS_LEN - 3 * 4;

                    let (contents_initial, mut contents_rest) =
                        contents.split_at(contents.len().min(MAX_OP_SOURCE_CONTENTS_LEN));

                    emitter.push_inst(&spv::Inst {
                        opcode: wk.OpSource,
                        result_type_id: None,
                        result_id: None,
                        operands: lang_operands()
                            .chain([spv::Operand::Id(wk.IdRef, ids.debug_strings[&cx[file]])])
                            .chain(spv::encode_literal_string(contents_initial))
                            .collect(),
                    })?;

                    while !contents_rest.is_empty() {
                        let (cont_chunk, rest) = contents_rest
                            .split_at(contents_rest.len().min(MAX_OP_SOURCE_CONT_CONTENTS_LEN));
                        contents_rest = rest;

                        emitter.push_inst(&spv::Inst {
                            opcode: wk.OpSourceContinued,
                            result_type_id: None,
                            result_id: None,
                            operands: spv::encode_literal_string(cont_chunk).collect(),
                        })?;
                    }
                }
            }
        }
        for ext_inst in debug_info.source_extension_insts() {
            emitter.push_inst(&ext_inst)?;
        }
        for debug_name_inst in debug_name_insts {
            emitter.push_inst(&debug_name_inst)?;
        }
        for mod_proc_inst in debug_info.module_processed_insts() {
            emitter.push_inst(&mod_proc_inst)?;
        }

        for decoration_inst in decoration_insts {
            emitter.push_inst(&decoration_inst)?;
        }

        let mut current_debug_line = None;
        let mut current_block_id = None; // HACK(eddyb) for `current_debug_line` resets.
        let insts_with_attrs = interned_globals_inst_gens
            .map(|gen| ((gen.mk_inst)(), gen.attrs))
            .chain(misc_inst_gens.map(|gen| ((gen.mk_inst)(), gen.attrs)));
        for (inst, attrs) in insts_with_attrs {
            // Reset line debuginfo when crossing/leaving blocks.
            let new_block_id = if inst.opcode == wk.OpLabel {
                Some(inst.result_id.unwrap())
            } else if inst.opcode == wk.OpFunctionEnd {
                None
            } else {
                current_block_id
            };
            if current_block_id != new_block_id {
                current_debug_line = None;
            }
            current_block_id = new_block_id;

            // Determine whether to emit `OpLine`/`OpNoLine` before `inst`,
            // in order to end up with the expected line debuginfo.
            // FIXME(eddyb) make this less of a search and more of a
            // lookup by splitting attrs into key and value parts.
            let new_debug_line = cx[attrs].attrs.iter().find_map(|attr| match *attr {
                Attr::SpvDebugLine {
                    file_path,
                    line,
                    col,
                } => Some((ids.debug_strings[&cx[file_path.0]], line, col)),
                _ => None,
            });
            if current_debug_line != new_debug_line {
                let (opcode, operands) = match new_debug_line {
                    Some((file_path_id, line, col)) => (
                        wk.OpLine,
                        [
                            spv::Operand::Id(wk.IdRef, file_path_id),
                            spv::Operand::Imm(spv::Imm::Short(wk.LiteralInteger, line)),
                            spv::Operand::Imm(spv::Imm::Short(wk.LiteralInteger, col)),
                        ]
                        .into_iter()
                        .collect(),
                    ),
                    None => (wk.OpNoLine, [].into_iter().collect()),
                };
                emitter.push_inst(&spv::Inst {
                    opcode,
                    result_type_id: None,
                    result_id: None,
                    operands,
                })?;
            }
            current_debug_line = new_debug_line;

            emitter.push_inst(&inst)?;
        }

        Ok(emitter)
    }
}
