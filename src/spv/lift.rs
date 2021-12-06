//! SPIR-T to SPIR-V lifting.

use crate::spv::{self, spec};
use crate::visit::{InnerVisit, Visitor};
use crate::{
    AddrSpace, Attr, AttrSet, Block, Const, ConstCtor, ConstCtorArg, ConstDef, Context,
    DataInstDef, DataInstInput, DataInstKind, DataInstOutput, DeclDef, ExportKey, Exportee, Func,
    FuncDecl, FuncDefBody, FuncParam, GlobalVar, GlobalVarDefBody, Import, Module, ModuleDebugInfo,
    ModuleDialect, Type, TypeCtor, TypeCtorArg, TypeDef,
};
use indexmap::{IndexMap, IndexSet};
use smallvec::SmallVec;
use std::collections::{BTreeMap, BTreeSet};
use std::num::NonZeroU32;
use std::path::Path;
use std::{io, iter};

impl spv::Dialect {
    fn capability_insts(&self) -> impl Iterator<Item = spv::Inst> + '_ {
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
    fn source_extension_insts(&self) -> impl Iterator<Item = spv::Inst> + '_ {
        let wk = &spec::Spec::get().well_known;
        self.source_extensions.iter().map(move |ext| spv::Inst {
            opcode: wk.OpSourceExtension,
            result_type_id: None,
            result_id: None,
            operands: spv::encode_literal_string(ext).collect(),
        })
    }

    fn module_processed_insts(&self) -> impl Iterator<Item = spv::Inst> + '_ {
        let wk = &spec::Spec::get().well_known;
        self.module_processes.iter().map(move |proc| spv::Inst {
            opcode: wk.OpModuleProcessed,
            result_type_id: None,
            result_id: None,
            operands: spv::encode_literal_string(proc).collect(),
        })
    }
}

impl FuncDecl {
    fn spv_func_type(&self, cx: &Context) -> Type {
        let wk = &spec::Spec::get().well_known;

        cx.intern(TypeDef {
            attrs: AttrSet::default(),
            ctor: TypeCtor::SpvInst(wk.OpTypeFunction),
            ctor_args: iter::once(self.ret_type)
                .chain(self.params.iter().map(|param| param.ty))
                .map(TypeCtorArg::Type)
                .collect(),
        })
    }
}

struct NeedsIdsCollector<'a> {
    cx: &'a Context,
    module: &'a Module,

    ext_inst_imports: BTreeSet<&'a str>,
    debug_strings: BTreeSet<&'a str>,

    globals: IndexSet<Global>,
    global_vars_seen: IndexSet<GlobalVar>,
    funcs: IndexSet<Func>,

    old_outputs: IndexSet<spv::Id>,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
enum Global {
    Type(Type),
    Const(Const),
}

impl Visitor<'_> for NeedsIdsCollector<'_> {
    fn visit_attr_set_use(&mut self, attrs: AttrSet) {
        self.visit_attr_set_def(&self.cx[attrs]);
    }
    fn visit_type_use(&mut self, ty: Type) {
        let global = Global::Type(ty);
        if self.globals.contains(&global) {
            return;
        }
        self.visit_type_def(&self.cx[ty]);
        self.globals.insert(global);
    }
    fn visit_const_use(&mut self, ct: Const) {
        let global = Global::Const(ct);
        if self.globals.contains(&global) {
            return;
        }
        self.visit_const_def(&self.cx[ct]);
        self.globals.insert(global);
    }

    fn visit_global_var_use(&mut self, gv: GlobalVar) {
        if self.global_vars_seen.insert(gv) {
            self.visit_global_var_decl(&self.module.global_vars[gv]);
        }
    }
    fn visit_func_use(&mut self, func: Func) {
        if self.funcs.contains(&func) {
            return;
        }
        // NOTE(eddyb) inserting first results in a different function ordering
        // in the resulting module, but the order doesn't matter, and we need
        // to avoid infinite recursion for recursive functions.
        self.funcs.insert(func);

        let func_decl = &self.module.funcs[func];
        // FIXME(eddyb) should this be cached in `self.funcs`?
        self.visit_type_use(func_decl.spv_func_type(self.cx));
        self.visit_func_decl(func_decl);
    }

    fn visit_spv_module_debug_info(&mut self, debug_info: &spv::ModuleDebugInfo) {
        for sources in debug_info.source_languages.values() {
            // The file operand of `OpSource` has to point to an `OpString`.
            self.debug_strings
                .extend(sources.file_contents.keys().copied().map(|s| &self.cx[s]));
        }
    }
    fn visit_attr(&mut self, attr: &Attr) {
        match *attr {
            Attr::SpvAnnotation { .. } | Attr::SpvBitflagsOperand(_) => {}
            Attr::SpvDebugLine { file_path, .. } => {
                self.debug_strings.insert(&self.cx[file_path.0]);
            }
        }
    }

    fn visit_data_inst_def(&mut self, data_inst_def: &DataInstDef) {
        match data_inst_def.kind {
            DataInstKind::FuncCall(_) => {}

            DataInstKind::SpvInst(_) => {}
            DataInstKind::SpvExtInst { ext_set, .. } => {
                self.ext_inst_imports.insert(&self.cx[ext_set]);
            }
        }
        data_inst_def.inner_visit_with(self);
    }
    fn visit_data_inst_output(&mut self, output: &DataInstOutput) {
        match *output {
            DataInstOutput::SpvValueResult { result_id, .. } => {
                self.old_outputs.insert(result_id);
            }
        }
        output.inner_visit_with(self);
    }
}

struct AllocatedIds<'a> {
    ext_inst_imports: BTreeMap<&'a str, spv::Id>,
    debug_strings: BTreeMap<&'a str, spv::Id>,

    globals: IndexMap<Global, spv::Id>,
    funcs: IndexMap<Func, FuncIds>,

    old_outputs: IndexMap<spv::Id, spv::Id>,
}

struct FuncIds {
    func_id: spv::Id,
    // FIXME(eddyb) should this just be a range?
    param_ids: SmallVec<[spv::Id; 4]>,
    // FIXME(eddyb) should this just be a range?
    label_ids: SmallVec<[spv::Id; 4]>,
}

impl<'a> NeedsIdsCollector<'a> {
    fn alloc_ids<E>(
        self,
        mut alloc_id: impl FnMut() -> Result<spv::Id, E>,
    ) -> Result<AllocatedIds<'a>, E> {
        let Self {
            cx: _,
            module,
            ext_inst_imports,
            debug_strings,
            globals,
            global_vars_seen: _,
            funcs,
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
            globals: globals
                .into_iter()
                .map(|g| Ok((g, alloc_id()?)))
                .collect::<Result<_, _>>()?,
            funcs: funcs
                .into_iter()
                .map(|func| {
                    let func_decl = &module.funcs[func];
                    let blocks = match &func_decl.def {
                        DeclDef::Imported(_) => &[][..],
                        DeclDef::Present(FuncDefBody {
                            data_insts: _,
                            blocks,
                        }) => blocks,
                    };
                    let func_ids = FuncIds {
                        func_id: alloc_id()?,
                        param_ids: func_decl
                            .params
                            .iter()
                            .map(|_| alloc_id())
                            .collect::<Result<_, _>>()?,
                        label_ids: blocks
                            .iter()
                            .map(|_| alloc_id())
                            .collect::<Result<_, _>>()?,
                    };
                    Ok((func, func_ids))
                })
                .collect::<Result<_, _>>()?,
            old_outputs: old_outputs
                .into_iter()
                .map(|old_id| Ok((old_id, alloc_id()?)))
                .collect::<Result<_, _>>()?,
        })
    }
}

/// "Maybe-decorated "lazy" SPIR-V instruction, allowing separately emitting
/// decorations from attributes, and the instruction itself, without eagerly
/// allocating all the instructions.
#[derive(Copy, Clone)]
enum LazyInst<'a> {
    Global(Global),
    OpFunction {
        func_id: spv::Id,
        func_decl: &'a FuncDecl,
    },
    OpFunctionParameter {
        param_id: spv::Id,
        param: &'a FuncParam,
    },
    OpLabel {
        label_id: spv::Id,
    },
    DataInst {
        parent_func: Func,
        data_inst_def: &'a DataInstDef,
    },
    OpFunctionEnd,
}

impl LazyInst<'_> {
    fn result_id_attrs_and_import(
        self,
        module: &Module,
        ids: &AllocatedIds,
    ) -> (Option<spv::Id>, AttrSet, Option<Import>) {
        let cx = module.cx_ref();

        match self {
            Self::Global(global) => {
                let (attrs, import) = match global {
                    Global::Type(ty) => (cx[ty].attrs, None),
                    Global::Const(ct) => {
                        let ct_def = &cx[ct];
                        match ct_def.ctor {
                            ConstCtor::PtrToGlobalVar(gv) => {
                                let gv_decl = &module.global_vars[gv];
                                let import = match gv_decl.def {
                                    DeclDef::Imported(import) => Some(import),
                                    DeclDef::Present(_) => None,
                                };
                                (gv_decl.attrs, import)
                            }
                            ConstCtor::SpvInst(_) => (ct_def.attrs, None),
                        }
                    }
                };
                (Some(ids.globals[&global]), attrs, import)
            }
            Self::OpFunction { func_id, func_decl } => {
                let import = match func_decl.def {
                    DeclDef::Imported(import) => Some(import),
                    DeclDef::Present(_) => None,
                };
                (Some(func_id), func_decl.attrs, import)
            }
            Self::OpFunctionParameter { param_id, param } => (Some(param_id), param.attrs, None),
            Self::OpLabel { label_id } => (Some(label_id), AttrSet::default(), None),
            Self::DataInst {
                parent_func: _,
                data_inst_def,
            } => {
                let result_id = data_inst_def
                    .output
                    .as_ref()
                    .map(|old_output| match *old_output {
                        DataInstOutput::SpvValueResult {
                            result_id: old_result_id,
                            ..
                        } => ids.old_outputs[&old_result_id],
                    });
                (result_id, data_inst_def.attrs, None)
            }
            Self::OpFunctionEnd => (None, AttrSet::default(), None),
        }
    }

    fn to_inst_and_attrs(self, module: &Module, ids: &AllocatedIds) -> (spv::Inst, AttrSet) {
        let wk = &spec::Spec::get().well_known;
        let cx = module.cx_ref();

        let (result_id, attrs, _) = self.result_id_attrs_and_import(module, ids);
        let inst = match self {
            Self::Global(global) => match global {
                Global::Type(ty) => {
                    let ty_def = &cx[ty];
                    spv::Inst {
                        opcode: match ty_def.ctor {
                            TypeCtor::SpvInst(opcode) => opcode,
                        },
                        result_type_id: None,
                        result_id,
                        operands: ty_def
                            .ctor_args
                            .iter()
                            .map(|&arg| match arg {
                                TypeCtorArg::Type(ty) => {
                                    spv::Operand::Id(wk.IdRef, ids.globals[&Global::Type(ty)])
                                }
                                TypeCtorArg::Const(ct) => {
                                    spv::Operand::Id(wk.IdRef, ids.globals[&Global::Const(ct)])
                                }
                                TypeCtorArg::SpvImm(imm) => spv::Operand::Imm(imm),
                            })
                            .collect(),
                    }
                }
                Global::Const(ct) => {
                    let ct_def = &cx[ct];
                    match ct_def.ctor {
                        ConstCtor::PtrToGlobalVar(gv) => {
                            assert!(ct_def.attrs == AttrSet::default());
                            assert!(ct_def.ctor_args.is_empty());

                            let gv_decl = &module.global_vars[gv];

                            assert!(ct_def.ty == gv_decl.type_of_ptr_to);

                            let storage_class = match gv_decl.addr_space {
                                AddrSpace::SpvStorageClass(sc) => {
                                    spv::Operand::Imm(spv::Imm::Short(wk.StorageClass, sc))
                                }
                            };
                            let initializer = match gv_decl.def {
                                DeclDef::Imported(_) => None,
                                DeclDef::Present(GlobalVarDefBody { initializer }) => initializer
                                    .map(|initializer| {
                                        spv::Operand::Id(
                                            wk.IdRef,
                                            ids.globals[&Global::Const(initializer)],
                                        )
                                    }),
                            };
                            spv::Inst {
                                opcode: wk.OpVariable,
                                result_type_id: Some(ids.globals[&Global::Type(ct_def.ty)]),
                                result_id,
                                operands: iter::once(storage_class).chain(initializer).collect(),
                            }
                        }

                        ConstCtor::SpvInst(opcode) => spv::Inst {
                            opcode,
                            result_type_id: Some(ids.globals[&Global::Type(ct_def.ty)]),
                            result_id,
                            operands: ct_def
                                .ctor_args
                                .iter()
                                .map(|&arg| match arg {
                                    ConstCtorArg::Const(ct) => {
                                        spv::Operand::Id(wk.IdRef, ids.globals[&Global::Const(ct)])
                                    }
                                    ConstCtorArg::SpvImm(imm) => spv::Operand::Imm(imm),
                                })
                                .collect(),
                        },
                    }
                }
            },
            Self::OpFunction {
                func_id: _,
                func_decl,
            } => {
                // FIXME(eddyb) make this less of a search and more of a
                // lookup by splitting attrs into key and value parts.
                let func_ctrl = cx[attrs]
                    .attrs
                    .iter()
                    .find_map(|attr| match *attr {
                        Attr::SpvBitflagsOperand(spv::Imm::Short(kind, word))
                            if kind == wk.FunctionControl =>
                        {
                            Some(word)
                        }
                        _ => None,
                    })
                    .unwrap_or(0);

                spv::Inst {
                    opcode: wk.OpFunction,
                    result_type_id: Some(ids.globals[&Global::Type(func_decl.ret_type)]),
                    result_id,
                    operands: [
                        spv::Operand::Imm(spv::Imm::Short(wk.FunctionControl, func_ctrl)),
                        spv::Operand::Id(
                            wk.IdRef,
                            ids.globals[&Global::Type(func_decl.spv_func_type(cx))],
                        ),
                    ]
                    .into_iter()
                    .collect(),
                }
            }
            Self::OpFunctionParameter { param_id: _, param } => spv::Inst {
                opcode: wk.OpFunctionParameter,
                result_type_id: Some(ids.globals[&Global::Type(param.ty)]),
                result_id,
                operands: [].into_iter().collect(),
            },
            Self::OpLabel { label_id: _ } => spv::Inst {
                opcode: wk.OpLabel,
                result_type_id: None,
                result_id,
                operands: [].into_iter().collect(),
            },
            Self::DataInst {
                parent_func,
                data_inst_def,
            } => {
                let (opcode, extra_initial_operands): (_, SmallVec<[_; 2]>) =
                    match data_inst_def.kind {
                        DataInstKind::FuncCall(callee) => (
                            wk.OpFunctionCall,
                            [spv::Operand::Id(wk.IdRef, ids.funcs[&callee].func_id)]
                                .into_iter()
                                .collect(),
                        ),
                        DataInstKind::SpvInst(opcode) => (opcode, [].into_iter().collect()),
                        DataInstKind::SpvExtInst { ext_set, inst } => (
                            wk.OpExtInst,
                            [
                                spv::Operand::Id(wk.IdRef, ids.ext_inst_imports[&cx[ext_set]]),
                                spv::Operand::Imm(spv::Imm::Short(wk.LiteralExtInstInteger, inst)),
                            ]
                            .into_iter()
                            .collect(),
                        ),
                    };
                spv::Inst {
                    opcode,
                    result_type_id: data_inst_def.output.map(|old_output| match old_output {
                        DataInstOutput::SpvValueResult { result_type, .. } => {
                            ids.globals[&Global::Type(result_type)]
                        }
                    }),
                    result_id,
                    operands: extra_initial_operands
                        .into_iter()
                        .chain(data_inst_def.inputs.iter().map(|&input| match input {
                            DataInstInput::Const(ct) => {
                                spv::Operand::Id(wk.IdRef, ids.globals[&Global::Const(ct)])
                            }
                            DataInstInput::FuncParam { idx } => spv::Operand::Id(
                                wk.IdRef,
                                ids.funcs[&parent_func].param_ids[usize::try_from(idx).unwrap()],
                            ),

                            DataInstInput::Block { idx } => spv::Operand::Id(
                                wk.IdRef,
                                ids.funcs[&parent_func].label_ids[usize::try_from(idx).unwrap()],
                            ),

                            DataInstInput::SpvImm(imm) => spv::Operand::Imm(imm),
                            DataInstInput::SpvUntrackedId(old_id) => {
                                spv::Operand::Id(wk.IdRef, ids.old_outputs[&old_id])
                            }
                        }))
                        .collect(),
                }
            }
            Self::OpFunctionEnd => spv::Inst {
                opcode: wk.OpFunctionEnd,
                result_type_id: None,
                result_id: None,
                operands: [].into_iter().collect(),
            },
        };
        (inst, attrs)
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
            module: self,
            ext_inst_imports: BTreeSet::new(),
            debug_strings: BTreeSet::new(),
            globals: IndexSet::new(),
            global_vars_seen: IndexSet::new(),
            funcs: IndexSet::new(),
            old_outputs: IndexSet::new(),
        };
        needs_ids_collector.visit_module(self);

        // Because `GlobalVar`s are given IDs by the `Const`s that point to them
        // (i.e. `ConstCtor::PtrToGlobalVar`), any `GlobalVar`s in other positions
        // require extra care to ensure the ID-giving `Const` is visited.
        let global_var_to_id_giving_global = |gv| {
            let type_of_ptr_to_global_var = self.global_vars[gv].type_of_ptr_to;
            let ptr_to_global_var = cx.intern(ConstDef {
                attrs: AttrSet::default(),
                ty: type_of_ptr_to_global_var,
                ctor: ConstCtor::PtrToGlobalVar(gv),
                ctor_args: [].into_iter().collect(),
            });
            Global::Const(ptr_to_global_var)
        };
        for &gv in &needs_ids_collector.global_vars_seen {
            needs_ids_collector
                .globals
                .insert(global_var_to_id_giving_global(gv));
        }

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

        let global_and_func_insts =
            ids.globals
                .keys()
                .copied()
                .map(LazyInst::Global)
                .chain(ids.funcs.iter().flat_map(|(&func, func_ids)| {
                    let func_decl = &self.funcs[func];
                    let func_def_body = match &func_decl.def {
                        DeclDef::Imported(_) => None,
                        DeclDef::Present(def) => Some(def),
                    };

                    iter::once(LazyInst::OpFunction {
                        func_id: func_ids.func_id,
                        func_decl,
                    })
                    .chain(func_ids.param_ids.iter().zip(&func_decl.params).map(
                        |(&param_id, param)| LazyInst::OpFunctionParameter { param_id, param },
                    ))
                    .chain(func_def_body.into_iter().flat_map(move |func_def_body| {
                        let FuncDefBody { data_insts, blocks } = func_def_body;

                        func_ids
                            .label_ids
                            .iter()
                            .zip(blocks)
                            .flat_map(move |(&label_id, block)| {
                                let Block { insts } = block;

                                iter::once(LazyInst::OpLabel { label_id }).chain(insts.iter().map(
                                    move |&inst| LazyInst::DataInst {
                                        parent_func: func,
                                        data_inst_def: &data_insts[inst],
                                    },
                                ))
                            })
                    }))
                    .chain([LazyInst::OpFunctionEnd])
                }));

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

        for lazy_inst in global_and_func_insts.clone() {
            let (result_id, attrs, import) = lazy_inst.result_id_attrs_and_import(self, &ids);

            for attr in cx[attrs].attrs.iter() {
                match attr {
                    Attr::SpvAnnotation { opcode, params } => {
                        let target_id = result_id.expect(
                            "FIXME: it shouldn't be possible to attach \
                                 attributes to instructions without an output",
                        );

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
                    Attr::SpvDebugLine { .. } | Attr::SpvBitflagsOperand(_) => {}
                }

                if let Some(import) = import {
                    let target_id = result_id.unwrap();
                    match import {
                        Import::LinkName(name) => {
                            decoration_insts.push(spv::Inst {
                                opcode: wk.OpDecorate,
                                result_type_id: None,
                                result_id: None,
                                operands: [
                                    spv::Operand::Id(wk.IdRef, target_id),
                                    spv::Operand::Imm(spv::Imm::Short(
                                        wk.Decoration,
                                        wk.LinkageAttributes,
                                    )),
                                ]
                                .into_iter()
                                .chain(spv::encode_literal_string(&cx[name]))
                                .chain([spv::Operand::Imm(spv::Imm::Short(
                                    wk.LinkageType,
                                    wk.Import,
                                ))])
                                .collect(),
                            });
                        }
                    }
                }
            }
        }

        for (export_key, &exportee) in &self.exports {
            let target_id = match exportee {
                Exportee::GlobalVar(gv) => ids.globals[&global_var_to_id_giving_global(gv)],
                Exportee::Func(func) => ids.funcs[&func].func_id,
            };
            match export_key {
                &ExportKey::LinkName(name) => {
                    decoration_insts.push(spv::Inst {
                        opcode: wk.OpDecorate,
                        result_type_id: None,
                        result_id: None,
                        operands: [
                            spv::Operand::Id(wk.IdRef, target_id),
                            spv::Operand::Imm(spv::Imm::Short(wk.Decoration, wk.LinkageAttributes)),
                        ]
                        .into_iter()
                        .chain(spv::encode_literal_string(&cx[name]))
                        .chain([spv::Operand::Imm(spv::Imm::Short(
                            wk.LinkageType,
                            wk.Export,
                        ))])
                        .collect(),
                    });
                }
                ExportKey::SpvEntryPoint {
                    params,
                    interface_global_vars,
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
                        .chain(interface_global_vars.iter().map(|&gv| {
                            spv::Operand::Id(
                                wk.IdRef,
                                ids.globals[&global_var_to_id_giving_global(gv)],
                            )
                        }))
                        .collect(),
                    });
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
        for lazy_inst in global_and_func_insts {
            let (inst, attrs) = lazy_inst.to_inst_and_attrs(self, &ids);

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
