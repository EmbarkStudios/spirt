//! SPIR-T to SPIR-V lifting.

use crate::spv::{self, spec};
use crate::visit::{InnerVisit, Visitor};
use crate::{
    cfg, AddrSpace, Attr, AttrSet, Const, ConstCtor, ConstDef, Context, ControlNodeKind,
    ControlNodeOutputDecl, DataInst, DataInstDef, DataInstKind, DeclDef, EntityList, ExportKey,
    Exportee, Func, FuncDecl, FuncParam, FxIndexMap, FxIndexSet, GlobalVar, GlobalVarDefBody,
    Import, Module, ModuleDebugInfo, ModuleDialect, Type, TypeCtor, TypeCtorArg, TypeDef, Value,
};
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use std::collections::{BTreeMap, BTreeSet};
use std::num::NonZeroU32;
use std::path::Path;
use std::{io, iter, mem};

impl spv::Dialect {
    fn capability_insts(&self) -> impl Iterator<Item = spv::InstWithIds> + '_ {
        let wk = &spec::Spec::get().well_known;
        self.capabilities.iter().map(move |&cap| spv::InstWithIds {
            without_ids: spv::Inst {
                opcode: wk.OpCapability,
                imms: iter::once(spv::Imm::Short(wk.Capability, cap)).collect(),
            },
            result_type_id: None,
            result_id: None,
            ids: [].into_iter().collect(),
        })
    }

    pub fn extension_insts(&self) -> impl Iterator<Item = spv::InstWithIds> + '_ {
        let wk = &spec::Spec::get().well_known;
        self.extensions.iter().map(move |ext| spv::InstWithIds {
            without_ids: spv::Inst {
                opcode: wk.OpExtension,
                imms: spv::encode_literal_string(ext).collect(),
            },
            result_type_id: None,
            result_id: None,
            ids: [].into_iter().collect(),
        })
    }
}

impl spv::ModuleDebugInfo {
    fn source_extension_insts(&self) -> impl Iterator<Item = spv::InstWithIds> + '_ {
        let wk = &spec::Spec::get().well_known;
        self.source_extensions
            .iter()
            .map(move |ext| spv::InstWithIds {
                without_ids: spv::Inst {
                    opcode: wk.OpSourceExtension,
                    imms: spv::encode_literal_string(ext).collect(),
                },
                result_type_id: None,
                result_id: None,
                ids: [].into_iter().collect(),
            })
    }

    fn module_processed_insts(&self) -> impl Iterator<Item = spv::InstWithIds> + '_ {
        let wk = &spec::Spec::get().well_known;
        self.module_processes
            .iter()
            .map(move |proc| spv::InstWithIds {
                without_ids: spv::Inst {
                    opcode: wk.OpModuleProcessed,
                    imms: spv::encode_literal_string(proc).collect(),
                },
                result_type_id: None,
                result_id: None,
                ids: [].into_iter().collect(),
            })
    }
}

impl FuncDecl {
    fn spv_func_type(&self, cx: &Context) -> Type {
        let wk = &spec::Spec::get().well_known;

        cx.intern(TypeDef {
            attrs: AttrSet::default(),
            ctor: TypeCtor::SpvInst(wk.OpTypeFunction.into()),
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

    globals: FxIndexSet<Global>,
    global_vars_seen: FxIndexSet<GlobalVar>,
    funcs: FxIndexSet<Func>,
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
}

struct AllocatedIds<'a> {
    ext_inst_imports: BTreeMap<&'a str, spv::Id>,
    debug_strings: BTreeMap<&'a str, spv::Id>,

    // FIXME(eddyb) use `EntityOrientedDenseMap` here.
    globals: FxIndexMap<Global, spv::Id>,
    // FIXME(eddyb) use `EntityOrientedDenseMap` here.
    funcs: FxIndexMap<Func, FuncLifting<'a>>,
}

// FIXME(eddyb) should this use ID ranges instead of `SmallVec<[spv::Id; 4]>`?
struct FuncLifting<'a> {
    func_id: spv::Id,
    param_ids: SmallVec<[spv::Id; 4]>,
    // FIXME(eddyb) use `EntityOrientedDenseMap` here.
    data_inst_output_ids: FxHashMap<DataInst, spv::Id>,
    // FIXME(eddyb) use `EntityOrientedDenseMap` here.
    label_ids: FxHashMap<cfg::ControlPoint, spv::Id>,
    // FIXME(eddyb) use `EntityOrientedDenseMap` here (modulo iteration?).
    blocks: FxIndexMap<cfg::ControlPoint, BlockLifting<'a>>,
}

struct BlockLifting<'a> {
    phis: SmallVec<[Phi; 2]>,
    insts: SmallVec<[EntityList<DataInst>; 1]>,
    terminator: &'a cfg::ControlInst,
}

struct Phi {
    output_decl: ControlNodeOutputDecl,

    result_id: spv::Id,
    cases: SmallVec<[(Value, cfg::ControlPoint); 2]>,
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
                    Ok((
                        func,
                        FuncLifting::from_func_decl(&module.funcs[func], || alloc_id())?,
                    ))
                })
                .collect::<Result<_, _>>()?,
        })
    }
}

impl<'a> FuncLifting<'a> {
    fn from_func_decl<E>(
        func_decl: &'a FuncDecl,
        mut alloc_id: impl FnMut() -> Result<spv::Id, E>,
    ) -> Result<Self, E> {
        let func_id = alloc_id()?;
        let param_ids = func_decl
            .params
            .iter()
            .map(|_| alloc_id())
            .collect::<Result<_, _>>()?;

        let func_def_body = match &func_decl.def {
            DeclDef::Imported(_) => {
                return Ok(Self {
                    func_id,
                    param_ids,
                    data_inst_output_ids: Default::default(),
                    label_ids: Default::default(),
                    blocks: Default::default(),
                });
            }
            DeclDef::Present(def) => def,
        };

        // Create a SPIR-V block for every CFG point needing one.
        let mut blocks: FxIndexMap<_, _> = func_def_body
            .cfg
            .rev_post_order(func_def_body)
            .filter(
                |point| match func_def_body.control_nodes[point.control_node()].kind {
                    // Only create a block for the `Entry` point of a
                    // `ControlNodeKind::Block`, not also its `Exit`.
                    ControlNodeKind::Block { .. } => {
                        matches!(point, cfg::ControlPoint::Entry(_))
                    }
                    _ => true,
                },
            )
            .map(|point| {
                let control_node_def = &func_def_body.control_nodes[point.control_node()];
                let phis = if let cfg::ControlPoint::Exit(_) = point {
                    control_node_def
                        .outputs
                        .iter()
                        .map(|&output_decl| {
                            Ok(Phi {
                                result_id: alloc_id()?,
                                cases: SmallVec::new(),
                                output_decl,
                            })
                        })
                        .collect::<Result<_, _>>()?
                } else {
                    SmallVec::new()
                };
                let (insts, terminator) = match control_node_def.kind {
                    ControlNodeKind::Block { insts } => {
                        // The terminator of a `ControlNodeKind::Block` is attached
                        // to its `Exit` point, but as per the `filter` above,
                        // the block itself is attached to the `Entry` point.
                        let terminator = func_def_body
                            .cfg
                            .control_insts
                            .get(cfg::ControlPoint::Exit(point.control_node()))
                            .expect("missing terminator for `ControlNodeKind::Block`");

                        (insts.into_iter().collect(), terminator)
                    }
                    _ => (
                        SmallVec::new(),
                        func_def_body
                            .cfg
                            .control_insts
                            .get(point)
                            .expect("missing terminator"),
                    ),
                };
                Ok((
                    point,
                    BlockLifting {
                        phis,
                        insts,
                        terminator,
                    },
                ))
            })
            .collect::<Result<_, _>>()?;

        // Count the number of "uses" of each block (each incoming edge, plus
        // `1` for the entry block), to help determine which blocks are part
        // of a linear branch chain (and potentially fusable), later on.
        //
        // FIXME(eddyb) also count uses in selection/loop merges, when that
        // information starts being emitted.
        // FIXME(eddyb) use `EntityOrientedDenseMap` here.
        let mut use_counts = FxHashMap::default();
        use_counts.reserve(blocks.len());
        if let Some((&entry_point, _)) = blocks.first() {
            use_counts.insert(entry_point, 1usize);
        }
        for block in blocks.values() {
            for &target in &block.terminator.targets {
                *use_counts.entry(target).or_default() += 1;
            }
        }

        // Fuse chains of linear branches, when there is no information being
        // lost by the fusion. This is done in reverse order, so that in e.g.
        // `a -> b -> c`, `b -> c` is fused first, then when the iteration
        // reaches `a`, it sees `a -> bc` and can further fuse that into one
        // `abc` block, without knowing about `b` and `c` themselves
        // (this is possible because RPO will always output `[a, b, c]`, when
        // `b` and `c` only have one predecessor each).
        //
        // HACK(eddyb) this takes advantage of `blocks` being an `IndexMap`,
        // to iterate at the same time as mutating other entries.
        for block_idx in (0..blocks.len()).rev() {
            let BlockLifting {
                terminator: original_terminator,
                ..
            } = blocks[block_idx];

            let is_trivial_branch = {
                let cfg::ControlInst {
                    attrs,
                    kind,
                    inputs,
                    targets,
                    target_merge_outputs,
                } = original_terminator;

                *attrs == AttrSet::default()
                    && matches!(kind, cfg::ControlInstKind::Branch)
                    && inputs.is_empty()
                    && targets.len() == 1
                    && target_merge_outputs.is_empty()
            };

            if is_trivial_branch {
                let target = original_terminator.targets[0];
                let target_use_count = use_counts.get_mut(&target).unwrap();

                if *target_use_count == 1 {
                    let BlockLifting {
                        phis: ref target_phis,
                        insts: ref mut extra_insts,
                        terminator: new_terminator,
                    } = blocks[&target];

                    // FIXME(eddyb) check for block-level attributes, once/if
                    // they start being tracked.
                    if target_phis.is_empty() {
                        let extra_insts = mem::take(extra_insts);
                        *target_use_count = 0;

                        let combined_block = &mut blocks[block_idx];
                        combined_block.insts.extend(extra_insts);
                        combined_block.terminator = new_terminator;
                    }
                }
            }
        }

        // Remove now-unused blocks.
        blocks.retain(|point, _| use_counts[&point] > 0);

        // Collect `OpPhi`s from other blocks' edges into each block.
        //
        // HACK(eddyb) this takes advantage of `blocks` being an `IndexMap`,
        // to iterate at the same time as mutating other entries.
        for block_idx in 0..blocks.len() {
            let (&source_point, &BlockLifting { terminator, .. }) =
                blocks.get_index(block_idx).unwrap();

            for (&target, outputs) in &terminator.target_merge_outputs {
                let target_block = blocks.get_mut(&cfg::ControlPoint::Exit(target)).unwrap();
                for (target_phi, &v) in target_block.phis.iter_mut().zip(outputs) {
                    target_phi.cases.push((v, source_point));
                }
            }
        }

        let all_insts_with_output = blocks
            .values()
            .flat_map(|block| block.insts.iter().copied())
            .flat_map(|insts| func_def_body.at(Some(insts)))
            .filter(|&func_at_inst| func_at_inst.def().output_type.is_some())
            .map(|func_at_inst| func_at_inst.position);

        Ok(Self {
            func_id,
            param_ids,
            data_inst_output_ids: all_insts_with_output
                .map(|inst| Ok((inst, alloc_id()?)))
                .collect::<Result<_, _>>()?,
            label_ids: blocks
                .keys()
                .map(|&point| Ok((point, alloc_id()?)))
                .collect::<Result<_, _>>()?,
            blocks: blocks,
        })
    }
}

/// "Maybe-decorated "lazy" SPIR-V instruction, allowing separately emitting
/// decorations from attributes, and the instruction itself, without eagerly
/// allocating all the instructions.
#[derive(Copy, Clone)]
enum LazyInst<'a, 'b> {
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
    OpPhi {
        parent_func: &'b FuncLifting<'a>,
        phi: &'b Phi,
    },
    DataInst {
        parent_func: &'b FuncLifting<'a>,
        result_id: Option<spv::Id>,
        data_inst_def: &'a DataInstDef,
    },
    ControlInst {
        parent_func: &'b FuncLifting<'a>,
        control_inst: &'a cfg::ControlInst,
    },
    OpFunctionEnd,
}

impl LazyInst<'_, '_> {
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
                            ConstCtor::SpvInst { .. } => (ct_def.attrs, None),
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
            Self::OpPhi {
                parent_func: _,
                phi,
            } => (Some(phi.result_id), phi.output_decl.attrs, None),
            Self::DataInst {
                parent_func: _,
                result_id,
                data_inst_def,
            } => (result_id, data_inst_def.attrs, None),
            Self::ControlInst {
                parent_func: _,
                control_inst,
            } => (None, control_inst.attrs, None),
            Self::OpFunctionEnd => (None, AttrSet::default(), None),
        }
    }

    fn to_inst_and_attrs(self, module: &Module, ids: &AllocatedIds) -> (spv::InstWithIds, AttrSet) {
        let wk = &spec::Spec::get().well_known;
        let cx = module.cx_ref();

        let value_to_id = |parent_func: &FuncLifting, v| match v {
            Value::Const(ct) => ids.globals[&Global::Const(ct)],
            Value::FuncParam { idx } => parent_func.param_ids[usize::try_from(idx).unwrap()],
            Value::ControlNodeOutput {
                control_node,
                output_idx,
            } => {
                parent_func.blocks[&cfg::ControlPoint::Exit(control_node)].phis
                    [usize::try_from(output_idx).unwrap()]
                .result_id
            }
            Value::DataInstOutput(inst) => parent_func.data_inst_output_ids[&inst],
        };

        let (result_id, attrs, _) = self.result_id_attrs_and_import(module, ids);
        let inst = match self {
            Self::Global(global) => match global {
                Global::Type(ty) => {
                    let ty_def = &cx[ty];
                    match &ty_def.ctor {
                        TypeCtor::SpvInst(inst) => spv::InstWithIds {
                            without_ids: inst.clone(),
                            result_type_id: None,
                            result_id,
                            ids: ty_def
                                .ctor_args
                                .iter()
                                .map(|&arg| {
                                    ids.globals[&match arg {
                                        TypeCtorArg::Type(ty) => Global::Type(ty),
                                        TypeCtorArg::Const(ct) => Global::Const(ct),
                                    }]
                                })
                                .collect(),
                        },
                    }
                }
                Global::Const(ct) => {
                    let ct_def = &cx[ct];
                    match &ct_def.ctor {
                        &ConstCtor::PtrToGlobalVar(gv) => {
                            assert!(ct_def.attrs == AttrSet::default());
                            assert!(ct_def.ctor_args.is_empty());

                            let gv_decl = &module.global_vars[gv];

                            assert!(ct_def.ty == gv_decl.type_of_ptr_to);

                            let storage_class = match gv_decl.addr_space {
                                AddrSpace::SpvStorageClass(sc) => {
                                    spv::Imm::Short(wk.StorageClass, sc)
                                }
                            };
                            let initializer = match gv_decl.def {
                                DeclDef::Imported(_) => None,
                                DeclDef::Present(GlobalVarDefBody { initializer }) => initializer
                                    .map(|initializer| ids.globals[&Global::Const(initializer)]),
                            };
                            spv::InstWithIds {
                                without_ids: spv::Inst {
                                    opcode: wk.OpVariable,
                                    imms: iter::once(storage_class).collect(),
                                },
                                result_type_id: Some(ids.globals[&Global::Type(ct_def.ty)]),
                                result_id,
                                ids: initializer.into_iter().collect(),
                            }
                        }

                        ConstCtor::SpvInst(inst) => spv::InstWithIds {
                            without_ids: inst.clone(),
                            result_type_id: Some(ids.globals[&Global::Type(ct_def.ty)]),
                            result_id,
                            ids: ct_def
                                .ctor_args
                                .iter()
                                .map(|&ct| ids.globals[&Global::Const(ct)])
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

                spv::InstWithIds {
                    without_ids: spv::Inst {
                        opcode: wk.OpFunction,
                        imms: iter::once(spv::Imm::Short(wk.FunctionControl, func_ctrl)).collect(),
                    },
                    result_type_id: Some(ids.globals[&Global::Type(func_decl.ret_type)]),
                    result_id,
                    ids: iter::once(ids.globals[&Global::Type(func_decl.spv_func_type(cx))])
                        .collect(),
                }
            }
            Self::OpFunctionParameter { param_id: _, param } => spv::InstWithIds {
                without_ids: wk.OpFunctionParameter.into(),
                result_type_id: Some(ids.globals[&Global::Type(param.ty)]),
                result_id,
                ids: [].into_iter().collect(),
            },
            Self::OpLabel { label_id: _ } => spv::InstWithIds {
                without_ids: wk.OpLabel.into(),
                result_type_id: None,
                result_id,
                ids: [].into_iter().collect(),
            },
            Self::OpPhi { parent_func, phi } => spv::InstWithIds {
                without_ids: wk.OpPhi.into(),
                result_type_id: Some(ids.globals[&Global::Type(phi.output_decl.ty)]),
                result_id: Some(phi.result_id),
                ids: phi
                    .cases
                    .iter()
                    .flat_map(|&(v, source_point)| {
                        [
                            value_to_id(parent_func, v),
                            parent_func.label_ids[&source_point],
                        ]
                    })
                    .collect(),
            },
            Self::DataInst {
                parent_func,
                result_id: _,
                data_inst_def,
            } => {
                let (inst, extra_initial_id_operand) = match &data_inst_def.kind {
                    &DataInstKind::FuncCall(callee) => {
                        (wk.OpFunctionCall.into(), Some(ids.funcs[&callee].func_id))
                    }
                    DataInstKind::SpvInst(inst) => (inst.clone(), None),
                    &DataInstKind::SpvExtInst { ext_set, inst } => (
                        spv::Inst {
                            opcode: wk.OpExtInst,
                            imms: iter::once(spv::Imm::Short(wk.LiteralExtInstInteger, inst))
                                .collect(),
                        },
                        Some(ids.ext_inst_imports[&cx[ext_set]]),
                    ),
                };
                spv::InstWithIds {
                    without_ids: inst,
                    result_type_id: data_inst_def
                        .output_type
                        .map(|ty| ids.globals[&Global::Type(ty)]),
                    result_id,
                    ids: extra_initial_id_operand
                        .into_iter()
                        .chain(
                            data_inst_def
                                .inputs
                                .iter()
                                .map(|&v| value_to_id(parent_func, v)),
                        )
                        .collect(),
                }
            }
            Self::ControlInst {
                parent_func,
                control_inst,
            } => {
                let inst = match &control_inst.kind {
                    cfg::ControlInstKind::Unreachable => wk.OpUnreachable.into(),
                    cfg::ControlInstKind::Return => {
                        if control_inst.inputs.is_empty() {
                            wk.OpReturn.into()
                        } else {
                            wk.OpReturnValue.into()
                        }
                    }
                    cfg::ControlInstKind::ExitInvocation(cfg::ExitInvocationKind::SpvInst(
                        inst,
                    )) => inst.clone(),

                    cfg::ControlInstKind::Branch => wk.OpBranch.into(),

                    cfg::ControlInstKind::SelectBranch(cfg::SelectionKind::BoolCond) => {
                        wk.OpBranchConditional.into()
                    }
                    cfg::ControlInstKind::SelectBranch(cfg::SelectionKind::SpvInst(inst)) => {
                        inst.clone()
                    }
                };
                spv::InstWithIds {
                    without_ids: inst,
                    result_type_id: None,
                    result_id: None,
                    ids: control_inst
                        .inputs
                        .iter()
                        .map(|&v| value_to_id(parent_func, v))
                        .chain(
                            control_inst
                                .targets
                                .iter()
                                .map(|&target| parent_func.label_ids[&target]),
                        )
                        .collect(),
                }
            }
            Self::OpFunctionEnd => spv::InstWithIds {
                without_ids: wk.OpFunctionEnd.into(),
                result_type_id: None,
                result_id: None,
                ids: [].into_iter().collect(),
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
            globals: FxIndexSet::default(),
            global_vars_seen: FxIndexSet::default(),
            funcs: FxIndexSet::default(),
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
                .chain(ids.funcs.iter().flat_map(|(&func, func_lifting)| {
                    let func_decl = &self.funcs[func];
                    let func_def_body = match &func_decl.def {
                        DeclDef::Imported(_) => None,
                        DeclDef::Present(def) => Some(def),
                    };

                    iter::once(LazyInst::OpFunction {
                        func_id: func_lifting.func_id,
                        func_decl,
                    })
                    .chain(func_lifting.param_ids.iter().zip(&func_decl.params).map(
                        |(&param_id, param)| LazyInst::OpFunctionParameter { param_id, param },
                    ))
                    .chain(func_lifting.blocks.iter().flat_map(move |(point, block)| {
                        let BlockLifting {
                            phis,
                            insts,
                            terminator,
                        } = block;

                        iter::once(LazyInst::OpLabel {
                            label_id: func_lifting.label_ids[&point],
                        })
                        .chain(phis.iter().map(|phi| LazyInst::OpPhi {
                            parent_func: func_lifting,
                            phi,
                        }))
                        .chain(
                            insts
                                .iter()
                                .copied()
                                .flat_map(move |insts| func_def_body.unwrap().at(Some(insts)))
                                .map(move |func_at_inst| {
                                    let data_inst_def = func_at_inst.def();
                                    LazyInst::DataInst {
                                        parent_func: func_lifting,
                                        result_id: data_inst_def.output_type.map(|_| {
                                            func_lifting.data_inst_output_ids
                                                [&func_at_inst.position]
                                        }),
                                        data_inst_def,
                                    }
                                }),
                        )
                        .chain([LazyInst::ControlInst {
                            parent_func: func_lifting,
                            control_inst: terminator,
                        }])
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
            emitter.push_inst(&spv::InstWithIds {
                without_ids: spv::Inst {
                    opcode: wk.OpExtInstImport,
                    imms: spv::encode_literal_string(name).collect(),
                },
                result_type_id: None,
                result_id: Some(id),
                ids: [].into_iter().collect(),
            })?;
        }
        emitter.push_inst(&spv::InstWithIds {
            without_ids: spv::Inst {
                opcode: wk.OpMemoryModel,
                imms: [
                    spv::Imm::Short(wk.AddressingModel, dialect.addressing_model),
                    spv::Imm::Short(wk.MemoryModel, dialect.memory_model),
                ]
                .into_iter()
                .collect(),
            },
            result_type_id: None,
            result_id: None,
            ids: [].into_iter().collect(),
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
                    Attr::SpvAnnotation(inst @ spv::Inst { opcode, .. }) => {
                        let target_id = result_id.expect(
                            "FIXME: it shouldn't be possible to attach \
                                 attributes to instructions without an output",
                        );

                        let inst = spv::InstWithIds {
                            without_ids: inst.clone(),
                            result_type_id: None,
                            result_id: None,
                            ids: iter::once(target_id).collect(),
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
                            decoration_insts.push(spv::InstWithIds {
                                without_ids: spv::Inst {
                                    opcode: wk.OpDecorate,
                                    imms: iter::once(spv::Imm::Short(
                                        wk.Decoration,
                                        wk.LinkageAttributes,
                                    ))
                                    .chain(spv::encode_literal_string(&cx[name]))
                                    .chain([spv::Imm::Short(wk.LinkageType, wk.Import)])
                                    .collect(),
                                },
                                result_type_id: None,
                                result_id: None,
                                ids: iter::once(target_id).collect(),
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
                    decoration_insts.push(spv::InstWithIds {
                        without_ids: spv::Inst {
                            opcode: wk.OpDecorate,
                            imms: iter::once(spv::Imm::Short(wk.Decoration, wk.LinkageAttributes))
                                .chain(spv::encode_literal_string(&cx[name]))
                                .chain([spv::Imm::Short(wk.LinkageType, wk.Export)])
                                .collect(),
                        },
                        result_type_id: None,
                        result_id: None,
                        ids: iter::once(target_id).collect(),
                    });
                }
                ExportKey::SpvEntryPoint {
                    imms,
                    interface_global_vars,
                } => {
                    entry_point_insts.push(spv::InstWithIds {
                        without_ids: spv::Inst {
                            opcode: wk.OpEntryPoint,
                            imms: imms.iter().copied().collect(),
                        },
                        result_type_id: None,
                        result_id: None,
                        ids: iter::once(target_id)
                            .chain(
                                interface_global_vars
                                    .iter()
                                    .map(|&gv| ids.globals[&global_var_to_id_giving_global(gv)]),
                            )
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
            emitter.push_inst(&spv::InstWithIds {
                without_ids: spv::Inst {
                    opcode: wk.OpString,
                    imms: spv::encode_literal_string(s).collect(),
                },
                result_type_id: None,
                result_id: Some(id),
                ids: [].into_iter().collect(),
            })?;
        }
        for (lang, sources) in &debug_info.source_languages {
            let lang_imms = || {
                [
                    spv::Imm::Short(wk.SourceLanguage, lang.lang),
                    spv::Imm::Short(wk.LiteralInteger, lang.version),
                ]
                .into_iter()
            };
            if sources.file_contents.is_empty() {
                emitter.push_inst(&spv::InstWithIds {
                    without_ids: spv::Inst {
                        opcode: wk.OpSource,
                        imms: lang_imms().collect(),
                    },
                    result_type_id: None,
                    result_id: None,
                    ids: [].into_iter().collect(),
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

                    emitter.push_inst(&spv::InstWithIds {
                        without_ids: spv::Inst {
                            opcode: wk.OpSource,
                            imms: lang_imms()
                                .chain(spv::encode_literal_string(contents_initial))
                                .collect(),
                        },
                        result_type_id: None,
                        result_id: None,
                        ids: iter::once(ids.debug_strings[&cx[file]]).collect(),
                    })?;

                    while !contents_rest.is_empty() {
                        let (cont_chunk, rest) = contents_rest
                            .split_at(contents_rest.len().min(MAX_OP_SOURCE_CONT_CONTENTS_LEN));
                        contents_rest = rest;

                        emitter.push_inst(&spv::InstWithIds {
                            without_ids: spv::Inst {
                                opcode: wk.OpSourceContinued,
                                imms: spv::encode_literal_string(cont_chunk).collect(),
                            },
                            result_type_id: None,
                            result_id: None,
                            ids: [].into_iter().collect(),
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
                let (opcode, imms, ids) = match new_debug_line {
                    Some((file_path_id, line, col)) => (
                        wk.OpLine,
                        [
                            spv::Imm::Short(wk.LiteralInteger, line),
                            spv::Imm::Short(wk.LiteralInteger, col),
                        ]
                        .into_iter()
                        .collect(),
                        iter::once(file_path_id).collect(),
                    ),
                    None => (
                        wk.OpNoLine,
                        [].into_iter().collect(),
                        [].into_iter().collect(),
                    ),
                };
                emitter.push_inst(&spv::InstWithIds {
                    without_ids: spv::Inst { opcode, imms },
                    result_type_id: None,
                    result_id: None,
                    ids,
                })?;
            }
            current_debug_line = new_debug_line;

            emitter.push_inst(&inst)?;
        }

        Ok(emitter)
    }
}
