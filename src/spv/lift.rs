//! SPIR-T to SPIR-V lifting.

use crate::func_at::FuncAt;
use crate::spv::{self, spec};
use crate::visit::{InnerVisit, Visitor};
use crate::{
    cfg, AddrSpace, Attr, AttrSet, Const, ConstCtor, ConstDef, Context, ControlNode,
    ControlNodeKind, ControlNodeOutputDecl, ControlRegion, ControlRegionInputDecl, DataInst,
    DataInstDef, DataInstForm, DataInstFormDef, DataInstKind, DeclDef, EntityList, ExportKey,
    Exportee, Func, FuncDecl, FuncParam, FxIndexMap, FxIndexSet, GlobalVar, GlobalVarDefBody,
    Import, Module, ModuleDebugInfo, ModuleDialect, SelectionKind, Type, TypeCtor, TypeCtorArg,
    TypeDef, Value,
};
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
use std::num::NonZeroU32;
use std::path::Path;
use std::{io, iter, mem, slice};

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
    data_inst_forms_seen: FxIndexSet<DataInstForm>,
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
        let ty_def = &self.cx[ty];
        match ty_def.ctor {
            // FIXME(eddyb) this should be a proper `Result`-based error instead,
            // and/or `spv::lift` should mutate the module for legalization.
            TypeCtor::QPtr => {
                unreachable!("`TypeCtor::QPtr` should be legalized away before lifting");
            }

            TypeCtor::SpvInst(_) => {}
            TypeCtor::SpvStringLiteralForExtInst => {
                unreachable!(
                    "`TypeCtor::SpvStringLiteralForExtInst` should not be used \
                     as a type outside of `ConstCtor::SpvStringLiteralForExtInst`"
                );
            }
        }
        self.visit_type_def(ty_def);
        self.globals.insert(global);
    }
    fn visit_const_use(&mut self, ct: Const) {
        let global = Global::Const(ct);
        if self.globals.contains(&global) {
            return;
        }
        let ct_def = &self.cx[ct];
        match ct_def.ctor {
            ConstCtor::PtrToGlobalVar(_) | ConstCtor::SpvInst(_) => {
                self.visit_const_def(ct_def);
                self.globals.insert(global);
            }

            // HACK(eddyb) because this is an `OpString` and needs to go earlier
            // in the module than any `OpConstant*`, it needs to be special-cased,
            // without visiting its type, or an entry in `self.globals`.
            ConstCtor::SpvStringLiteralForExtInst(s) => {
                let ConstDef {
                    attrs,
                    ty,
                    ctor: _,
                    ctor_args,
                } = ct_def;

                assert!(*attrs == AttrSet::default());
                assert!(
                    self.cx[*ty]
                        == TypeDef {
                            attrs: AttrSet::default(),
                            ctor: TypeCtor::SpvStringLiteralForExtInst,
                            ctor_args: SmallVec::new(),
                        }
                );
                assert!(ctor_args.is_empty());

                self.debug_strings.insert(&self.cx[s]);
            }
        }
    }
    fn visit_data_inst_form_use(&mut self, data_inst_form: DataInstForm) {
        if self.data_inst_forms_seen.insert(data_inst_form) {
            self.visit_data_inst_form_def(&self.cx[data_inst_form]);
        }
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
            Attr::Diagnostics(_)
            | Attr::QPtr(_)
            | Attr::SpvAnnotation { .. }
            | Attr::SpvBitflagsOperand(_) => {}
            Attr::SpvDebugLine { file_path, .. } => {
                self.debug_strings.insert(&self.cx[file_path.0]);
            }
        }
        attr.inner_visit_with(self);
    }

    fn visit_data_inst_form_def(&mut self, data_inst_form_def: &DataInstFormDef) {
        #[allow(clippy::match_same_arms)]
        match data_inst_form_def.kind {
            // FIXME(eddyb) this should be a proper `Result`-based error instead,
            // and/or `spv::lift` should mutate the module for legalization.
            DataInstKind::QPtr(_) => {
                unreachable!("`DataInstKind::QPtr` should be legalized away before lifting");
            }

            DataInstKind::FuncCall(_) => {}

            DataInstKind::SpvInst(_) => {}
            DataInstKind::SpvExtInst { ext_set, .. } => {
                self.ext_inst_imports.insert(&self.cx[ext_set]);
            }
        }
        data_inst_form_def.inner_visit_with(self);
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
    region_inputs_source: FxHashMap<ControlRegion, RegionInputsSource>,
    // FIXME(eddyb) use `EntityOrientedDenseMap` here.
    data_inst_output_ids: FxHashMap<DataInst, spv::Id>,

    label_ids: FxHashMap<CfgPoint, spv::Id>,
    blocks: FxIndexMap<CfgPoint, BlockLifting<'a>>,
}

/// What determines the values for [`Value::ControlRegionInput`]s, for a specific
/// region (effectively the subset of "region parents" that support inputs).
///
/// Note that this is not used when a [`cfg::ControlInst`] has `target_inputs`,
/// and the target [`ControlRegion`] itself has phis for its `inputs`.
enum RegionInputsSource {
    FuncParams,
    LoopHeaderPhis(ControlNode),
}

/// Any of the possible points in structured or unstructured SPIR-T control-flow,
/// that may require a separate SPIR-V basic block.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
enum CfgPoint {
    RegionEntry(ControlRegion),
    RegionExit(ControlRegion),

    ControlNodeEntry(ControlNode),
    ControlNodeExit(ControlNode),
}

struct BlockLifting<'a> {
    phis: SmallVec<[Phi; 2]>,
    insts: SmallVec<[EntityList<DataInst>; 1]>,
    terminator: Terminator<'a>,
}

struct Phi {
    attrs: AttrSet,
    ty: Type,

    result_id: spv::Id,
    cases: FxIndexMap<CfgPoint, Value>,

    // HACK(eddyb) used for `Loop` `initial_inputs`, to indicate that any edge
    // to the `Loop` (other than the backedge, which is already in `cases`)
    // should automatically get an entry into `cases`, with this value.
    default_value: Option<Value>,
}

/// Similar to [`cfg::ControlInst`], except:
/// * `targets` use [`CfgPoint`]s instead of [`ControlRegion`]s, to be able to
///   reach any of the SPIR-V blocks being created during lifting
/// * φ ("phi") values can be provided for targets regardless of "which side" of
///   the structured control-flow they are for ("region input" vs "node output")
/// * optional `merge` (for `OpSelectionMerge`/`OpLoopMerge`)
/// * existing data is borrowed (from the [`FuncDefBody`](crate::FuncDefBody)),
///   wherever possible
struct Terminator<'a> {
    attrs: AttrSet,

    kind: Cow<'a, cfg::ControlInstKind>,

    // FIXME(eddyb) use `Cow` or something, but ideally the "owned" case always
    // has at most one input, so allocating a whole `Vec` for that seems unwise.
    inputs: SmallVec<[Value; 2]>,

    // FIXME(eddyb) change the inline size of this to fit most instructions.
    targets: SmallVec<[CfgPoint; 4]>,

    target_phi_values: FxIndexMap<CfgPoint, &'a [Value]>,

    merge: Option<Merge<CfgPoint>>,
}

#[derive(Copy, Clone)]
enum Merge<L> {
    Selection(L),

    Loop {
        /// The label just after the whole loop, i.e. the `break` target.
        loop_merge: L,

        /// A label that the back-edge block post-dominates, i.e. some point in
        /// the loop body where looping around is inevitable (modulo `break`ing
        /// out of the loop through a `do`-`while`-style conditional back-edge).
        ///
        /// SPIR-V calls this "the `continue` target", but unlike other aspects
        /// of SPIR-V "structured control-flow", there can be multiple valid
        /// choices (any that fit the post-dominator/"inevitability" definition).
        //
        // FIXME(eddyb) https://github.com/EmbarkStudios/spirt/pull/10 tried to
        // set this to the loop body entry, but that may not be valid if the loop
        // body actually diverges, because then the loop body exit will still be
        // post-dominating the back-edge *but* the loop body itself wouldn't have
        // any relationship between its entry and its *unreachable* exit.
        loop_continue: L,
    },
}

impl<'a> NeedsIdsCollector<'a> {
    fn alloc_ids<E>(
        self,
        mut alloc_id: impl FnMut() -> Result<spv::Id, E>,
    ) -> Result<AllocatedIds<'a>, E> {
        let Self {
            cx,
            module,
            ext_inst_imports,
            debug_strings,
            globals,
            data_inst_forms_seen: _,
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
                        FuncLifting::from_func_decl(cx, &module.funcs[func], &mut alloc_id)?,
                    ))
                })
                .collect::<Result<_, _>>()?,
        })
    }
}

/// Helper type for deep traversal of the CFG (as a graph of [`CfgPoint`]s), which
/// tracks the necessary context for navigating a [`ControlRegion`]/[`ControlNode`].
#[derive(Copy, Clone)]
struct CfgCursor<'p, P = CfgPoint> {
    point: P,
    parent: Option<&'p CfgCursor<'p, ControlParent>>,
}

enum ControlParent {
    Region(ControlRegion),
    ControlNode(ControlNode),
}

impl<'a, 'p> FuncAt<'a, CfgCursor<'p>> {
    /// Return the next [`CfgPoint`] (wrapped in [`CfgCursor`]) in a linear
    /// chain within structured control-flow (i.e. no branching to child regions).
    fn unique_successor(self) -> Option<CfgCursor<'p>> {
        let cursor = self.position;
        match cursor.point {
            // Entering a `ControlRegion` enters its first `ControlNode` child,
            // or exits the region right away (if it has no children).
            CfgPoint::RegionEntry(region) => Some(CfgCursor {
                point: match self.at(region).def().children.iter().first {
                    Some(first_child) => CfgPoint::ControlNodeEntry(first_child),
                    None => CfgPoint::RegionExit(region),
                },
                parent: cursor.parent,
            }),

            // Exiting a `ControlRegion` exits its parent `ControlNode`.
            CfgPoint::RegionExit(_) => cursor.parent.map(|parent| match parent.point {
                ControlParent::Region(_) => unreachable!(),
                ControlParent::ControlNode(parent_control_node) => CfgCursor {
                    point: CfgPoint::ControlNodeExit(parent_control_node),
                    parent: parent.parent,
                },
            }),

            // Entering a `ControlNode` depends entirely on the `ControlNodeKind`.
            CfgPoint::ControlNodeEntry(control_node) => match self.at(control_node).def().kind {
                ControlNodeKind::Block { .. } => Some(CfgCursor {
                    point: CfgPoint::ControlNodeExit(control_node),
                    parent: cursor.parent,
                }),

                ControlNodeKind::Select { .. } | ControlNodeKind::Loop { .. } => None,
            },

            // Exiting a `ControlNode` chains to a sibling/parent.
            CfgPoint::ControlNodeExit(control_node) => {
                Some(match self.control_nodes[control_node].next_in_list() {
                    // Enter the next sibling in the `ControlRegion`, if one exists.
                    Some(next_control_node) => CfgCursor {
                        point: CfgPoint::ControlNodeEntry(next_control_node),
                        parent: cursor.parent,
                    },

                    // Exit the parent `ControlRegion`.
                    None => {
                        let parent = cursor.parent.unwrap();
                        match cursor.parent.unwrap().point {
                            ControlParent::Region(parent_region) => CfgCursor {
                                point: CfgPoint::RegionExit(parent_region),
                                parent: parent.parent,
                            },
                            ControlParent::ControlNode(_) => unreachable!(),
                        }
                    }
                })
            }
        }
    }
}

impl<'a> FuncAt<'a, ControlRegion> {
    /// Traverse every [`CfgPoint`] (deeply) contained in this [`ControlRegion`],
    /// in reverse post-order (RPO), with `f` receiving each [`CfgPoint`]
    /// in turn (wrapped in [`CfgCursor`], for further traversal flexibility),
    /// and being able to stop iteration by returning `Err`.
    ///
    /// RPO iteration over a CFG provides certain guarantees, most importantly
    /// that SSA definitions are visited before any of their uses.
    fn rev_post_order_try_for_each<E>(
        self,
        mut f: impl FnMut(CfgCursor<'_>) -> Result<(), E>,
    ) -> Result<(), E> {
        self.rev_post_order_try_for_each_inner(&mut f, None)
    }

    fn rev_post_order_try_for_each_inner<E>(
        self,
        f: &mut impl FnMut(CfgCursor<'_>) -> Result<(), E>,
        parent: Option<&CfgCursor<'_, ControlParent>>,
    ) -> Result<(), E> {
        let region = self.position;
        f(CfgCursor {
            point: CfgPoint::RegionEntry(region),
            parent,
        })?;
        for func_at_control_node in self.at_children() {
            func_at_control_node.rev_post_order_try_for_each_inner(
                f,
                &CfgCursor {
                    point: ControlParent::Region(region),
                    parent,
                },
            )?;
        }
        f(CfgCursor {
            point: CfgPoint::RegionExit(region),
            parent,
        })
    }
}

impl<'a> FuncAt<'a, ControlNode> {
    fn rev_post_order_try_for_each_inner<E>(
        self,
        f: &mut impl FnMut(CfgCursor<'_>) -> Result<(), E>,
        parent: &CfgCursor<'_, ControlParent>,
    ) -> Result<(), E> {
        let child_regions: &[_] = match &self.def().kind {
            ControlNodeKind::Block { .. } => &[],
            ControlNodeKind::Select { cases, .. } => cases,
            ControlNodeKind::Loop { body, .. } => slice::from_ref(body),
        };

        let control_node = self.position;
        let parent = Some(parent);
        f(CfgCursor {
            point: CfgPoint::ControlNodeEntry(control_node),
            parent,
        })?;
        for &region in child_regions {
            self.at(region).rev_post_order_try_for_each_inner(
                f,
                Some(&CfgCursor {
                    point: ControlParent::ControlNode(control_node),
                    parent,
                }),
            )?;
        }
        f(CfgCursor {
            point: CfgPoint::ControlNodeExit(control_node),
            parent,
        })
    }
}

impl<'a> FuncLifting<'a> {
    fn from_func_decl<E>(
        cx: &Context,
        func_decl: &'a FuncDecl,
        mut alloc_id: impl FnMut() -> Result<spv::Id, E>,
    ) -> Result<Self, E> {
        let wk = &spec::Spec::get().well_known;

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
                    region_inputs_source: Default::default(),
                    data_inst_output_ids: Default::default(),
                    label_ids: Default::default(),
                    blocks: Default::default(),
                });
            }
            DeclDef::Present(def) => def,
        };

        let mut region_inputs_source = FxHashMap::default();
        region_inputs_source.insert(func_def_body.body, RegionInputsSource::FuncParams);

        // Create a SPIR-V block for every CFG point needing one.
        let mut blocks = FxIndexMap::default();
        let mut visit_cfg_point = |point_cursor: CfgCursor<'_>| {
            let point = point_cursor.point;

            let phis = match point {
                CfgPoint::RegionEntry(region) => {
                    if region_inputs_source.contains_key(&region) {
                        // Region inputs handled by the parent of the region.
                        SmallVec::new()
                    } else {
                        func_def_body
                            .at(region)
                            .def()
                            .inputs
                            .iter()
                            .map(|&ControlRegionInputDecl { attrs, ty }| {
                                Ok(Phi {
                                    attrs,
                                    ty,

                                    result_id: alloc_id()?,
                                    cases: FxIndexMap::default(),
                                    default_value: None,
                                })
                            })
                            .collect::<Result<_, _>>()?
                    }
                }
                CfgPoint::RegionExit(_) => SmallVec::new(),

                CfgPoint::ControlNodeEntry(control_node) => {
                    match &func_def_body.at(control_node).def().kind {
                        // The backedge of a SPIR-V structured loop points to
                        // the "loop header", i.e. the `Entry` of the `Loop`,
                        // so that's where `body` `inputs` phis have to go.
                        ControlNodeKind::Loop {
                            initial_inputs,
                            body,
                            ..
                        } => {
                            let loop_body_def = func_def_body.at(*body).def();
                            let loop_body_inputs = &loop_body_def.inputs;

                            if !loop_body_inputs.is_empty() {
                                region_inputs_source.insert(
                                    *body,
                                    RegionInputsSource::LoopHeaderPhis(control_node),
                                );
                            }

                            loop_body_inputs
                                .iter()
                                .enumerate()
                                .map(|(i, &ControlRegionInputDecl { attrs, ty })| {
                                    Ok(Phi {
                                        attrs,
                                        ty,

                                        result_id: alloc_id()?,
                                        cases: FxIndexMap::default(),
                                        default_value: Some(initial_inputs[i]),
                                    })
                                })
                                .collect::<Result<_, _>>()?
                        }
                        _ => SmallVec::new(),
                    }
                }
                CfgPoint::ControlNodeExit(control_node) => func_def_body
                    .at(control_node)
                    .def()
                    .outputs
                    .iter()
                    .map(|&ControlNodeOutputDecl { attrs, ty }| {
                        Ok(Phi {
                            attrs,
                            ty,

                            result_id: alloc_id()?,
                            cases: FxIndexMap::default(),
                            default_value: None,
                        })
                    })
                    .collect::<Result<_, _>>()?,
            };

            let insts = match point {
                CfgPoint::ControlNodeEntry(control_node) => {
                    match func_def_body.at(control_node).def().kind {
                        ControlNodeKind::Block { insts } => [insts].into_iter().collect(),
                        _ => SmallVec::new(),
                    }
                }
                _ => SmallVec::new(),
            };

            // Get the terminator, or reconstruct it from structured control-flow.
            let terminator = match (point, func_def_body.at(point_cursor).unique_successor()) {
                // Exiting a `ControlRegion` w/o a structured parent.
                (CfgPoint::RegionExit(region), None) => {
                    let unstructured_terminator = func_def_body
                        .unstructured_cfg
                        .as_ref()
                        .and_then(|cfg| cfg.control_inst_on_exit_from.get(region));
                    if let Some(terminator) = unstructured_terminator {
                        let cfg::ControlInst {
                            attrs,
                            kind,
                            inputs,
                            targets,
                            target_inputs,
                        } = terminator;
                        Terminator {
                            attrs: *attrs,
                            kind: Cow::Borrowed(kind),
                            // FIXME(eddyb) borrow these whenever possible.
                            inputs: inputs.clone(),
                            targets: targets
                                .iter()
                                .map(|&target| CfgPoint::RegionEntry(target))
                                .collect(),
                            target_phi_values: target_inputs
                                .iter()
                                .map(|(&target, target_inputs)| {
                                    (CfgPoint::RegionEntry(target), &target_inputs[..])
                                })
                                .collect(),
                            merge: None,
                        }
                    } else {
                        // Structured return out of the function body.
                        assert!(region == func_def_body.body);
                        Terminator {
                            attrs: AttrSet::default(),
                            kind: Cow::Owned(cfg::ControlInstKind::Return),
                            inputs: func_def_body.at_body().def().outputs.clone(),
                            targets: [].into_iter().collect(),
                            target_phi_values: FxIndexMap::default(),
                            merge: None,
                        }
                    }
                }

                // Entering a `ControlNode` with child `ControlRegion`s.
                (CfgPoint::ControlNodeEntry(control_node), None) => {
                    let control_node_def = func_def_body.at(control_node).def();
                    match &control_node_def.kind {
                        ControlNodeKind::Block { .. } => {
                            unreachable!()
                        }

                        ControlNodeKind::Select {
                            kind,
                            scrutinee,
                            cases,
                        } => Terminator {
                            attrs: AttrSet::default(),
                            kind: Cow::Owned(cfg::ControlInstKind::SelectBranch(kind.clone())),
                            inputs: [*scrutinee].into_iter().collect(),
                            targets: cases
                                .iter()
                                .map(|&case| CfgPoint::RegionEntry(case))
                                .collect(),
                            target_phi_values: FxIndexMap::default(),
                            merge: Some(Merge::Selection(CfgPoint::ControlNodeExit(control_node))),
                        },

                        ControlNodeKind::Loop {
                            initial_inputs: _,
                            body,
                            repeat_condition: _,
                        } => Terminator {
                            attrs: AttrSet::default(),
                            kind: Cow::Owned(cfg::ControlInstKind::Branch),
                            inputs: [].into_iter().collect(),
                            targets: [CfgPoint::RegionEntry(*body)].into_iter().collect(),
                            target_phi_values: FxIndexMap::default(),
                            merge: Some(Merge::Loop {
                                loop_merge: CfgPoint::ControlNodeExit(control_node),
                                // NOTE(eddyb) see the note on `Merge::Loop`'s
                                // `loop_continue` field - in particular, for
                                // SPIR-T loops, we *could* pick any point
                                // before/after/between `body`'s `children`
                                // and it should be valid *but* that had to be
                                // reverted because it's only true in the absence
                                // of divergence within the loop body itself!
                                loop_continue: CfgPoint::RegionExit(*body),
                            }),
                        },
                    }
                }

                // Exiting a `ControlRegion` to the parent `ControlNode`.
                (CfgPoint::RegionExit(region), Some(parent_exit_cursor)) => {
                    let region_outputs = Some(&func_def_body.at(region).def().outputs[..])
                        .filter(|outputs| !outputs.is_empty());

                    let parent_exit = parent_exit_cursor.point;
                    let parent_node = match parent_exit {
                        CfgPoint::ControlNodeExit(parent_node) => parent_node,
                        _ => unreachable!(),
                    };

                    match func_def_body.at(parent_node).def().kind {
                        ControlNodeKind::Block { .. } => {
                            unreachable!()
                        }

                        ControlNodeKind::Select { .. } => Terminator {
                            attrs: AttrSet::default(),
                            kind: Cow::Owned(cfg::ControlInstKind::Branch),
                            inputs: [].into_iter().collect(),
                            targets: [parent_exit].into_iter().collect(),
                            target_phi_values: region_outputs
                                .map(|outputs| (parent_exit, outputs))
                                .into_iter()
                                .collect(),
                            merge: None,
                        },

                        ControlNodeKind::Loop {
                            initial_inputs: _,
                            body: _,
                            repeat_condition,
                        } => {
                            let backedge = CfgPoint::ControlNodeEntry(parent_node);
                            let target_phi_values = region_outputs
                                .map(|outputs| (backedge, outputs))
                                .into_iter()
                                .collect();

                            let is_infinite_loop = match repeat_condition {
                                Value::Const(cond) => {
                                    cx[cond].ctor == ConstCtor::SpvInst(wk.OpConstantTrue.into())
                                }

                                _ => false,
                            };
                            if is_infinite_loop {
                                Terminator {
                                    attrs: AttrSet::default(),
                                    kind: Cow::Owned(cfg::ControlInstKind::Branch),
                                    inputs: [].into_iter().collect(),
                                    targets: [backedge].into_iter().collect(),
                                    target_phi_values,
                                    merge: None,
                                }
                            } else {
                                Terminator {
                                    attrs: AttrSet::default(),
                                    kind: Cow::Owned(cfg::ControlInstKind::SelectBranch(
                                        SelectionKind::BoolCond,
                                    )),
                                    inputs: [repeat_condition].into_iter().collect(),
                                    targets: [backedge, parent_exit].into_iter().collect(),
                                    target_phi_values,
                                    merge: None,
                                }
                            }
                        }
                    }
                }

                // Siblings in the same `ControlRegion` (including the
                // implied edge from a `Block`'s `Entry` to its `Exit`).
                (_, Some(succ_cursor)) => Terminator {
                    attrs: AttrSet::default(),
                    kind: Cow::Owned(cfg::ControlInstKind::Branch),
                    inputs: [].into_iter().collect(),
                    targets: [succ_cursor.point].into_iter().collect(),
                    target_phi_values: FxIndexMap::default(),
                    merge: None,
                },

                // Impossible cases, they always return `(_, Some(_))`.
                (CfgPoint::RegionEntry(_) | CfgPoint::ControlNodeExit(_), None) => {
                    unreachable!()
                }
            };

            blocks.insert(
                point,
                BlockLifting {
                    phis,
                    insts,
                    terminator,
                },
            );

            Ok(())
        };
        match &func_def_body.unstructured_cfg {
            None => func_def_body
                .at_body()
                .rev_post_order_try_for_each(visit_cfg_point)?,
            Some(cfg) => {
                for region in cfg.rev_post_order(func_def_body) {
                    func_def_body
                        .at(region)
                        .rev_post_order_try_for_each(&mut visit_cfg_point)?;
                }
            }
        }

        // Count the number of "uses" of each block (each incoming edge, plus
        // `1` for the entry block), to help determine which blocks are part
        // of a linear branch chain (and potentially fusable), later on.
        //
        // FIXME(eddyb) use `EntityOrientedDenseMap` here.
        let mut use_counts = FxHashMap::default();
        use_counts.reserve(blocks.len());
        let all_edges = blocks
            .first()
            .map(|(&entry_point, _)| entry_point)
            .into_iter()
            .chain(blocks.values().flat_map(|block| {
                block
                    .terminator
                    .merge
                    .iter()
                    .flat_map(|merge| {
                        let (a, b) = match merge {
                            Merge::Selection(a) => (a, None),
                            Merge::Loop {
                                loop_merge: a,
                                loop_continue: b,
                            } => (a, Some(b)),
                        };
                        [a].into_iter().chain(b)
                    })
                    .chain(&block.terminator.targets)
                    .copied()
            }));
        for target in all_edges {
            *use_counts.entry(target).or_default() += 1;
        }

        // Fuse chains of linear branches, when there is no information being
        // lost by the fusion. This is done in reverse order, so that in e.g.
        // `a -> b -> c`, `b -> c` is fused first, then when the iteration
        // reaches `a`, it sees `a -> bc` and can further fuse that into one
        // `abc` block, without knowing about `b` and `c` themselves
        // (this is possible because RPO will always output `[a, b, c]`, when
        // `b` and `c` only have one predecessor each).
        //
        // FIXME(eddyb) while this could theoretically fuse certain kinds of
        // merge blocks (mostly loop bodies) into their unique precedessor, that
        // would require adjusting the `Merge` that points to them.
        //
        // HACK(eddyb) this takes advantage of `blocks` being an `IndexMap`,
        // to iterate at the same time as mutating other entries.
        for block_idx in (0..blocks.len()).rev() {
            let BlockLifting {
                terminator: original_terminator,
                ..
            } = &blocks[block_idx];

            let is_trivial_branch = {
                let Terminator {
                    attrs,
                    kind,
                    inputs,
                    targets,
                    target_phi_values,
                    merge,
                } = original_terminator;

                *attrs == AttrSet::default()
                    && matches!(**kind, cfg::ControlInstKind::Branch)
                    && inputs.is_empty()
                    && targets.len() == 1
                    && target_phi_values.is_empty()
                    && merge.is_none()
            };

            if is_trivial_branch {
                let target = original_terminator.targets[0];
                let target_use_count = use_counts.get_mut(&target).unwrap();

                if *target_use_count == 1 {
                    let BlockLifting {
                        phis: ref target_phis,
                        insts: ref mut extra_insts,
                        terminator: ref mut new_terminator,
                    } = blocks[&target];

                    // FIXME(eddyb) check for block-level attributes, once/if
                    // they start being tracked.
                    if target_phis.is_empty() {
                        let extra_insts = mem::take(extra_insts);
                        let new_terminator = mem::replace(
                            new_terminator,
                            Terminator {
                                attrs: Default::default(),
                                kind: Cow::Owned(cfg::ControlInstKind::Unreachable),
                                inputs: Default::default(),
                                targets: Default::default(),
                                target_phi_values: Default::default(),
                                merge: None,
                            },
                        );
                        *target_use_count = 0;

                        let combined_block = &mut blocks[block_idx];
                        combined_block.insts.extend(extra_insts);
                        combined_block.terminator = new_terminator;
                    }
                }
            }
        }

        // Remove now-unused blocks.
        blocks.retain(|point, _| use_counts[point] > 0);

        // Collect `OpPhi`s from other blocks' edges into each block.
        //
        // HACK(eddyb) this takes advantage of `blocks` being an `IndexMap`,
        // to iterate at the same time as mutating other entries.
        for source_block_idx in 0..blocks.len() {
            let (&source_point, source_block) = blocks.get_index(source_block_idx).unwrap();
            let targets = source_block.terminator.targets.clone();

            for target in targets {
                let source_values = {
                    let (_, source_block) = blocks.get_index(source_block_idx).unwrap();
                    source_block
                        .terminator
                        .target_phi_values
                        .get(&target)
                        .copied()
                };
                let target_block = blocks.get_mut(&target).unwrap();
                for (i, target_phi) in target_block.phis.iter_mut().enumerate() {
                    use indexmap::map::Entry;

                    let source_value = source_values
                        .map(|values| values[i])
                        .or(target_phi.default_value)
                        .unwrap();
                    match target_phi.cases.entry(source_point) {
                        Entry::Vacant(entry) => {
                            entry.insert(source_value);
                        }

                        // NOTE(eddyb) the only reason duplicates are allowed,
                        // is that `targets` may itself contain the same target
                        // multiple times (which would result in the same value).
                        Entry::Occupied(entry) => {
                            assert!(*entry.get() == source_value);
                        }
                    }
                }
            }
        }

        let all_insts_with_output = blocks
            .values()
            .flat_map(|block| block.insts.iter().copied())
            .flat_map(|insts| func_def_body.at(insts))
            .filter(|&func_at_inst| cx[func_at_inst.def().form].output_type.is_some())
            .map(|func_at_inst| func_at_inst.position);

        Ok(Self {
            func_id,
            param_ids,
            region_inputs_source,
            data_inst_output_ids: all_insts_with_output
                .map(|inst| Ok((inst, alloc_id()?)))
                .collect::<Result<_, _>>()?,
            label_ids: blocks
                .keys()
                .map(|&point| Ok((point, alloc_id()?)))
                .collect::<Result<_, _>>()?,
            blocks,
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
    Merge(Merge<spv::Id>),
    Terminator {
        parent_func: &'b FuncLifting<'a>,
        terminator: &'b Terminator<'a>,
    },
    OpFunctionEnd,
}

impl LazyInst<'_, '_> {
    fn result_id_attrs_and_import(
        self,
        module: &Module,
        ids: &AllocatedIds<'_>,
    ) -> (Option<spv::Id>, AttrSet, Option<Import>) {
        let cx = module.cx_ref();

        #[allow(clippy::match_same_arms)]
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

                            // Not inserted into `globals` while visiting.
                            ConstCtor::SpvStringLiteralForExtInst(_) => unreachable!(),
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
            } => (Some(phi.result_id), phi.attrs, None),
            Self::DataInst {
                parent_func: _,
                result_id,
                data_inst_def,
            } => (result_id, data_inst_def.attrs, None),
            Self::Merge(_) => (None, AttrSet::default(), None),
            Self::Terminator {
                parent_func: _,
                terminator,
            } => (None, terminator.attrs, None),
            Self::OpFunctionEnd => (None, AttrSet::default(), None),
        }
    }

    fn to_inst_and_attrs(
        self,
        module: &Module,
        ids: &AllocatedIds<'_>,
    ) -> (spv::InstWithIds, AttrSet) {
        let wk = &spec::Spec::get().well_known;
        let cx = module.cx_ref();

        let value_to_id = |parent_func: &FuncLifting<'_>, v| match v {
            Value::Const(ct) => match cx[ct].ctor {
                ConstCtor::SpvStringLiteralForExtInst(s) => ids.debug_strings[&cx[s]],

                _ => ids.globals[&Global::Const(ct)],
            },
            Value::ControlRegionInput { region, input_idx } => {
                let input_idx = usize::try_from(input_idx).unwrap();
                match parent_func.region_inputs_source.get(&region) {
                    Some(RegionInputsSource::FuncParams) => parent_func.param_ids[input_idx],
                    Some(&RegionInputsSource::LoopHeaderPhis(loop_node)) => {
                        parent_func.blocks[&CfgPoint::ControlNodeEntry(loop_node)].phis[input_idx]
                            .result_id
                    }
                    None => {
                        parent_func.blocks[&CfgPoint::RegionEntry(region)].phis[input_idx].result_id
                    }
                }
            }
            Value::ControlNodeOutput {
                control_node,
                output_idx,
            } => {
                parent_func.blocks[&CfgPoint::ControlNodeExit(control_node)].phis
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

                        // Not inserted into `globals` while visiting.
                        TypeCtor::QPtr | TypeCtor::SpvStringLiteralForExtInst => unreachable!(),
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
                                AddrSpace::Handles => {
                                    unreachable!(
                                        "`AddrSpace::Handles` should be legalized away before lifting"
                                    );
                                }
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

                        // Not inserted into `globals` while visiting.
                        ConstCtor::SpvStringLiteralForExtInst(_) => unreachable!(),
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
                result_type_id: Some(ids.globals[&Global::Type(phi.ty)]),
                result_id: Some(phi.result_id),
                ids: phi
                    .cases
                    .iter()
                    .flat_map(|(&source_point, &v)| {
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
                let DataInstFormDef { kind, output_type } = &cx[data_inst_def.form];
                let (inst, extra_initial_id_operand) = match kind {
                    // Disallowed while visiting.
                    DataInstKind::QPtr(_) => unreachable!(),

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
                    result_type_id: output_type.map(|ty| ids.globals[&Global::Type(ty)]),
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
            Self::Merge(Merge::Selection(merge_label_id)) => spv::InstWithIds {
                without_ids: spv::Inst {
                    opcode: wk.OpSelectionMerge,
                    imms: [spv::Imm::Short(wk.SelectionControl, 0)]
                        .into_iter()
                        .collect(),
                },
                result_type_id: None,
                result_id: None,
                ids: [merge_label_id].into_iter().collect(),
            },
            Self::Merge(Merge::Loop {
                loop_merge: merge_label_id,
                loop_continue: continue_label_id,
            }) => spv::InstWithIds {
                without_ids: spv::Inst {
                    opcode: wk.OpLoopMerge,
                    imms: [spv::Imm::Short(wk.LoopControl, 0)].into_iter().collect(),
                },
                result_type_id: None,
                result_id: None,
                ids: [merge_label_id, continue_label_id].into_iter().collect(),
            },
            Self::Terminator {
                parent_func,
                terminator,
            } => {
                let inst = match &*terminator.kind {
                    cfg::ControlInstKind::Unreachable => wk.OpUnreachable.into(),
                    cfg::ControlInstKind::Return => {
                        if terminator.inputs.is_empty() {
                            wk.OpReturn.into()
                        } else {
                            wk.OpReturnValue.into()
                        }
                    }
                    cfg::ControlInstKind::ExitInvocation(cfg::ExitInvocationKind::SpvInst(
                        inst,
                    )) => inst.clone(),

                    cfg::ControlInstKind::Branch => wk.OpBranch.into(),

                    cfg::ControlInstKind::SelectBranch(SelectionKind::BoolCond) => {
                        wk.OpBranchConditional.into()
                    }
                    cfg::ControlInstKind::SelectBranch(SelectionKind::SpvInst(inst)) => {
                        inst.clone()
                    }
                };
                spv::InstWithIds {
                    without_ids: inst,
                    result_type_id: None,
                    result_id: None,
                    ids: terminator
                        .inputs
                        .iter()
                        .map(|&v| value_to_id(parent_func, v))
                        .chain(
                            terminator
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
            data_inst_forms_seen: FxIndexSet::default(),
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
                            label_id: func_lifting.label_ids[point],
                        })
                        .chain(phis.iter().map(|phi| LazyInst::OpPhi {
                            parent_func: func_lifting,
                            phi,
                        }))
                        .chain(
                            insts
                                .iter()
                                .copied()
                                .flat_map(move |insts| func_def_body.unwrap().at(insts))
                                .map(move |func_at_inst| {
                                    let data_inst_def = func_at_inst.def();
                                    LazyInst::DataInst {
                                        parent_func: func_lifting,
                                        result_id: cx[data_inst_def.form].output_type.map(|_| {
                                            func_lifting.data_inst_output_ids
                                                [&func_at_inst.position]
                                        }),
                                        data_inst_def,
                                    }
                                }),
                        )
                        .chain(terminator.merge.map(|merge| {
                            LazyInst::Merge(match merge {
                                Merge::Selection(merge) => {
                                    Merge::Selection(func_lifting.label_ids[&merge])
                                }
                                Merge::Loop {
                                    loop_merge,
                                    loop_continue,
                                } => Merge::Loop {
                                    loop_merge: func_lifting.label_ids[&loop_merge],
                                    loop_continue: func_lifting.label_ids[&loop_continue],
                                },
                            })
                        }))
                        .chain([LazyInst::Terminator {
                            parent_func: func_lifting,
                            terminator,
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
            let (result_id, attrs, import) = lazy_inst.result_id_attrs_and_import(self, ids);

            for attr in cx[attrs].attrs.iter() {
                match attr {
                    Attr::Diagnostics(_)
                    | Attr::QPtr(_)
                    | Attr::SpvDebugLine { .. }
                    | Attr::SpvBitflagsOperand(_) => {}
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

                        if [wk.OpExecutionMode, wk.OpExecutionModeId].contains(opcode) {
                            execution_mode_insts.push(inst);
                        } else if [wk.OpName, wk.OpMemberName].contains(opcode) {
                            debug_name_insts.push(inst);
                        } else {
                            decoration_insts.push(inst);
                        }
                    }
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
                        // FIXME(eddyb) test with UTF-8! this `split_at` should
                        // actually take *less* than the full possible size, to
                        // avoid cutting a UTF-8 sequence.
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
            let (inst, attrs) = lazy_inst.to_inst_and_attrs(self, ids);

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
