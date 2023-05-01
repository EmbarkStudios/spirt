use crate::transform::{InnerTransform, Transformed, Transformer};
use crate::visit::{InnerVisit, Visitor};
use crate::{
    AttrSet, Const, Context, DataInstForm, DeclDef, ExportKey, Exportee, Func, FxIndexSet,
    GlobalVar, Import, Module, Type,
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::VecDeque;

// FIXME(eddyb) maybe make an export pruning pass that keeps some exports as
// roots and then only other exports if they're used by imports.

/// Remove exports which aren't "roots" (`is_root(export_key)` returns `false`),
/// and which aren't otherwise kept alive by a "root" (through [`Import::LinkName`]
/// declarations, with `name` matching [`ExportKey::LinkName`]), either directly
/// or transitively (including through any number of imports).
///
/// In essence, other than the "root" exports, `minimize_exports` only keeps the
/// exports that `resolve_imports` would use, and is recommended to first call
/// `minimize_exports` before using [`resolve_imports`], to reduce work.
///
/// Note that the "dead" definitions are not removed from the module, and any
/// external references to them could still be used (e.g. from a clone of the
/// `module.exports` map, before calling `minimize_exports`).
//
// FIXME(eddyb) make this operate on multiple modules.
pub fn minimize_exports(module: &mut Module, is_root: impl Fn(&ExportKey) -> bool) {
    let mut collector = LiveExportCollector {
        cx: module.cx_ref(),
        module,

        live_exports: FxIndexSet::default(),

        seen_types: FxHashSet::default(),
        seen_consts: FxHashSet::default(),
        seen_data_inst_forms: FxHashSet::default(),
        seen_global_vars: FxHashSet::default(),
        seen_funcs: FxHashSet::default(),
    };
    for (export_key, &exportee) in &module.exports {
        if is_root(export_key) && collector.live_exports.insert(export_key.clone()) {
            exportee.inner_visit_with(&mut collector);
        }
    }
    module.exports = collector
        .live_exports
        .into_iter()
        .map(|export_key| {
            let exportee = module.exports[&export_key];
            (export_key, exportee)
        })
        .collect();
}

struct LiveExportCollector<'a> {
    cx: &'a Context,
    module: &'a Module,

    live_exports: FxIndexSet<ExportKey>,

    // FIXME(eddyb) build some automation to avoid ever repeating these.
    seen_types: FxHashSet<Type>,
    seen_consts: FxHashSet<Const>,
    seen_data_inst_forms: FxHashSet<DataInstForm>,
    seen_global_vars: FxHashSet<GlobalVar>,
    seen_funcs: FxHashSet<Func>,
}

impl Visitor<'_> for LiveExportCollector<'_> {
    // FIXME(eddyb) build some automation to avoid ever repeating these.
    fn visit_attr_set_use(&mut self, _attrs: AttrSet) {
        // FIXME(eddyb) if `AttrSet`s are ignored, why not `Type`s too?
    }
    fn visit_type_use(&mut self, ty: Type) {
        if self.seen_types.insert(ty) {
            self.visit_type_def(&self.cx[ty]);
        }
    }
    fn visit_const_use(&mut self, ct: Const) {
        if self.seen_consts.insert(ct) {
            self.visit_const_def(&self.cx[ct]);
        }
    }
    fn visit_data_inst_form_use(&mut self, data_inst_form: DataInstForm) {
        if self.seen_data_inst_forms.insert(data_inst_form) {
            self.visit_data_inst_form_def(&self.cx[data_inst_form]);
        }
    }

    fn visit_global_var_use(&mut self, gv: GlobalVar) {
        if self.seen_global_vars.insert(gv) {
            self.visit_global_var_decl(&self.module.global_vars[gv]);
        }
    }
    fn visit_func_use(&mut self, func: Func) {
        if self.seen_funcs.insert(func) {
            self.visit_func_decl(&self.module.funcs[func]);
        }
    }

    fn visit_import(&mut self, import: &Import) {
        match *import {
            Import::LinkName(name) => {
                let export_key = ExportKey::LinkName(name);
                if let Some(&exportee) = self.module.exports.get(&export_key) {
                    if self.live_exports.insert(export_key) {
                        exportee.inner_visit_with(self);
                    }
                }
            }
        }
    }
}

/// Remap [`Import::LinkName`] to definitions exported as [`ExportKey::LinkName`].
///
/// To reduce the work performed, calling [`minimize_exports`] first is recommended.
//
// FIXME(eddyb) make this operate on multiple modules.
pub fn resolve_imports(module: &mut Module) {
    let (resolved_global_vars, resolved_funcs) = {
        let mut collector = ImportResolutionCollector {
            cx: module.cx_ref(),
            module,

            resolved_global_vars: FxHashMap::default(),
            resolved_funcs: FxHashMap::default(),

            seen_types: FxHashSet::default(),
            seen_consts: FxHashSet::default(),
            seen_data_inst_forms: FxHashSet::default(),
            seen_global_vars: FxHashSet::default(),
            seen_funcs: FxHashSet::default(),
        };
        collector.visit_module(module);
        (collector.resolved_global_vars, collector.resolved_funcs)
    };

    let mut resolver = ImportResolver {
        cx: &module.cx(),

        resolved_global_vars: &resolved_global_vars,
        resolved_funcs: &resolved_funcs,

        transformed_types: FxHashMap::default(),
        transformed_consts: FxHashMap::default(),
        transformed_data_inst_forms: FxHashMap::default(),
        transformed_global_vars: FxHashMap::default(),
        global_var_queue: VecDeque::new(),
        transformed_funcs: FxHashMap::default(),
        func_queue: VecDeque::new(),
    };

    // Seed the queues starting from the module exports.
    for exportee in module.exports.values_mut() {
        exportee
            .inner_transform_with(&mut resolver)
            .apply_to(exportee);
    }

    // Process the queues until they're all empty.
    while !resolver.global_var_queue.is_empty() || !resolver.func_queue.is_empty() {
        while let Some(gv) = resolver.global_var_queue.pop_front() {
            resolver.in_place_transform_global_var_decl(&mut module.global_vars[gv]);
        }
        while let Some(func) = resolver.func_queue.pop_front() {
            resolver.in_place_transform_func_decl(&mut module.funcs[func]);
        }
    }
}

// FIXME(eddyb) figure out if this step can be skipped by somehow letting
// `ImportResolver` access declarations while mutating definitions.
struct ImportResolutionCollector<'a> {
    cx: &'a Context,
    module: &'a Module,

    resolved_global_vars: FxHashMap<GlobalVar, GlobalVar>,
    resolved_funcs: FxHashMap<Func, Func>,

    // FIXME(eddyb) build some automation to avoid ever repeating these.
    seen_types: FxHashSet<Type>,
    seen_consts: FxHashSet<Const>,
    seen_data_inst_forms: FxHashSet<DataInstForm>,
    seen_global_vars: FxHashSet<GlobalVar>,
    seen_funcs: FxHashSet<Func>,
}

impl Visitor<'_> for ImportResolutionCollector<'_> {
    // FIXME(eddyb) build some automation to avoid ever repeating these.
    fn visit_attr_set_use(&mut self, _attrs: AttrSet) {
        // FIXME(eddyb) if `AttrSet`s are ignored, why not `Type`s too?
    }
    fn visit_type_use(&mut self, ty: Type) {
        if self.seen_types.insert(ty) {
            self.visit_type_def(&self.cx[ty]);
        }
    }
    fn visit_const_use(&mut self, ct: Const) {
        if self.seen_consts.insert(ct) {
            self.visit_const_def(&self.cx[ct]);
        }
    }
    fn visit_data_inst_form_use(&mut self, data_inst_form: DataInstForm) {
        if self.seen_data_inst_forms.insert(data_inst_form) {
            self.visit_data_inst_form_def(&self.cx[data_inst_form]);
        }
    }

    fn visit_global_var_use(&mut self, gv: GlobalVar) {
        if self.seen_global_vars.insert(gv) {
            let gv_decl = &self.module.global_vars[gv];
            self.visit_global_var_decl(gv_decl);

            // FIXME(eddyb) if the export is missing (or the wrong kind), it will
            // simply not get remapped - perhaps some kind of diagnostic is in
            // order? (maybe an entire pass infrastructure that can report errors)
            if let DeclDef::Imported(Import::LinkName(name)) = gv_decl.def {
                if let Some(&Exportee::GlobalVar(def_gv)) =
                    self.module.exports.get(&ExportKey::LinkName(name))
                {
                    self.resolved_global_vars.insert(gv, def_gv);
                }
            }
        }
    }
    fn visit_func_use(&mut self, func: Func) {
        if self.seen_funcs.insert(func) {
            let func_decl = &self.module.funcs[func];
            self.visit_func_decl(func_decl);

            // FIXME(eddyb) if the export is missing (or the wrong kind), it will
            // simply not get remapped - perhaps some kind of diagnostic is in
            // order? (maybe an entire pass infrastructure that can report errors)
            if let DeclDef::Imported(Import::LinkName(name)) = func_decl.def {
                if let Some(&Exportee::Func(def_func)) =
                    self.module.exports.get(&ExportKey::LinkName(name))
                {
                    self.resolved_funcs.insert(func, def_func);
                }
            }
        }
    }
}

struct ImportResolver<'a> {
    cx: &'a Context,

    resolved_global_vars: &'a FxHashMap<GlobalVar, GlobalVar>,
    resolved_funcs: &'a FxHashMap<Func, Func>,

    // FIXME(eddyb) build some automation to avoid ever repeating these.
    transformed_types: FxHashMap<Type, Transformed<Type>>,
    transformed_consts: FxHashMap<Const, Transformed<Const>>,
    transformed_data_inst_forms: FxHashMap<DataInstForm, Transformed<DataInstForm>>,
    transformed_global_vars: FxHashMap<GlobalVar, Transformed<GlobalVar>>,
    global_var_queue: VecDeque<GlobalVar>,
    transformed_funcs: FxHashMap<Func, Transformed<Func>>,
    func_queue: VecDeque<Func>,
}

impl Transformer for ImportResolver<'_> {
    // FIXME(eddyb) build some automation to avoid ever repeating these.
    fn transform_type_use(&mut self, ty: Type) -> Transformed<Type> {
        if let Some(&cached) = self.transformed_types.get(&ty) {
            return cached;
        }
        let transformed = self
            .transform_type_def(&self.cx[ty])
            .map(|ty_def| self.cx.intern(ty_def));
        self.transformed_types.insert(ty, transformed);
        transformed
    }
    fn transform_const_use(&mut self, ct: Const) -> Transformed<Const> {
        if let Some(&cached) = self.transformed_consts.get(&ct) {
            return cached;
        }
        let transformed = self
            .transform_const_def(&self.cx[ct])
            .map(|ct_def| self.cx.intern(ct_def));
        self.transformed_consts.insert(ct, transformed);
        transformed
    }
    fn transform_data_inst_form_use(
        &mut self,
        data_inst_form: DataInstForm,
    ) -> Transformed<DataInstForm> {
        if let Some(&cached) = self.transformed_data_inst_forms.get(&data_inst_form) {
            return cached;
        }
        let transformed = self
            .transform_data_inst_form_def(&self.cx[data_inst_form])
            .map(|data_inst_form_def| self.cx.intern(data_inst_form_def));
        self.transformed_data_inst_forms
            .insert(data_inst_form, transformed);
        transformed
    }

    fn transform_global_var_use(&mut self, gv: GlobalVar) -> Transformed<GlobalVar> {
        if let Some(&cached) = self.transformed_global_vars.get(&gv) {
            return cached;
        }
        let transformed = match self.resolved_global_vars.get(&gv).copied() {
            Some(mut new_gv) => {
                self.transform_global_var_use(new_gv).apply_to(&mut new_gv);
                Transformed::Changed(new_gv)
            }
            None => {
                self.global_var_queue.push_back(gv);
                Transformed::Unchanged
            }
        };
        self.transformed_global_vars.insert(gv, transformed);
        transformed
    }
    fn transform_func_use(&mut self, func: Func) -> Transformed<Func> {
        if let Some(&cached) = self.transformed_funcs.get(&func) {
            return cached;
        }
        let transformed = match self.resolved_funcs.get(&func).copied() {
            Some(mut new_func) => {
                self.transform_func_use(new_func).apply_to(&mut new_func);
                Transformed::Changed(new_func)
            }
            None => {
                self.func_queue.push_back(func);
                Transformed::Unchanged
            }
        };
        self.transformed_funcs.insert(func, transformed);
        transformed
    }
}
