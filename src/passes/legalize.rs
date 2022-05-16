use crate::visit::{InnerVisit, Visitor};
use crate::{cfg, AttrSet, Const, Context, DeclDef, Func, FxIndexSet, GlobalVar, Module, Type};

/// Apply the `cfg::Structurize` algorithm to all function definitions in `module`.
pub fn structurize_func_cfgs(module: &mut Module) {
    let cx = &module.cx();

    // FIXME(eddyb) reuse this collection work in some kind of "pass manager".
    let mut collector = ReachableUseCollector {
        cx,
        module,

        seen_types: FxIndexSet::default(),
        seen_consts: FxIndexSet::default(),
        seen_global_vars: FxIndexSet::default(),
        seen_funcs: FxIndexSet::default(),
    };
    for &exportee in module.exports.values() {
        exportee.inner_visit_with(&mut collector);
    }

    for &func in &collector.seen_funcs {
        if let DeclDef::Present(func_def_body) = &mut module.funcs[func].def {
            cfg::Structurizer::new(cx, func_def_body).structurize_func();
        }
    }
}

struct ReachableUseCollector<'a> {
    cx: &'a Context,
    module: &'a Module,

    // FIXME(eddyb) build some automation to avoid ever repeating these.
    seen_types: FxIndexSet<Type>,
    seen_consts: FxIndexSet<Const>,
    seen_global_vars: FxIndexSet<GlobalVar>,
    seen_funcs: FxIndexSet<Func>,
}

impl Visitor<'_> for ReachableUseCollector<'_> {
    // FIXME(eddyb) build some automation to avoid ever repeating these.
    fn visit_attr_set_use(&mut self, _attrs: AttrSet) {}
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
}
