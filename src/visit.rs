use crate::{
    spv, Attr, AttrSet, AttrSetDef, Func, Global, Misc, MiscInput, MiscKind, MiscOutput, Module,
    ModuleDebugInfo, ModuleDialect,
};

// FIXME(eddyb) `Sized` bound shouldn't be needed but removing it requires
// writing `impl Visitor<'a> + ?Sized` in `fn inner_visit_with` signatures.
pub trait Visitor<'a>: Sized {
    // Context-interned leaves (no default provided).
    // FIXME(eddyb) treat these separately somehow and allow e.g. automatic deep
    // visiting (with a set to avoid repeat visits) if a `Rc<Context>` is provided.
    fn visit_attr_set_use(&mut self, attrs: AttrSet);

    // Leaves (noop default behavior).
    fn visit_spv_dialect(&mut self, _dialect: &spv::Dialect) {}
    fn visit_spv_module_debug_info(&mut self, _debug_info: &spv::ModuleDebugInfo) {}
    fn visit_misc_output(&mut self, _output: MiscOutput) {}
    fn visit_misc_input(&mut self, _input: MiscInput) {}
    fn visit_attr(&mut self, _attr: &Attr) {}

    // Non-leaves (defaulting to calling `.inner_visit_with(self)`).
    fn visit_module(&mut self, module: &'a Module) {
        module.inner_visit_with(self);
    }
    fn visit_module_dialect(&mut self, dialect: &'a ModuleDialect) {
        dialect.inner_visit_with(self);
    }
    fn visit_module_debug_info(&mut self, debug_info: &'a ModuleDebugInfo) {
        debug_info.inner_visit_with(self);
    }
    fn visit_global(&mut self, global: &'a Global) {
        global.inner_visit_with(self);
    }
    fn visit_func(&mut self, func: &'a Func) {
        func.inner_visit_with(self);
    }
    fn visit_misc(&mut self, misc: &'a Misc) {
        misc.inner_visit_with(self);
    }
    fn visit_attr_set_def(&mut self, attrs_def: &'a AttrSetDef) {
        attrs_def.inner_visit_with(self);
    }
}

/// Trait implemented on "visitable" types, to further "explore" a type by
/// visiting its "interior" (i.e. variants and/or fields).
///
/// That is, an `impl InnerVisit for X` will call the relevant `Visitor` method
/// for each `X` field, effectively performing a single level of a deep visit.
/// Also, if `Visitor::visit_X` exists for a given `X`, its default should be to
/// call `X::inner_visit_with` (i.e. so that visiting is mostly-deep by default).
pub trait InnerVisit {
    // FIXME(eddyb) the naming here isn't great, can it be improved?
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>);
}

/// Dynamic dispatch version of `InnerVisit`.
///
/// `dyn DynInnerVisit<'a, V>` is possible, unlike `dyn InnerVisit`, because of
/// the `trait`-level type parameter `V`, which replaces the method parameter.
pub trait DynInnerVisit<'a, V> {
    fn dyn_inner_visit_with(&'a self, visitor: &mut V);
}

impl<'a, T: InnerVisit, V: Visitor<'a>> DynInnerVisit<'a, V> for T {
    fn dyn_inner_visit_with(&'a self, visitor: &mut V) {
        self.inner_visit_with(visitor);
    }
}

// FIXME(eddyb) should the impls be here, or next to definitions? (maybe derived?)
impl InnerVisit for Module {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        // FIXME(eddyb) this can't be exhaustive because of the private `cx` field.
        let Self {
            dialect,
            debug_info,
            globals,
            funcs,
            ..
        } = self;

        visitor.visit_module_dialect(dialect);
        visitor.visit_module_debug_info(debug_info);
        for global in globals {
            visitor.visit_global(global);
        }
        for func in funcs {
            visitor.visit_func(func);
        }
    }
}

impl InnerVisit for ModuleDialect {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        match self {
            Self::Spv(dialect) => visitor.visit_spv_dialect(dialect),
        }
    }
}

impl InnerVisit for ModuleDebugInfo {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        match self {
            Self::Spv(debug_info) => {
                visitor.visit_spv_module_debug_info(debug_info);
            }
        }
    }
}

impl InnerVisit for Global {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        match self {
            Self::Misc(misc) => visitor.visit_misc(misc),
        }
    }
}

impl InnerVisit for Func {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        let Self { insts } = self;

        for inst in insts {
            visitor.visit_misc(inst);
        }
    }
}

impl InnerVisit for Misc {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        let Self {
            kind,
            output,
            inputs,
            attrs,
        } = self;

        match kind {
            MiscKind::SpvInst { .. } => {}
        }
        if let Some(output) = *output {
            visitor.visit_misc_output(output);
        }
        for &input in inputs {
            visitor.visit_misc_input(input);
        }
        visitor.visit_attr_set_use(*attrs);
    }
}

impl InnerVisit for AttrSetDef {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        let Self { attrs } = self;

        for attr in attrs {
            visitor.visit_attr(attr);
        }
    }
}
