//! Immutable IR traversal.

use crate::func_at::FuncAt;
use crate::qptr::{self, QPtrAttr, QPtrMemUsage, QPtrMemUsageKind, QPtrOp, QPtrUsage};
use crate::{
    cfg, spv, AddrSpace, Attr, AttrSet, AttrSetDef, Const, ConstCtor, ConstDef, ControlNode,
    ControlNodeDef, ControlNodeKind, ControlNodeOutputDecl, ControlRegion, ControlRegionDef,
    ControlRegionInputDecl, DataInstDef, DataInstForm, DataInstFormDef, DataInstKind, DeclDef,
    DiagMsgPart, EntityListIter, ExportKey, Exportee, Func, FuncDecl, FuncDefBody, FuncParam,
    GlobalVar, GlobalVarDecl, GlobalVarDefBody, Import, Module, ModuleDebugInfo, ModuleDialect,
    SelectionKind, Type, TypeCtor, TypeCtorArg, TypeDef, Value,
};

// FIXME(eddyb) `Sized` bound shouldn't be needed but removing it requires
// writing `impl Visitor<'a> + ?Sized` in `fn inner_visit_with` signatures.
pub trait Visitor<'a>: Sized {
    // Context-interned leaves (no default provided).
    // FIXME(eddyb) treat these separately somehow and allow e.g. automatic deep
    // visiting (with a set to avoid repeat visits) if a `Rc<Context>` is provided.
    fn visit_attr_set_use(&mut self, attrs: AttrSet);
    fn visit_type_use(&mut self, ty: Type);
    fn visit_const_use(&mut self, ct: Const);
    fn visit_data_inst_form_use(&mut self, data_inst_form: DataInstForm);

    // Module-stored entity leaves (no default provided).
    fn visit_global_var_use(&mut self, gv: GlobalVar);
    fn visit_func_use(&mut self, func: Func);

    // Leaves (noop default behavior).
    fn visit_spv_dialect(&mut self, _dialect: &spv::Dialect) {}
    fn visit_spv_module_debug_info(&mut self, _debug_info: &spv::ModuleDebugInfo) {}
    fn visit_import(&mut self, _import: &Import) {}

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
    fn visit_attr_set_def(&mut self, attrs_def: &'a AttrSetDef) {
        attrs_def.inner_visit_with(self);
    }
    fn visit_attr(&mut self, attr: &'a Attr) {
        attr.inner_visit_with(self);
    }
    fn visit_type_def(&mut self, ty_def: &'a TypeDef) {
        ty_def.inner_visit_with(self);
    }
    fn visit_const_def(&mut self, ct_def: &'a ConstDef) {
        ct_def.inner_visit_with(self);
    }
    fn visit_global_var_decl(&mut self, gv_decl: &'a GlobalVarDecl) {
        gv_decl.inner_visit_with(self);
    }
    fn visit_func_decl(&mut self, func_decl: &'a FuncDecl) {
        func_decl.inner_visit_with(self);
    }
    fn visit_control_region_def(&mut self, func_at_control_region: FuncAt<'a, ControlRegion>) {
        func_at_control_region.inner_visit_with(self);
    }
    fn visit_control_node_def(&mut self, func_at_control_node: FuncAt<'a, ControlNode>) {
        func_at_control_node.inner_visit_with(self);
    }
    fn visit_data_inst_def(&mut self, data_inst_def: &'a DataInstDef) {
        data_inst_def.inner_visit_with(self);
    }
    fn visit_data_inst_form_def(&mut self, data_inst_form_def: &'a DataInstFormDef) {
        data_inst_form_def.inner_visit_with(self);
    }
    fn visit_value_use(&mut self, v: &'a Value) {
        v.inner_visit_with(self);
    }
}

/// Trait implemented on "visitable" types (shallowly visitable, at least).
///
/// That is, an `impl Visit for X` will call the relevant [`Visitor`] method for
/// `X`, typically named `Visitor::visit_X` or `Visitor::visit_X_use`.
//
// FIXME(eddyb) use this more (e.g. in implementing `InnerVisit`).
pub trait Visit {
    fn visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>);
}

macro_rules! impl_visit {
    (
        by_val { $($by_val_method:ident($by_val_ty:ty)),* $(,)? }
        by_ref { $($by_ref_method:ident($by_ref_ty:ty)),* $(,)? }
        forward_to_inner_visit { $($forward_to_inner_visit_ty:ty),* $(,)? }
    ) => {
        $(impl Visit for $by_val_ty {
            fn visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
                visitor.$by_val_method(*self);
            }
        })*
        $(impl Visit for $by_ref_ty {
            fn visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
                visitor.$by_ref_method(self);
            }
        })*
        $(impl Visit for $forward_to_inner_visit_ty {
            fn visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
                self.inner_visit_with(visitor);
            }
        })*
    };
}

impl_visit! {
    by_val {
        visit_attr_set_use(AttrSet),
        visit_type_use(Type),
        visit_const_use(Const),
        visit_global_var_use(GlobalVar),
        visit_func_use(Func),
    }
    by_ref {
        visit_spv_dialect(spv::Dialect),
        visit_spv_module_debug_info(spv::ModuleDebugInfo),
        visit_import(Import),
        visit_module(Module),
        visit_module_dialect(ModuleDialect),
        visit_module_debug_info(ModuleDebugInfo),
        visit_attr_set_def(AttrSetDef),
        visit_attr(Attr),
        visit_type_def(TypeDef),
        visit_const_def(ConstDef),
        visit_global_var_decl(GlobalVarDecl),
        visit_func_decl(FuncDecl),
        visit_data_inst_def(DataInstDef),
        visit_value_use(Value),
    }
    forward_to_inner_visit {
        // NOTE(eddyb) the interpolated parts of `Attr::Diagnostics` aren't visited
        // by default (as they're "inert data"), this is only for `print`'s usage.
        Vec<DiagMsgPart>,
    }
}

/// Dynamic dispatch version of [`Visit`].
///
/// `dyn DynVisit<'a, V>` is possible, unlike `dyn Visit`, because of the
/// `trait`-level type parameter `V`, which replaces the method parameter.
pub trait DynVisit<'a, V> {
    fn dyn_visit_with(&'a self, visitor: &mut V);
}

impl<'a, T: Visit, V: Visitor<'a>> DynVisit<'a, V> for T {
    fn dyn_visit_with(&'a self, visitor: &mut V) {
        self.visit_with(visitor);
    }
}

/// Trait implemented on "deeply visitable" types, to further "explore" a type
/// by visiting its "interior" (i.e. variants and/or fields).
///
/// That is, an `impl InnerVisit for X` will call the relevant [`Visitor`] method
/// for each `X` field, effectively performing a single level of a deep visit.
/// Also, if `Visitor::visit_X` exists for a given `X`, its default should be to
/// call `X::inner_visit_with` (i.e. so that visiting is mostly-deep by default).
pub trait InnerVisit {
    // FIXME(eddyb) the naming here isn't great, can it be improved?
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>);
}

/// Dynamic dispatch version of [`InnerVisit`].
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
            global_vars: _,
            funcs: _,
            exports,
            ..
        } = self;

        visitor.visit_module_dialect(dialect);
        visitor.visit_module_debug_info(debug_info);
        for (export_key, exportee) in exports {
            export_key.inner_visit_with(visitor);
            exportee.inner_visit_with(visitor);
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

impl InnerVisit for ExportKey {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        match self {
            Self::LinkName(_) => {}

            Self::SpvEntryPoint {
                imms: _,
                interface_global_vars,
            } => {
                for &gv in interface_global_vars {
                    visitor.visit_global_var_use(gv);
                }
            }
        }
    }
}

impl InnerVisit for Exportee {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        match *self {
            Self::GlobalVar(gv) => visitor.visit_global_var_use(gv),
            Self::Func(func) => visitor.visit_func_use(func),
        }
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

impl InnerVisit for Attr {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        match self {
            Attr::Diagnostics(_)
            | Attr::SpvAnnotation(_)
            | Attr::SpvDebugLine { .. }
            | Attr::SpvBitflagsOperand(_) => {}

            Attr::QPtr(attr) => match attr {
                QPtrAttr::ToSpvPtrInput {
                    input_idx: _,
                    pointee,
                }
                | QPtrAttr::FromSpvPtrOutput {
                    addr_space: _,
                    pointee,
                } => visitor.visit_type_use(pointee.0),

                QPtrAttr::Usage(usage) => usage.0.inner_visit_with(visitor),
            },
        }
    }
}

// NOTE(eddyb) the interpolated parts of `Attr::Diagnostics` aren't visited
// by default (as they're "inert data"), this is only for `print`'s usage.
impl InnerVisit for Vec<DiagMsgPart> {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        for part in self {
            match part {
                DiagMsgPart::Plain(_) => {}
                &DiagMsgPart::Attrs(attrs) => visitor.visit_attr_set_use(attrs),
                &DiagMsgPart::Type(ty) => visitor.visit_type_use(ty),
                &DiagMsgPart::Const(ct) => visitor.visit_const_use(ct),
                DiagMsgPart::QPtrUsage(usage) => usage.inner_visit_with(visitor),
            }
        }
    }
}

impl InnerVisit for QPtrUsage {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        match self {
            &QPtrUsage::Handles(qptr::shapes::Handle::Opaque(ty)) => {
                visitor.visit_type_use(ty);
            }
            QPtrUsage::Handles(qptr::shapes::Handle::Buffer(_, data_usage)) => {
                data_usage.inner_visit_with(visitor);
            }
            QPtrUsage::Memory(usage) => usage.inner_visit_with(visitor),
        }
    }
}

impl InnerVisit for QPtrMemUsage {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        let Self { max_size: _, kind } = self;
        kind.inner_visit_with(visitor);
    }
}

impl InnerVisit for QPtrMemUsageKind {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        match self {
            Self::Unused => {}
            &Self::StrictlyTyped(ty) | &Self::DirectAccess(ty) => {
                visitor.visit_type_use(ty);
            }
            Self::OffsetBase(entries) => {
                for sub_usage in entries.values() {
                    sub_usage.inner_visit_with(visitor);
                }
            }
            Self::DynOffsetBase { element, stride: _ } => {
                element.inner_visit_with(visitor);
            }
        }
    }
}

impl InnerVisit for TypeDef {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        let Self {
            attrs,
            ctor,
            ctor_args,
        } = self;

        visitor.visit_attr_set_use(*attrs);
        match ctor {
            TypeCtor::QPtr | TypeCtor::SpvInst(_) | TypeCtor::SpvStringLiteralForExtInst => {}
        }
        for &arg in ctor_args {
            match arg {
                TypeCtorArg::Type(ty) => visitor.visit_type_use(ty),
                TypeCtorArg::Const(ct) => visitor.visit_const_use(ct),
            }
        }
    }
}

impl InnerVisit for ConstDef {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        let Self {
            attrs,
            ty,
            ctor,
            ctor_args,
        } = self;

        visitor.visit_attr_set_use(*attrs);
        visitor.visit_type_use(*ty);
        match *ctor {
            ConstCtor::PtrToGlobalVar(gv) => visitor.visit_global_var_use(gv),
            ConstCtor::SpvInst(_) | ConstCtor::SpvStringLiteralForExtInst(_) => {}
        }
        for &ct in ctor_args {
            visitor.visit_const_use(ct);
        }
    }
}

impl<D: InnerVisit> InnerVisit for DeclDef<D> {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        match self {
            Self::Imported(import) => visitor.visit_import(import),
            Self::Present(def) => def.inner_visit_with(visitor),
        }
    }
}

impl InnerVisit for GlobalVarDecl {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        let Self {
            attrs,
            type_of_ptr_to,
            shape,
            addr_space,
            def,
        } = self;

        visitor.visit_attr_set_use(*attrs);
        visitor.visit_type_use(*type_of_ptr_to);
        if let Some(shape) = shape {
            match shape {
                qptr::shapes::GlobalVarShape::TypedInterface(ty) => visitor.visit_type_use(*ty),
                qptr::shapes::GlobalVarShape::Handles { .. }
                | qptr::shapes::GlobalVarShape::UntypedData(_) => {}
            }
        }
        match addr_space {
            AddrSpace::Handles | AddrSpace::SpvStorageClass(_) => {}
        }
        def.inner_visit_with(visitor);
    }
}

impl InnerVisit for GlobalVarDefBody {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        let Self { initializer } = self;

        if let Some(initializer) = *initializer {
            visitor.visit_const_use(initializer);
        }
    }
}

impl InnerVisit for FuncDecl {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        let Self {
            attrs,
            ret_type,
            params,
            def,
        } = self;

        visitor.visit_attr_set_use(*attrs);
        visitor.visit_type_use(*ret_type);
        for param in params {
            param.inner_visit_with(visitor);
        }
        def.inner_visit_with(visitor);
    }
}

impl InnerVisit for FuncParam {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        let Self { attrs, ty } = *self;

        visitor.visit_attr_set_use(attrs);
        visitor.visit_type_use(ty);
    }
}

impl InnerVisit for FuncDefBody {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        match &self.unstructured_cfg {
            None => visitor.visit_control_region_def(self.at_body()),
            Some(cfg) => {
                for region in cfg.rev_post_order(self) {
                    visitor.visit_control_region_def(self.at(region));

                    if let Some(control_inst) = cfg.control_inst_on_exit_from.get(region) {
                        control_inst.inner_visit_with(visitor);
                    }
                }
            }
        }
    }
}

// FIXME(eddyb) this can't implement `InnerVisit` because of the `&'a self`
// requirement, whereas this has `'a` in `self: FuncAt<'a, ControlRegion>`.
impl<'a> FuncAt<'a, ControlRegion> {
    pub fn inner_visit_with(self, visitor: &mut impl Visitor<'a>) {
        let ControlRegionDef {
            inputs,
            children,
            outputs,
        } = self.def();

        for input in inputs {
            input.inner_visit_with(visitor);
        }
        self.at(*children).into_iter().inner_visit_with(visitor);
        for v in outputs {
            visitor.visit_value_use(v);
        }
    }
}

impl InnerVisit for ControlRegionInputDecl {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        let Self { attrs, ty } = *self;

        visitor.visit_attr_set_use(attrs);
        visitor.visit_type_use(ty);
    }
}

// FIXME(eddyb) this can't implement `InnerVisit` because of the `&'a self`
// requirement, whereas this has `'a` in `self: FuncAt<'a, ...>`.
impl<'a> FuncAt<'a, EntityListIter<ControlNode>> {
    pub fn inner_visit_with(self, visitor: &mut impl Visitor<'a>) {
        for func_at_control_node in self {
            visitor.visit_control_node_def(func_at_control_node);
        }
    }
}

// FIXME(eddyb) this can't implement `InnerVisit` because of the `&'a self`
// requirement, whereas this has `'a` in `self: FuncAt<'a, ControlNode>`.
impl<'a> FuncAt<'a, ControlNode> {
    pub fn inner_visit_with(self, visitor: &mut impl Visitor<'a>) {
        let ControlNodeDef { kind, outputs } = self.def();

        match kind {
            ControlNodeKind::Block { insts } => {
                for func_at_inst in self.at(*insts) {
                    visitor.visit_data_inst_def(func_at_inst.def());
                }
            }
            ControlNodeKind::Select {
                kind: SelectionKind::BoolCond | SelectionKind::SpvInst(_),
                scrutinee,
                cases,
            } => {
                visitor.visit_value_use(scrutinee);
                for &case in cases {
                    visitor.visit_control_region_def(self.at(case));
                }
            }
            ControlNodeKind::Loop {
                initial_inputs,
                body,
                repeat_condition,
            } => {
                for v in initial_inputs {
                    visitor.visit_value_use(v);
                }
                visitor.visit_control_region_def(self.at(*body));
                visitor.visit_value_use(repeat_condition);
            }
        }
        for output in outputs {
            output.inner_visit_with(visitor);
        }
    }
}

impl InnerVisit for ControlNodeOutputDecl {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        let Self { attrs, ty } = *self;

        visitor.visit_attr_set_use(attrs);
        visitor.visit_type_use(ty);
    }
}

impl InnerVisit for DataInstDef {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        let Self {
            attrs,
            form,
            inputs,
        } = self;

        visitor.visit_attr_set_use(*attrs);
        visitor.visit_data_inst_form_use(*form);
        for v in inputs {
            visitor.visit_value_use(v);
        }
    }
}

impl InnerVisit for DataInstFormDef {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        let Self { kind, output_type } = self;

        match kind {
            &DataInstKind::FuncCall(func) => visitor.visit_func_use(func),
            DataInstKind::QPtr(op) => match *op {
                QPtrOp::FuncLocalVar(_)
                | QPtrOp::HandleArrayIndex
                | QPtrOp::BufferData
                | QPtrOp::BufferDynLen { .. }
                | QPtrOp::Offset(_)
                | QPtrOp::DynOffset { .. }
                | QPtrOp::Load
                | QPtrOp::Store => {}
            },
            DataInstKind::SpvInst(_) | DataInstKind::SpvExtInst { .. } => {}
        }
        if let Some(ty) = *output_type {
            visitor.visit_type_use(ty);
        }
    }
}

impl InnerVisit for cfg::ControlInst {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        let Self {
            attrs,
            kind,
            inputs,
            targets: _,
            target_inputs,
        } = self;

        visitor.visit_attr_set_use(*attrs);
        match kind {
            cfg::ControlInstKind::Unreachable
            | cfg::ControlInstKind::Return
            | cfg::ControlInstKind::ExitInvocation(cfg::ExitInvocationKind::SpvInst(_))
            | cfg::ControlInstKind::Branch
            | cfg::ControlInstKind::SelectBranch(
                SelectionKind::BoolCond | SelectionKind::SpvInst(_),
            ) => {}
        }
        for v in inputs {
            visitor.visit_value_use(v);
        }
        for inputs in target_inputs.values() {
            for v in inputs {
                visitor.visit_value_use(v);
            }
        }
    }
}

impl InnerVisit for Value {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        match *self {
            Self::Const(ct) => visitor.visit_const_use(ct),
            Self::ControlRegionInput {
                region: _,
                input_idx: _,
            }
            | Self::ControlNodeOutput {
                control_node: _,
                output_idx: _,
            }
            | Self::DataInstOutput(_) => {}
        }
    }
}
