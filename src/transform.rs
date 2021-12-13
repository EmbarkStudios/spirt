use crate::{
    spv, AddrSpace, Attr, AttrSet, AttrSetDef, BlockDef, BlockInput, Const, ConstCtor,
    ConstCtorArg, ConstDef, ControlInst, ControlInstInput, ControlInstKind, DataInstDef,
    DataInstInput, DataInstKind, DeclDef, ExportKey, Exportee, Func, FuncDecl, FuncDefBody,
    FuncParam, GlobalVar, GlobalVarDecl, GlobalVarDefBody, Import, Module, ModuleDebugInfo,
    ModuleDialect, Type, TypeCtor, TypeCtorArg, TypeDef, Value,
};
use std::cmp::Ordering;

/// The result of a transformation (which is not in-place).
#[must_use]
#[derive(Copy, Clone)]
pub enum Transformed<T> {
    /// The original `T` value remains as it was, at no cost.
    Unchanged,

    /// Some part of the original `T` value was transformed, and a new `T` value
    /// had to be constructed. This change will propagate in any "outer" value.
    Changed(T),
}

impl<T> Transformed<T> {
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Transformed<U> {
        match self {
            Transformed::Unchanged => Transformed::Unchanged,
            Transformed::Changed(new) => Transformed::Changed(f(new)),
        }
    }

    pub fn apply_to(self, dest: &mut T) {
        match self {
            Transformed::Unchanged => {}
            Transformed::Changed(new) => *dest = new,
        }
    }
}

// HACK(eddyb) the `Self` type here doesn't matter, it only exists so that we
// can call e.g. `Transformed::foo(...)` methods.
impl Transformed<()> {
    /// Map every element of an iterator through `transform_elem` and return
    /// `Transformed::Changed(new_iter)` if any `transform_elem` call returned
    /// `Transformed::Changed`, with `new_iter` containing a combination of the
    /// changed elements, and clones of the unchanged elements.
    pub fn map_iter<'a, T: 'a + Clone>(
        iter: impl Iterator<Item = &'a T> + Clone + 'a,
        mut transform_elem: impl FnMut(&'a T) -> Transformed<T> + 'a,
    ) -> Transformed<impl Iterator<Item = T> + 'a> {
        for (i, elem_i) in iter.clone().enumerate() {
            if let Transformed::Changed(new_elem_i) = transform_elem(elem_i) {
                let mut new_elem_i = Some(new_elem_i);
                return Transformed::Changed(iter.enumerate().map(move |(j, elem_j)| {
                    match j.cmp(&i) {
                        // Earlier elements, for which `transform_elem` was called
                        // already, and had returned `Unchanged`.
                        Ordering::Less => elem_j.clone(),

                        // The first element for which `transform_elem` returned
                        // `Changed`, resulting in the `Changed` iterator.
                        Ordering::Equal => new_elem_i.take().unwrap(),

                        // Later elements, for which only now `transform_elem`
                        // gets called, and may be `Unchanged` or `Changed`.
                        Ordering::Greater => match transform_elem(elem_j) {
                            Transformed::Unchanged => elem_j.clone(),
                            Transformed::Changed(new_elem_j) => new_elem_j,
                        },
                    }
                }));
            }
        }
        Transformed::Unchanged
    }
}

/// Helper macro to create a combined `Transformed` out of several variables,
/// each with their own transformation, where any `Transformed::Changed` input
/// will result in a `Transformed::Changed` output, using a combination of the
/// changed inputs, and clones of the unchanged inputs.
macro_rules! transform {
    // User-facing entry-point, dispatches to the internal more-explicit form.
    ({ $($input:ident -> $input_transformed:expr),+ $(,)? } => $output:expr) => {
        transform!(@explicit {
            $($input: transform($input_transformed), clone(Clone::clone($input));)+
        } => $output)
    };

    // Single input is just a `map`.
    (@explicit {
        $x:ident: transform($x_transformed:expr), clone($x_cloned:expr);
    } => $output:expr) => {
        $x_transformed.map(|$x| $output)
    };

    // Reduce the first two inputs into one input, recursively.
    (@explicit {
        $a:ident: transform($a_transformed:expr), clone($a_cloned:expr);
        $b:ident: transform($b_transformed:expr), clone($b_cloned:expr);
        $($inputs:tt)*
    } => $output:expr) => {{
        // HACK(eddyb) avoid exponential blow-up from duplicating expressions.
        let clone_a = || $a_cloned;
        let clone_b = || $b_cloned;

        transform!(@explicit {
            ab: transform(match ($a_transformed, $b_transformed) {
                (Transformed::Unchanged, Transformed::Unchanged)
                    => Transformed::Unchanged,
                (Transformed::Changed(new_a), Transformed::Unchanged)
                    => Transformed::Changed((new_a, clone_b())),
                (Transformed::Unchanged, Transformed::Changed(new_b))
                    => Transformed::Changed((clone_a(), new_b)),
                (Transformed::Changed(new_a), Transformed::Changed(new_b))
                    => Transformed::Changed((new_a, new_b)),
            }), clone((clone_a(), clone_b()));
            $($inputs)*
        } => {
            let ($a, $b) = ab;
            $output
        })
    }}
}

// FIXME(eddyb) `Sized` bound shouldn't be needed but removing it requires
// writing `impl Transformer + ?Sized` in `fn inner_transform_with` signatures.
pub trait Transformer: Sized {
    // Context-interned leaves (noop default behavior).
    fn transform_attr_set_use(&mut self, _attrs: AttrSet) -> Transformed<AttrSet> {
        Transformed::Unchanged
    }
    fn transform_type_use(&mut self, _ty: Type) -> Transformed<Type> {
        Transformed::Unchanged
    }
    fn transform_const_use(&mut self, _ct: Const) -> Transformed<Const> {
        Transformed::Unchanged
    }

    // Module-stored (but context-allocated indices) leaves (noop default behavior).
    fn transform_global_var_use(&mut self, _gv: GlobalVar) -> Transformed<GlobalVar> {
        Transformed::Unchanged
    }
    fn transform_func_use(&mut self, _func: Func) -> Transformed<Func> {
        Transformed::Unchanged
    }

    // Leaves (noop default behavior).
    fn transform_attr(&mut self, _attr: &Attr) -> Transformed<Attr> {
        Transformed::Unchanged
    }

    // Leaves transformed in-place (noop default behavior).
    fn in_place_transform_spv_dialect(&mut self, _dialect: &mut spv::Dialect) {}
    fn in_place_transform_spv_module_debug_info(&mut self, _debug_info: &mut spv::ModuleDebugInfo) {
    }

    // Non-leaves (defaulting to calling `.inner_transform_with(self)`).
    fn transform_attr_set_def(&mut self, attrs_def: &AttrSetDef) -> Transformed<AttrSetDef> {
        attrs_def.inner_transform_with(self)
    }
    fn transform_type_def(&mut self, ty_def: &TypeDef) -> Transformed<TypeDef> {
        ty_def.inner_transform_with(self)
    }
    fn transform_const_def(&mut self, ct_def: &ConstDef) -> Transformed<ConstDef> {
        ct_def.inner_transform_with(self)
    }
    fn transform_data_inst_input(&mut self, input: &DataInstInput) -> Transformed<DataInstInput> {
        input.inner_transform_with(self)
    }
    fn transform_control_inst_input(
        &mut self,
        input: &ControlInstInput,
    ) -> Transformed<ControlInstInput> {
        input.inner_transform_with(self)
    }

    // Non-leaves transformed in-place (defaulting to calling
    // `.inner_in_place_transform_with(self)`).
    fn in_place_transform_module(&mut self, module: &mut Module) {
        module.inner_in_place_transform_with(self);
    }
    fn in_place_transform_module_dialect(&mut self, dialect: &mut ModuleDialect) {
        dialect.inner_in_place_transform_with(self);
    }
    fn in_place_transform_module_debug_info(&mut self, debug_info: &mut ModuleDebugInfo) {
        debug_info.inner_in_place_transform_with(self);
    }
    fn in_place_transform_global_var_decl(&mut self, gv_decl: &mut GlobalVarDecl) {
        gv_decl.inner_in_place_transform_with(self);
    }
    fn in_place_transform_func_decl(&mut self, func_decl: &mut FuncDecl) {
        func_decl.inner_in_place_transform_with(self);
    }
    fn in_place_transform_data_inst_def(&mut self, data_inst_def: &mut DataInstDef) {
        data_inst_def.inner_in_place_transform_with(self);
    }
    fn in_place_transform_control_inst(&mut self, control_inst: &mut ControlInst) {
        control_inst.inner_in_place_transform_with(self);
    }
}

/// Trait implemented on "transformable" types, to further "elaborate" a type by
/// transforming its "interior" (i.e. variants and/or fields).
///
/// That is, an `impl InnerTransform for X` will call the relevant `Transformer`
/// method for each `X` field, effectively performing a single level of a deep
/// transform.
/// Also, if `Transformer::transform_X` exists for a given `X`, its default should
/// be to call `X::inner_transform_with` (i.e. so that transforming is mostly-deep
/// by default).
pub trait InnerTransform: Sized {
    // FIXME(eddyb) the naming here isn't great, can it be improved?
    // FIXME(eddyb) should this be `self -> Self` instead of `&mut self -> ()`?
    fn inner_transform_with(&self, transformer: &mut impl Transformer) -> Transformed<Self>;
}

/// Like `InnerTransform`, but only for the `in_place_transform_X` cases.
pub trait InnerInPlaceTransform {
    fn inner_in_place_transform_with(&mut self, transformer: &mut impl Transformer);
}

// FIXME(eddyb) should the impls be here, or next to definitions? (maybe derived?)
impl InnerInPlaceTransform for Module {
    fn inner_in_place_transform_with(&mut self, transformer: &mut impl Transformer) {
        // FIXME(eddyb) this can't be exhaustive because of the private `cx` field.
        let Self {
            dialect,
            debug_info,
            global_vars: _,
            funcs: _,
            exports,
            ..
        } = self;

        transformer.in_place_transform_module_dialect(dialect);
        transformer.in_place_transform_module_debug_info(debug_info);

        // HACK(eddyb) this takes two passes, once for values and once for keys,
        // to be able to use in-place mutable iteration for the former, and
        // `Transformed::map_iter` (i.e. immutable iteration) for the latter.
        for exportee in exports.values_mut() {
            exportee
                .inner_transform_with(transformer)
                .apply_to(exportee);
        }
        Transformed::map_iter(exports.keys(), |export_key| {
            export_key.inner_transform_with(transformer)
        })
        .map(|new_keys_iter| {
            // Recombine the new keys with the existing values.
            new_keys_iter.zip(exports.values().cloned()).collect()
        })
        .apply_to(exports);
    }
}

impl InnerInPlaceTransform for ModuleDialect {
    fn inner_in_place_transform_with(&mut self, transformer: &mut impl Transformer) {
        match self {
            Self::Spv(dialect) => transformer.in_place_transform_spv_dialect(dialect),
        }
    }
}

impl InnerInPlaceTransform for ModuleDebugInfo {
    fn inner_in_place_transform_with(&mut self, transformer: &mut impl Transformer) {
        match self {
            Self::Spv(debug_info) => {
                transformer.in_place_transform_spv_module_debug_info(debug_info);
            }
        }
    }
}

impl InnerTransform for ExportKey {
    fn inner_transform_with(&self, transformer: &mut impl Transformer) -> Transformed<Self> {
        match self {
            Self::LinkName(_) => Transformed::Unchanged,

            Self::SpvEntryPoint {
                params,
                interface_global_vars,
            } => transform!({
                params -> Transformed::Unchanged,
                interface_global_vars -> Transformed::map_iter(
                    interface_global_vars.iter(),
                    |&gv| transformer.transform_global_var_use(gv),
                ).map(|new_iter| new_iter.collect()),
            } => Self::SpvEntryPoint {
                params,
                interface_global_vars,
            }),
        }
    }
}

impl InnerTransform for Exportee {
    fn inner_transform_with(&self, transformer: &mut impl Transformer) -> Transformed<Self> {
        match *self {
            Self::GlobalVar(gv) => transform!({
                gv -> transformer.transform_global_var_use(gv),
            } => Self::GlobalVar(gv)),

            Self::Func(func) => transform!({
                func -> transformer.transform_func_use(func),
            } => Self::Func(func)),
        }
    }
}

impl InnerTransform for AttrSetDef {
    fn inner_transform_with(&self, transformer: &mut impl Transformer) -> Transformed<Self> {
        let Self { attrs } = self;

        transform!({
            attrs -> Transformed::map_iter(
                attrs.iter(),
                |attr| transformer.transform_attr(attr),
            ).map(|new_iter| new_iter.collect()),
        } => Self {
            attrs,
        })
    }
}

impl InnerTransform for TypeDef {
    fn inner_transform_with(&self, transformer: &mut impl Transformer) -> Transformed<Self> {
        let Self {
            attrs,
            ctor,
            ctor_args,
        } = self;

        transform!({
            attrs -> transformer.transform_attr_set_use(*attrs),
            ctor -> match ctor {
                TypeCtor::SpvInst(_) => Transformed::Unchanged,
            },
            ctor_args -> Transformed::map_iter(ctor_args.iter(), |arg| match *arg {
                TypeCtorArg::Type(ty) => transform!({
                    ty -> transformer.transform_type_use(ty),
                } => TypeCtorArg::Type(ty)),

                TypeCtorArg::Const(ct) => transform!({
                    ct -> transformer.transform_const_use(ct),
                } => TypeCtorArg::Const(ct)),

                TypeCtorArg::SpvImm(_) => Transformed::Unchanged,
            }).map(|new_iter| new_iter.collect()),
        } => Self {
            attrs,
            ctor,
            ctor_args,
        })
    }
}

impl InnerTransform for ConstDef {
    fn inner_transform_with(&self, transformer: &mut impl Transformer) -> Transformed<Self> {
        let Self {
            attrs,
            ty,
            ctor,
            ctor_args,
        } = self;

        transform!({
            attrs -> transformer.transform_attr_set_use(*attrs),
            ty -> transformer.transform_type_use(*ty),
            ctor -> match ctor {
                ConstCtor::PtrToGlobalVar(gv) => transform!({
                    gv -> transformer.transform_global_var_use(*gv),
                } => ConstCtor::PtrToGlobalVar(gv)),

                ConstCtor::SpvInst(_) => Transformed::Unchanged
            },
            ctor_args -> Transformed::map_iter(ctor_args.iter(), |arg| match *arg {
                ConstCtorArg::Const(ct) => transform!({
                    ct -> transformer.transform_const_use(ct),
                } => ConstCtorArg::Const(ct)),

                ConstCtorArg::SpvImm(_) => Transformed::Unchanged,
            }).map(|new_iter| new_iter.collect()),
        } => Self {
            attrs,
            ty,
            ctor,
            ctor_args,
        })
    }
}

impl<D: InnerInPlaceTransform> InnerInPlaceTransform for DeclDef<D> {
    fn inner_in_place_transform_with(&mut self, transformer: &mut impl Transformer) {
        match self {
            Self::Imported(import) => match import {
                Import::LinkName(_) => {}
            },
            Self::Present(def) => def.inner_in_place_transform_with(transformer),
        }
    }
}

impl InnerInPlaceTransform for GlobalVarDecl {
    fn inner_in_place_transform_with(&mut self, transformer: &mut impl Transformer) {
        let Self {
            attrs,
            type_of_ptr_to,
            addr_space,
            def,
        } = self;

        transformer.transform_attr_set_use(*attrs).apply_to(attrs);
        transformer
            .transform_type_use(*type_of_ptr_to)
            .apply_to(type_of_ptr_to);
        match addr_space {
            AddrSpace::SpvStorageClass(_) => {}
        }
        def.inner_in_place_transform_with(transformer);
    }
}

impl InnerInPlaceTransform for GlobalVarDefBody {
    fn inner_in_place_transform_with(&mut self, transformer: &mut impl Transformer) {
        let Self { initializer } = self;

        if let Some(initializer) = initializer {
            transformer
                .transform_const_use(*initializer)
                .apply_to(initializer);
        }
    }
}

impl InnerInPlaceTransform for FuncDecl {
    fn inner_in_place_transform_with(&mut self, transformer: &mut impl Transformer) {
        let Self {
            attrs,
            ret_type,
            params,
            def,
        } = self;

        transformer.transform_attr_set_use(*attrs).apply_to(attrs);
        transformer.transform_type_use(*ret_type).apply_to(ret_type);
        for param in params {
            param.inner_transform_with(transformer).apply_to(param);
        }
        def.inner_in_place_transform_with(transformer);
    }
}

impl InnerTransform for FuncParam {
    fn inner_transform_with(&self, transformer: &mut impl Transformer) -> Transformed<Self> {
        let Self { attrs, ty } = self;

        transform!({
            attrs -> transformer.transform_attr_set_use(*attrs),
            ty -> transformer.transform_type_use(*ty),
        } => Self {
            attrs,
            ty,
        })
    }
}

impl InnerInPlaceTransform for FuncDefBody {
    fn inner_in_place_transform_with(&mut self, transformer: &mut impl Transformer) {
        let Self {
            data_insts,
            blocks,
            all_blocks,
        } = self;

        for &block in all_blocks.iter() {
            let BlockDef {
                inputs,
                insts,
                terminator,
            } = &mut blocks[block];

            for input in inputs {
                input.inner_transform_with(transformer).apply_to(input);
            }
            for inst in insts {
                transformer.in_place_transform_data_inst_def(&mut data_insts[*inst]);
            }
            transformer.in_place_transform_control_inst(terminator);
        }
    }
}

impl InnerTransform for BlockInput {
    fn inner_transform_with(&self, transformer: &mut impl Transformer) -> Transformed<Self> {
        let Self { attrs, ty } = self;

        transform!({
            attrs -> transformer.transform_attr_set_use(*attrs),
            ty -> transformer.transform_type_use(*ty),
        } => Self {
            attrs,
            ty,
        })
    }
}

impl InnerInPlaceTransform for DataInstDef {
    fn inner_in_place_transform_with(&mut self, transformer: &mut impl Transformer) {
        let Self {
            attrs,
            kind,
            output_type,
            inputs,
        } = self;

        transformer.transform_attr_set_use(*attrs).apply_to(attrs);
        match kind {
            DataInstKind::FuncCall(func) => transformer.transform_func_use(*func).apply_to(func),
            DataInstKind::SpvInst(_) | DataInstKind::SpvExtInst { .. } => {}
        }
        if let Some(ty) = output_type {
            transformer.transform_type_use(*ty).apply_to(ty);
        }
        for input in inputs {
            transformer.transform_data_inst_input(input).apply_to(input);
        }
    }
}

impl InnerTransform for DataInstInput {
    fn inner_transform_with(&self, transformer: &mut impl Transformer) -> Transformed<Self> {
        match self {
            Self::Value(v) => transform!({
                v -> v.inner_transform_with(transformer),
            } => Self::Value(v)),

            Self::SpvImm(_) => Transformed::Unchanged,
        }
    }
}

impl InnerInPlaceTransform for ControlInst {
    fn inner_in_place_transform_with(&mut self, transformer: &mut impl Transformer) {
        let Self {
            attrs,
            kind,
            inputs,
            target_block_inputs,
        } = self;

        transformer.transform_attr_set_use(*attrs).apply_to(attrs);
        match kind {
            ControlInstKind::SpvInst(_) => {}
        }
        for input in inputs {
            transformer
                .transform_control_inst_input(input)
                .apply_to(input);
        }
        for block_inputs in target_block_inputs.values_mut() {
            for v in block_inputs {
                v.inner_transform_with(transformer).apply_to(v);
            }
        }
    }
}

impl InnerTransform for ControlInstInput {
    fn inner_transform_with(&self, transformer: &mut impl Transformer) -> Transformed<Self> {
        match self {
            Self::Value(v) => transform!({
                v -> v.inner_transform_with(transformer),
            } => Self::Value(v)),

            Self::TargetBlock(_) => Transformed::Unchanged,

            Self::SpvImm(_) => Transformed::Unchanged,
        }
    }
}

impl InnerTransform for Value {
    fn inner_transform_with(&self, transformer: &mut impl Transformer) -> Transformed<Self> {
        match self {
            Self::Const(ct) => transform!({
                ct -> transformer.transform_const_use(*ct),
            } => Self::Const(ct)),

            Self::FuncParam { idx: _ }
            | Self::BlockInput {
                block: _,
                input_idx: _,
            }
            | Self::DataInstOutput(_) => Transformed::Unchanged,
        }
    }
}
