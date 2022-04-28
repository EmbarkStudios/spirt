// FIXME(eddyb) stop using `itertools` for methods like `intersperse` when they
// get stabilized on `Iterator` instead.
#![allow(unstable_name_collisions)]
use itertools::Itertools as _;

use crate::visit::{DynInnerVisit, InnerVisit, Visitor};
use crate::{
    cfg, spv, AddrSpace, Attr, AttrSet, AttrSetDef, Const, ConstCtor, ConstDef, Context,
    ControlNode, ControlNodeDef, ControlNodeKind, ControlNodeOutputDecl, DataInst, DataInstDef,
    DataInstKind, DeclDef, ExportKey, Exportee, Func, FuncAt, FuncDecl, FuncDefBody, FuncParam,
    FxIndexMap, GlobalVar, GlobalVarDecl, GlobalVarDefBody, Import, Module, ModuleDebugInfo,
    ModuleDialect, Type, TypeCtor, TypeCtorArg, TypeDef, Value,
};
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use std::mem;

mod pretty;

/// "Definitions-before-uses" / "topo-sorted" printing plan.
///
/// In order to represent parts of a DAG textually, it first needs to have its
/// nodes "flattened" into an order (also known as "topo(logical) sorting"),
/// which `Plan` wholly records, before any printing can commence.
///
/// Additionally, nodes without a significant identity (i.e. interned ones) may
/// have their separate definition omitted in some cases where printing them
/// inline at their use site(s) is preferred (e.g. when they have a single use).
///
/// Once a `Plan` contains everything that needs to be printed, formatting the
/// `Plan` value with `fmt::Display` will print all of the nodes in the `Plan`.
pub struct Plan<'a> {
    cx: &'a Context,

    /// When visiting anything module-stored (global vars and funcs), the module
    /// is needed to go from the index to the definition, which is then cached.
    current_module: Option<&'a Module>,
    global_var_decl_cache: FxHashMap<GlobalVar, &'a GlobalVarDecl>,
    func_decl_cache: FxHashMap<Func, &'a FuncDecl>,

    nodes: Vec<Node<'a>>,
    use_counts: FxIndexMap<Use, usize>,
}

/// Helper for printing a mismatch error between two nodes (e.g. types), while
/// taking advantage of the print infrastructure that will print all dependencies.
pub struct ExpectedVsFound<E, F> {
    pub expected: E,
    pub found: F,
}

/// Printing `Plan` entry, an effective reification of SPIR-T's implicit DAG.
#[derive(Copy, Clone)]
enum Node<'a> {
    /// Nodes that involve interning and require extra processing to print
    /// (see also `InternedNode`).
    Interned(InternedNode),

    GlobalVar(GlobalVar),
    Func(Func),

    /// Other nodes, which only need to provide a way to collect dependencies
    /// (via `InnerVisit`) and then print the node itself.
    ///
    /// The `dyn Trait` approach allows supporting custom user types "for free",
    /// as well as deduplicating repetitive handling of the base node types.
    Dyn(&'a dyn DynNode<'a>),
}

/// Subset of `Node` representing only nodes that involve interning, and which
/// get assigned "names" on the fly during printing.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
enum InternedNode {
    AttrSet(AttrSet),
    Type(Type),
    Const(Const),
}

impl InternedNode {
    fn category(self) -> &'static str {
        match self {
            Self::AttrSet(_) => "attrs",
            Self::Type(_) => "type",
            Self::Const(_) => "const",
        }
    }
}

trait DynNode<'a>: DynInnerVisit<'a, Plan<'a>> + Print<Output = pretty::Fragment> {}
impl<'a, T: DynInnerVisit<'a, Plan<'a>> + Print<Output = pretty::Fragment>> DynNode<'a> for T {}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
enum Use {
    Interned(InternedNode),

    GlobalVar(GlobalVar),
    Func(Func),

    ControlPointLabel(cfg::ControlPoint),

    ControlNodeOutput {
        control_node: ControlNode,
        output_idx: u32,
    },
    DataInstOutput(DataInst),
}

impl Use {
    fn category(self) -> &'static str {
        match self {
            Self::Interned(node) => node.category(),
            Self::GlobalVar(_) => "global_var",
            Self::Func(_) => "func",
            Self::ControlPointLabel(_) => "label",
            Self::ControlNodeOutput { .. } | Self::DataInstOutput(_) => "v",
        }
    }
}

impl<'a> Plan<'a> {
    pub fn empty(module: &'a Module) -> Self {
        Self {
            cx: module.cx_ref(),
            current_module: Some(module),
            global_var_decl_cache: FxHashMap::default(),
            func_decl_cache: FxHashMap::default(),
            nodes: vec![],
            use_counts: FxIndexMap::default(),
        }
    }

    /// Like `empty`, but without supporting anything module-stored (like global vars).
    pub fn empty_outside_module(cx: &'a Context) -> Self {
        Self {
            cx,
            current_module: None,
            global_var_decl_cache: FxHashMap::default(),
            func_decl_cache: FxHashMap::default(),
            nodes: vec![],
            use_counts: FxIndexMap::default(),
        }
    }

    /// Create a `Plan` with all of `root`'s dependencies, followed by `root` itself.
    pub fn for_root(
        module: &'a Module,
        root: &'a (impl DynInnerVisit<'a, Plan<'a>> + Print<Output = pretty::Fragment>),
    ) -> Self {
        let mut plan = Self::empty(module);
        plan.use_node(Node::Dyn(root));
        plan
    }

    /// Like `for_root`, but without supporting anything module-stored (like global vars).
    pub fn for_root_outside_module(
        cx: &'a Context,
        root: &'a (impl DynInnerVisit<'a, Plan<'a>> + Print<Output = pretty::Fragment>),
    ) -> Self {
        let mut plan = Self::empty_outside_module(cx);
        plan.use_node(Node::Dyn(root));
        plan
    }

    /// Create a `Plan` with all of `module`'s contents.
    ///
    /// Shorthand for `Plan::for_root(module, module)`.
    pub fn for_module(module: &'a Module) -> Self {
        Self::for_root(module, module)
    }

    /// Add `node` to the plan, after all of its dependencies.
    ///
    /// For `Node::Interned` (and the `Node` variants that are module-stored),
    /// only the first call recurses into the definition, subsequent calls only
    /// update its (internally tracked) "use count".
    fn use_node(&mut self, node: Node<'a>) {
        let visit_once_use = match node {
            Node::Interned(node) => Some(Use::Interned(node)),
            Node::GlobalVar(gv) => Some(Use::GlobalVar(gv)),
            Node::Func(func) => Some(Use::Func(func)),
            Node::Dyn(_) => None,
        };
        if let Some(visit_once_use) = visit_once_use {
            if let Some(use_count) = self.use_counts.get_mut(&visit_once_use) {
                *use_count += 1;
                return;
            }
        }

        // FIXME(eddyb) should this be a generic `inner_visit` method on `Node`?
        match node {
            Node::Interned(InternedNode::AttrSet(attrs)) => {
                self.visit_attr_set_def(&self.cx[attrs]);
            }
            Node::Interned(InternedNode::Type(ty)) => {
                self.visit_type_def(&self.cx[ty]);
            }
            Node::Interned(InternedNode::Const(ct)) => {
                self.visit_const_def(&self.cx[ct]);
            }

            Node::GlobalVar(gv) => match self.global_var_decl_cache.get(&gv).copied() {
                Some(gv_decl) => self.visit_global_var_decl(gv_decl),

                // FIXME(eddyb) should this be a hard error?
                None => {}
            },

            Node::Func(func) => match self.func_decl_cache.get(&func).copied() {
                Some(func_decl) => self.visit_func_decl(func_decl),

                // FIXME(eddyb) should this be a hard error?
                None => {}
            },

            // FIXME(eddyb) this could be an issue if `Visitor::visit_...` should
            // be intercepting this before the `inner_visit_with` part.
            Node::Dyn(node) => node.dyn_inner_visit_with(self),
        }

        self.nodes.push(node);

        if let Some(visit_once_use) = visit_once_use {
            *self.use_counts.entry(visit_once_use).or_default() += 1;
        }
    }
}

impl<'a> Visitor<'a> for Plan<'a> {
    fn visit_attr_set_use(&mut self, attrs: AttrSet) {
        self.use_node(Node::Interned(InternedNode::AttrSet(attrs)));
    }
    fn visit_type_use(&mut self, ty: Type) {
        self.use_node(Node::Interned(InternedNode::Type(ty)));
    }
    fn visit_const_use(&mut self, ct: Const) {
        self.use_node(Node::Interned(InternedNode::Const(ct)));
    }

    fn visit_global_var_use(&mut self, gv: GlobalVar) {
        match self.current_module {
            Some(module) => {
                self.global_var_decl_cache
                    .insert(gv, &module.global_vars[gv]);
            }

            // FIXME(eddyb) should this be a hard error?
            None => {}
        }
        self.use_node(Node::GlobalVar(gv));
    }

    fn visit_func_use(&mut self, func: Func) {
        match self.current_module {
            Some(module) => {
                use std::collections::hash_map::Entry;

                match self.func_decl_cache.entry(func) {
                    Entry::Occupied(_) => {
                        // Avoid infinite recursion for recursive functions.
                        return;
                    }
                    Entry::Vacant(entry) => {
                        entry.insert(&module.funcs[func]);
                    }
                }
            }

            // FIXME(eddyb) should this be a hard error?
            None => {}
        }
        self.use_node(Node::Func(func));
    }

    fn visit_module(&mut self, module: &'a Module) {
        let old_module = self.current_module.replace(module);
        self.use_node(Node::Dyn(module));
        self.current_module = old_module;
    }
    fn visit_module_dialect(&mut self, dialect: &'a ModuleDialect) {
        self.use_node(Node::Dyn(dialect));
    }
    fn visit_module_debug_info(&mut self, debug_info: &'a ModuleDebugInfo) {
        self.use_node(Node::Dyn(debug_info));
    }

    fn visit_func_decl(&mut self, func_decl: &'a FuncDecl) {
        if let DeclDef::Present(func_def_body) = &func_decl.def {
            // FIXME(eddyb) computing the RPO and not reusing it later isn't very
            // efficient, but there aren't any other ways to get the right order.
            for point in func_def_body.cfg.rev_post_order(func_def_body) {
                if let Some(control_inst) = func_def_body.cfg.control_insts.get(point) {
                    for &target in &control_inst.targets {
                        *self
                            .use_counts
                            .entry(Use::ControlPointLabel(target))
                            .or_default() += 1;
                    }
                }
            }
        }

        func_decl.inner_visit_with(self);
    }
    fn visit_value_use(&mut self, v: &'a Value) {
        match *v {
            Value::Const(_) | Value::FuncParam { .. } => {}

            Value::ControlNodeOutput {
                control_node,
                output_idx,
            } => {
                *self
                    .use_counts
                    .entry(Use::ControlNodeOutput {
                        control_node,
                        output_idx,
                    })
                    .or_default() += 1;
            }
            Value::DataInstOutput(inst) => {
                *self
                    .use_counts
                    .entry(Use::DataInstOutput(inst))
                    .or_default() += 1;
            }
        }
        v.inner_visit_with(self);
    }
}

// FIXME(eddyb) this should be more general but we lack a `Visit` trait, and
// `Type` doesn't implement `InnerVisit` (which would be the wrong trait anyway).
impl InnerVisit for ExpectedVsFound<Type, Type> {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        let Self { expected, found } = *self;

        visitor.visit_type_use(expected);
        visitor.visit_type_use(found);
    }
}

impl Plan<'_> {
    /// Print the whole `Plan` to a `pretty::Fragment` and perform layout on it.
    ///
    /// The resulting `pretty::FragmentPostLayout` value supports `fmt::Display`
    /// for convenience, but also more specific methods (e.g. HTML output).
    pub fn pretty_print(&self) -> pretty::FragmentPostLayout {
        let pretty = self.print(&Printer::new(self));

        // FIXME(eddyb) make max line width configurable.
        let max_line_width = 100;

        pretty.layout_with_max_line_width(max_line_width)
    }
}

pub struct Printer<'a, 'b> {
    cx: &'a Context,
    use_styles: FxHashMap<Use, UseStyle>,

    global_var_decl_cache: &'b FxHashMap<GlobalVar, &'a GlobalVarDecl>,
    func_decl_cache: &'b FxHashMap<Func, &'a FuncDecl>,
}

/// How an use of a node should be printed.
#[derive(Copy, Clone)]
enum UseStyle {
    /// Refer to this node by its category and an `idx` (e.g. `"attrs123"`).
    Anon {
        /// For intra-function `Use`s (i.e. `Use::ControlPointLabel` and values),
        /// this disambiguates the parent function (for e.g. anchors).
        parent_func: Option<Func>,

        idx: usize,
    },

    /// Print this node inline at the use site.
    Inline,
}

impl<'a, 'b> Printer<'a, 'b> {
    fn new(plan: &'b Plan<'a>) -> Self {
        let cx = plan.cx;
        let wk = &spv::spec::Spec::get().well_known;

        #[derive(Default)]
        struct AnonCounters {
            attr_sets: usize,
            types: usize,
            consts: usize,

            global_vars: usize,
            funcs: usize,
        }
        let mut anon_counters = AnonCounters::default();

        let mut use_styles: FxHashMap<_, _> = plan
            .use_counts
            .iter()
            .map(|(&use_kind, &use_count)| {
                // HACK(eddyb) these are assigned later.
                if let Use::ControlPointLabel(_)
                | Use::ControlNodeOutput { .. }
                | Use::DataInstOutput(_) = use_kind
                {
                    return (use_kind, UseStyle::Inline);
                }

                let inline = match use_kind {
                    Use::Interned(node) => {
                        use_count == 1
                            || match node {
                                InternedNode::AttrSet(attrs) => {
                                    let AttrSetDef { attrs } = &cx[attrs];
                                    attrs.len() <= 1
                                        || attrs.iter().any(|attr| {
                                            // HACK(eddyb) because of how these
                                            // are printed as comments outside
                                            // the `#{...}` syntax, they can't
                                            // work unless they're printed inline.
                                            matches!(attr, Attr::SpvDebugLine { .. })
                                        })
                                }
                                InternedNode::Type(ty) => {
                                    let ty_def = &cx[ty];

                                    // FIXME(eddyb) remove the duplication between
                                    // here and `TypeDef`'s `Print` impl.
                                    let has_compact_print = match &ty_def.ctor {
                                        TypeCtor::SpvInst(inst) => [
                                            wk.OpTypeBool,
                                            wk.OpTypeInt,
                                            wk.OpTypeFloat,
                                            wk.OpTypeVector,
                                        ]
                                        .contains(&inst.opcode),
                                    };

                                    has_compact_print || ty_def.ctor_args.is_empty()
                                }
                                InternedNode::Const(ct) => {
                                    let ct_def = &cx[ct];

                                    // FIXME(eddyb) remove the duplication between
                                    // here and `ConstDef`'s `Print` impl.
                                    let has_compact_print = match &ct_def.ctor {
                                        ConstCtor::SpvInst(inst) => {
                                            [wk.OpConstantFalse, wk.OpConstantTrue, wk.OpConstant]
                                                .contains(&inst.opcode)
                                        }
                                        _ => false,
                                    };

                                    has_compact_print || ct_def.ctor_args.is_empty()
                                }
                            }
                    }
                    Use::GlobalVar(_) | Use::Func(_) => false,
                    Use::ControlPointLabel(_)
                    | Use::ControlNodeOutput { .. }
                    | Use::DataInstOutput(_) => {
                        unreachable!()
                    }
                };
                let style = if inline {
                    UseStyle::Inline
                } else {
                    let ac = &mut anon_counters;
                    let counter = match use_kind {
                        Use::Interned(InternedNode::AttrSet(_)) => &mut ac.attr_sets,
                        Use::Interned(InternedNode::Type(_)) => &mut ac.types,
                        Use::Interned(InternedNode::Const(_)) => &mut ac.consts,
                        Use::GlobalVar(_) => &mut ac.global_vars,
                        Use::Func(_) => &mut ac.funcs,
                        Use::ControlPointLabel(_)
                        | Use::ControlNodeOutput { .. }
                        | Use::DataInstOutput(_) => {
                            unreachable!()
                        }
                    };
                    let idx = *counter;
                    *counter += 1;
                    UseStyle::Anon {
                        parent_func: None,
                        idx,
                    }
                };
                (use_kind, style)
            })
            .collect();

        for (&func, &func_decl) in &plan.func_decl_cache {
            if let DeclDef::Present(func_def_body) = &func_decl.def {
                assert!(matches!(
                    use_styles.get(&Use::Func(func)),
                    Some(UseStyle::Anon { .. })
                ));

                let mut control_pointer_label_counter = 0;
                let mut value_counter = 0;

                for point in func_def_body.cfg.rev_post_order(func_def_body) {
                    if let Some(use_style) = use_styles.get_mut(&Use::ControlPointLabel(point)) {
                        let idx = control_pointer_label_counter;
                        control_pointer_label_counter += 1;
                        *use_style = UseStyle::Anon {
                            parent_func: Some(func),
                            idx,
                        };
                    }

                    // HACK(eddyb) this needs to visit `UnstructuredMerge`s on `Exit`
                    // instead of `Entry`, because they don't have have `Entry`s.
                    let can_uniquely_visit =
                        match func_def_body.control_nodes[point.control_node()].kind {
                            ControlNodeKind::UnstructuredMerge => {
                                assert!(matches!(point, cfg::ControlPoint::Exit(_)));
                                true
                            }
                            _ => matches!(point, cfg::ControlPoint::Entry(_)),
                        };

                    if !can_uniquely_visit {
                        continue;
                    }

                    let control_node = point.control_node();
                    let ControlNodeDef { kind, outputs } =
                        &*func_def_body.control_nodes[control_node];

                    let block_insts = match *kind {
                        ControlNodeKind::UnstructuredMerge => None,
                        ControlNodeKind::Block { insts } => insts,
                    };

                    let defined_values =
                        func_def_body
                            .at(block_insts)
                            .into_iter()
                            .filter(|func_at_inst| func_at_inst.def().output_type.is_some())
                            .map(|func_at_inst| Use::DataInstOutput(func_at_inst.position))
                            .chain(outputs.iter().enumerate().map(|(i, _)| {
                                Use::ControlNodeOutput {
                                    control_node,
                                    output_idx: i.try_into().unwrap(),
                                }
                            }));
                    for use_kind in defined_values {
                        if let Some(use_style) = use_styles.get_mut(&use_kind) {
                            let idx = value_counter;
                            value_counter += 1;
                            *use_style = UseStyle::Anon {
                                parent_func: Some(func),
                                idx,
                            };
                        }
                    }
                }
            }
        }

        Self {
            cx,
            use_styles,
            global_var_decl_cache: &plan.global_var_decl_cache,
            func_decl_cache: &plan.func_decl_cache,
        }
    }

    pub fn cx(&self) -> &'a Context {
        self.cx
    }

    // Styles for a variety of syntactic categories.
    // FIXME(eddyb) this is a somewhat inefficient way of declaring these.

    fn error_style(&self) -> pretty::Styles {
        pretty::Styles::color(pretty::palettes::simple::MAGENTA)
    }
    fn comment_style(&self) -> pretty::Styles {
        pretty::Styles {
            opacity: Some(0.2),
            ..Default::default()
        }
    }
    fn numeric_literal_style(&self) -> pretty::Styles {
        pretty::Styles::color(pretty::palettes::simple::YELLOW)
    }
    fn string_literal_style(&self) -> pretty::Styles {
        pretty::Styles::color(pretty::palettes::simple::RED)
    }
    fn declarative_keyword_style(&self) -> pretty::Styles {
        pretty::Styles::color(pretty::palettes::simple::BLUE)
    }
    fn imperative_keyword_style(&self) -> pretty::Styles {
        pretty::Styles::color(pretty::palettes::simple::MAGENTA)
    }
    fn spv_operand_kind_name_style(&self) -> pretty::Styles {
        // HACK(eddyb) effectively this is almost always redundant.
        pretty::Styles {
            opacity: Some(0.4),
            ..self.declarative_keyword_style()
        }
    }
    fn spv_enumerand_name_style(&self) -> pretty::Styles {
        pretty::Styles::color(pretty::palettes::simple::CYAN)
    }
    fn attr_style(&self) -> pretty::Styles {
        pretty::Styles {
            color: Some(pretty::palettes::simple::GREEN),
            opacity: Some(0.6),
            ..Default::default()
        }
    }

    /// Pretty-print a `: T` style "type ascription" suffix.
    ///
    /// This should be used everywhere some type ascription notation is needed,
    /// to ensure consistency across all such situations.
    fn pretty_type_ascription_suffix(&self, ty: Type) -> pretty::Fragment {
        pretty::join_space(":", [ty.print(self)])
    }

    /// Pretty-print a single SPIR-V operand from only immediates, potentially
    /// composed of an enumerand with parameters (which consumes more immediates).
    fn pretty_spv_operand_from_imms(
        &self,
        imms: impl IntoIterator<Item = spv::Imm>,
    ) -> pretty::Fragment {
        // FIXME(eddyb) deduplicate the `Token` match with `pretty_spv_inst`.
        pretty::Fragment::new(
            spv::print::operand_from_imms(imms)
                .tokens
                .into_iter()
                .map(|token| match token {
                    spv::print::Token::Error(s) => self.error_style().apply(s),
                    spv::print::Token::Punctuation(s) => s.into(),
                    spv::print::Token::OperandKindName(s) => {
                        self.spv_operand_kind_name_style().apply(s)
                    }
                    spv::print::Token::EnumerandName(s) => self.spv_enumerand_name_style().apply(s),
                    spv::print::Token::NumericLiteral(s) => self.numeric_literal_style().apply(s),
                    spv::print::Token::StringLiteral(s) => self.string_literal_style().apply(s),
                    spv::print::Token::Id(_) => unreachable!(),
                }),
        )
    }

    /// Pretty-print a single SPIR-V (short) immediate (e.g. an enumerand).
    fn pretty_spv_imm(&self, kind: spv::spec::OperandKind, word: u32) -> pretty::Fragment {
        self.pretty_spv_operand_from_imms([spv::Imm::Short(kind, word)])
    }

    /// Pretty-print an arbitrary SPIR-V `opcode` with `imms` and `ids` as its
    /// SPIR-V operands (with each `ID` in `ids` passed through `print_id`),
    /// and optionally with a ` : ...` type ascription at the end (`result_type`).
    ///
    /// `print_id` can return `None` to indicate an ID operand is implicit in
    /// SPIR-T, and should not be printed (e.g. decorations' target IDs).
    /// But if `print_id` doesn't need to return `Option<_>` (for `None`), its
    /// return type can skip the `Option` entirely (which allows passing in the
    /// `Print::print` method, instead of a closure, as `print_id`).
    ///
    /// Immediate operands are wrapped in angle brackets, while `ID` operands are
    /// wrapped in parentheses, e.g.: `OpFoo<Bar, 123, "baz">(v1, v2)`.
    ///
    /// This should be used everywhere a SPIR-V instruction needs to be printed,
    /// to ensure consistency across all such situations.
    fn pretty_spv_inst<ID: Copy, OPF: Into<Option<pretty::Fragment>>>(
        &self,
        spv_inst_name_style: pretty::Styles,
        opcode: spv::spec::Opcode,
        imms: &[spv::Imm],
        ids: impl IntoIterator<Item = ID>,
        print_id: impl Fn(ID, &Self) -> OPF,
        result_type: Option<Type>,
    ) -> pretty::Fragment {
        // Split operands into "angle brackets" (immediates) and "parens" (IDs),
        // with compound operands (i.e. enumerand with ID parameter) using both,
        // e.g: `OpFoo<Bar(/* #0 */)>(/* #0 */ v123)`.
        let mut next_extra_idx: usize = 0;
        let mut paren_operands = SmallVec::<[_; 16]>::new();
        let mut angle_bracket_operands =
            spv::print::inst_operands(opcode, imms.iter().copied(), ids)
                .filter_map(|operand| {
                    if let [spv::print::Token::Id(id)] = operand.tokens[..] {
                        paren_operands.extend(print_id(id, self).into());
                        None
                    } else {
                        // FIXME(eddyb) deduplicate the `Token` match with `pretty_spv_operand_from_imms`.
                        Some(pretty::Fragment::new(operand.tokens.into_iter().map(
                            |token| match token {
                                spv::print::Token::Error(s) => self.error_style().apply(s),
                                spv::print::Token::Punctuation(s) => s.into(),
                                spv::print::Token::OperandKindName(s) => {
                                    self.spv_operand_kind_name_style().apply(s)
                                }
                                spv::print::Token::EnumerandName(s) => {
                                    self.spv_enumerand_name_style().apply(s)
                                }
                                spv::print::Token::NumericLiteral(s) => {
                                    self.numeric_literal_style().apply(s)
                                }
                                spv::print::Token::StringLiteral(s) => {
                                    self.string_literal_style().apply(s)
                                }
                                spv::print::Token::Id(id) => {
                                    let comment = self
                                        .comment_style()
                                        .apply(format!("/* #{} */", next_extra_idx));
                                    next_extra_idx += 1;

                                    let id = print_id(id, self).into().unwrap_or_else(|| {
                                        self.comment_style().apply("/* implicit ID */").into()
                                    });
                                    paren_operands.push(pretty::join_space(comment.clone(), [id]));

                                    comment
                                }
                            },
                        )))
                    }
                })
                .peekable();

        // Put together all the pieces, angle-bracketed operands then parenthesized
        // ones, e.g.: `OpFoo<Bar, 123, "baz">(v1, v2)` (with either group optional).
        let mut out = spv_inst_name_style.apply(opcode.name()).into();

        if angle_bracket_operands.peek().is_some() {
            out = pretty::Fragment::new([
                out,
                pretty::join_comma_sep("<", angle_bracket_operands, ">"),
            ]);
        }

        if !paren_operands.is_empty() {
            out = pretty::Fragment::new([out, pretty::join_comma_sep("(", paren_operands, ")")]);
        }

        if let Some(ty) = result_type {
            out = pretty::Fragment::new([out, self.pretty_type_ascription_suffix(ty)]);
        }

        out
    }
}

pub trait Print {
    type Output;
    fn print(&self, printer: &Printer<'_, '_>) -> Self::Output;
}

impl<E: Print<Output = pretty::Fragment>, F: Print<Output = pretty::Fragment>> Print
    for ExpectedVsFound<E, F>
{
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_, '_>) -> pretty::Fragment {
        let Self { expected, found } = self;

        pretty::Fragment::new([
            "expected: ".into(),
            expected.print(printer),
            pretty::Node::ForceLineSeparation.into(),
            "found: ".into(),
            found.print(printer),
        ])
    }
}

/// A `Print` `Output` type that splits the attributes from the main body of the
/// definition, allowing additional processing before they get concatenated.
#[derive(Default)]
pub struct AttrsAndDef {
    pub attrs: pretty::Fragment,
    pub def: pretty::Fragment,
}

impl Use {
    /// Common implementation for `Use::print` and `Use::print_as_def`.
    fn print_as_ref_or_def(&self, printer: &Printer<'_, '_>, is_def: bool) -> pretty::Fragment {
        let style = printer
            .use_styles
            .get(self)
            .copied()
            .unwrap_or(UseStyle::Inline);
        match style {
            UseStyle::Anon { parent_func, idx } => {
                let name = format!("{}{}", self.category(), idx);
                let anchor = if let Some(func) = parent_func {
                    // Disambiguate intra-function anchors (labels/values) by
                    // prepending a prefix of the form `func123_`.
                    let func = Use::Func(func);
                    let func_idx = match printer.use_styles[&func] {
                        UseStyle::Anon { idx, .. } => idx,
                        _ => unreachable!(),
                    };
                    format!("{}{}_{}", func.category(), func_idx, name)
                } else {
                    // FIXME(eddyb) avoid having to clone `String`s here.
                    name.clone()
                };
                let (name, name_style) = match self {
                    Self::Interned(InternedNode::AttrSet(_)) => {
                        (format!("#{name}"), printer.attr_style())
                    }
                    _ => (name, Default::default()),
                };
                let name = pretty::Styles {
                    anchor: Some(anchor),
                    anchor_is_def: is_def,
                    ..name_style
                }
                .apply(name);
                match self {
                    Self::Interned(InternedNode::AttrSet(_)) => {
                        // HACK(eddyb) separate `AttrSet` uses from their target.
                        pretty::Fragment::new([name, pretty::Node::ForceLineSeparation])
                    }
                    _ => name.into(),
                }
            }
            UseStyle::Inline => match *self {
                Self::Interned(node) => {
                    let AttrsAndDef {
                        attrs: attrs_of_def,
                        def,
                    } = node.print(printer);
                    pretty::Fragment::new([attrs_of_def, def])
                }
                Self::GlobalVar(_) => "/* unused global_var */_".into(),
                Self::Func(_) => "/* unused func */_".into(),
                Self::ControlPointLabel(_)
                | Self::ControlNodeOutput { .. }
                | Self::DataInstOutput(_) => "_".into(),
            },
        }
    }

    fn print_as_def(&self, printer: &Printer<'_, '_>) -> pretty::Fragment {
        self.print_as_ref_or_def(printer, true)
    }
}

impl Print for Use {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_, '_>) -> pretty::Fragment {
        self.print_as_ref_or_def(printer, false)
    }
}

// Interned/module-stored nodes dispatch through the `Use` impl above.
impl Print for AttrSet {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_, '_>) -> pretty::Fragment {
        Use::Interned(InternedNode::AttrSet(*self)).print(printer)
    }
}
impl Print for Type {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_, '_>) -> pretty::Fragment {
        Use::Interned(InternedNode::Type(*self)).print(printer)
    }
}
impl Print for Const {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_, '_>) -> pretty::Fragment {
        Use::Interned(InternedNode::Const(*self)).print(printer)
    }
}
impl Print for GlobalVar {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_, '_>) -> pretty::Fragment {
        Use::GlobalVar(*self).print(printer)
    }
}
impl Print for Func {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_, '_>) -> pretty::Fragment {
        Use::Func(*self).print(printer)
    }
}

// NOTE(eddyb) the `Print` impl for `Node` is for the top-level definition,
// *not* any uses (which go through the `Print` impls above).

impl Print for Plan<'_> {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_, '_>) -> pretty::Fragment {
        let mut out = pretty::Fragment::default();

        let mut first = true;
        for &node in &self.nodes {
            let AttrsAndDef { mut attrs, mut def } = node.print(printer);

            // HACK(eddyb) move an anchor def at the start of `def` to an empty
            // anchor just before attributes, so that navigating to the anchor
            // does not "hide" those attributes.
            if let [pretty::Node::StyledText(ref mut styles_and_text), ..] = def.nodes[..] {
                let styles = &mut styles_and_text.0;
                if !attrs.nodes.is_empty() && mem::take(&mut styles.anchor_is_def) {
                    attrs.nodes.insert(
                        0,
                        pretty::Styles {
                            anchor: styles.anchor.clone(),
                            anchor_is_def: true,
                            ..Default::default()
                        }
                        .apply(""),
                    );
                }
            }

            let def = pretty::Fragment::new([attrs, def.into()]);
            if !def.nodes.is_empty() {
                // Visually separate top-level definitions.
                if !first {
                    // FIXME(eddyb) have an explicit `pretty::Node`
                    // for "vertical gap" instead.
                    out.nodes.push("\n\n".into());
                }
                first = false;

                // FIXME(eddyb) this should probably be `out += def;`.
                out.nodes.extend(def.nodes);
                out.nodes.push(pretty::Node::ForceLineSeparation.into());
            }
        }

        out
    }
}

impl Print for Node<'_> {
    type Output = AttrsAndDef;
    fn print(&self, printer: &Printer<'_, '_>) -> AttrsAndDef {
        match *self {
            Self::Interned(node) => match printer.use_styles.get(&Use::Interned(node)).copied() {
                Some(UseStyle::Anon {
                    parent_func: _,
                    idx,
                }) => {
                    let AttrsAndDef {
                        attrs: attrs_of_def,
                        def,
                    } = node.print(printer);

                    let name = format!("{}{}", node.category(), idx);
                    let name = pretty::Styles {
                        // FIXME(eddyb) avoid having to clone `String`s here.
                        anchor: Some(name.clone()),
                        anchor_is_def: true,
                        ..Default::default()
                    }
                    .apply(name);

                    AttrsAndDef {
                        attrs: attrs_of_def,
                        def: pretty::Fragment::new([name.into(), " = ".into(), def]),
                    }
                }
                _ => AttrsAndDef::default(),
            },

            Self::GlobalVar(gv) => match printer.global_var_decl_cache.get(&gv) {
                Some(gv_decl) => {
                    let AttrsAndDef { attrs, def } = gv_decl.print(printer);
                    AttrsAndDef {
                        attrs,
                        def: pretty::Fragment::new([Use::GlobalVar(gv).print_as_def(printer), def]),
                    }
                }
                None => AttrsAndDef::default(),
            },

            Self::Func(func) => match printer.func_decl_cache.get(&func) {
                Some(func_decl) => {
                    let AttrsAndDef { attrs, def } = func_decl.print(printer);
                    AttrsAndDef {
                        attrs,
                        def: pretty::Fragment::new([Use::Func(func).print_as_def(printer), def]),
                    }
                }
                None => AttrsAndDef::default(),
            },

            Self::Dyn(node) => AttrsAndDef {
                attrs: pretty::Fragment::default(),
                def: node.print(printer),
            },
        }
    }
}

impl Print for Module {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_, '_>) -> pretty::Fragment {
        if self.exports.is_empty() {
            return pretty::Fragment::default();
        }

        pretty::Fragment::new([
            printer.declarative_keyword_style().apply("export").into(),
            " ".into(),
            pretty::join_comma_sep(
                "{",
                self.exports
                    .iter()
                    .map(|(export_key, exportee)| {
                        pretty::Fragment::new([
                            export_key.print(printer).into(),
                            ": ".into(),
                            exportee.print(printer),
                        ])
                    })
                    .map(|entry| {
                        pretty::Fragment::new([pretty::Node::ForceLineSeparation.into(), entry])
                    }),
                "}",
            ),
        ])
    }
}

impl Print for ModuleDialect {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_, '_>) -> pretty::Fragment {
        let dialect = match self {
            Self::Spv(spv::Dialect {
                version_major,
                version_minor,
                capabilities,
                extensions,
                addressing_model,
                memory_model,
            }) => {
                let wk = &spv::spec::Spec::get().well_known;

                pretty::join_comma_sep(
                    "SPIR-V {",
                    [
                        pretty::Fragment::new([
                            "version: ".into(),
                            printer
                                .numeric_literal_style()
                                .apply(format!("{}.{}", version_major, version_minor)),
                        ]),
                        pretty::join_comma_sep(
                            "extensions: {",
                            extensions.iter().map(|ext| {
                                printer.string_literal_style().apply(format!("{:?}", ext))
                            }),
                            "}",
                        ),
                        pretty::join_comma_sep(
                            "capabilities: {",
                            capabilities
                                .iter()
                                .map(|&cap| printer.pretty_spv_imm(wk.Capability, cap)),
                            "}",
                        ),
                        pretty::Fragment::new([
                            "addressing_model: ".into(),
                            printer.pretty_spv_imm(wk.AddressingModel, *addressing_model),
                        ]),
                        pretty::Fragment::new([
                            "memory_model: ".into(),
                            printer.pretty_spv_imm(wk.MemoryModel, *memory_model),
                        ]),
                    ]
                    .into_iter()
                    .map(|entry| {
                        pretty::Fragment::new([pretty::Node::ForceLineSeparation.into(), entry])
                    }),
                    "}",
                )
            }
        };
        pretty::Fragment::new([
            printer
                .declarative_keyword_style()
                .apply("module.dialect")
                .into(),
            " = ".into(),
            dialect,
        ])
    }
}

impl Print for ModuleDebugInfo {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_, '_>) -> pretty::Fragment {
        let debug_info = match self {
            Self::Spv(spv::ModuleDebugInfo {
                original_generator_magic,
                source_languages,
                source_extensions,
                module_processes,
            }) => {
                let wk = &spv::spec::Spec::get().well_known;

                pretty::join_comma_sep(
                    "SPIR-V {",
                    [
                        pretty::Fragment::new([
                            "generator: ".into(),
                            original_generator_magic
                                .map(|generator_magic| {
                                    let (tool_id, tool_version) =
                                        (generator_magic.get() >> 16, generator_magic.get() as u16);
                                    pretty::Fragment::new([
                                        "{ tool_id: ".into(),
                                        printer
                                            .numeric_literal_style()
                                            .apply(format!("{}", tool_id)),
                                        ", version: ".into(),
                                        printer
                                            .numeric_literal_style()
                                            .apply(format!("{}", tool_version)),
                                        " }".into(),
                                    ])
                                })
                                .unwrap_or_else(|| "unknown".into()),
                        ]),
                        pretty::join_comma_sep(
                            "source_languages: {",
                            source_languages
                                .iter()
                                .map(|(lang, sources)| {
                                    let spv::DebugSources { file_contents } = sources;
                                    pretty::Fragment::new([
                                        printer.pretty_spv_imm(wk.SourceLanguage, lang.lang),
                                        " { version: ".into(),
                                        printer
                                            .numeric_literal_style()
                                            .apply(format!("{}", lang.version))
                                            .into(),
                                        " }: ".into(),
                                        pretty::join_comma_sep(
                                            "{",
                                            file_contents
                                                .iter()
                                                .map(|(&file, contents)| {
                                                    format!(
                                                        "{:?}: {:?}",
                                                        &printer.cx[file], contents
                                                    )
                                                })
                                                .map(|entry| {
                                                    pretty::Fragment::new([
                                                        pretty::Node::ForceLineSeparation,
                                                        entry.into(),
                                                    ])
                                                }),
                                            "}",
                                        ),
                                    ])
                                })
                                .map(|entry| {
                                    pretty::Fragment::new([
                                        pretty::Node::ForceLineSeparation.into(),
                                        entry,
                                    ])
                                }),
                            "}",
                        ),
                        format!("source_extensions: {:?}", source_extensions).into(),
                        format!("module_processes: {:?}", module_processes).into(),
                    ]
                    .into_iter()
                    .map(|entry| {
                        pretty::Fragment::new([pretty::Node::ForceLineSeparation.into(), entry])
                    }),
                    "}",
                )
            }
        };
        pretty::Fragment::new([
            printer
                .declarative_keyword_style()
                .apply("module.debug_info")
                .into(),
            " = ".into(),
            debug_info,
        ])
    }
}

impl Print for ExportKey {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_, '_>) -> pretty::Fragment {
        match self {
            &Self::LinkName(name) => printer
                .string_literal_style()
                .apply(format!("{:?}", &printer.cx[name]))
                .into(),

            // HACK(eddyb) `interface_global_vars` should be recomputed by
            // `spv::lift` anyway, so hiding them here mimics that.
            Self::SpvEntryPoint {
                imms,
                interface_global_vars: _,
            } => {
                let wk = &spv::spec::Spec::get().well_known;

                struct ImplicitTargetId;

                printer.pretty_spv_inst(
                    printer.declarative_keyword_style(),
                    wk.OpEntryPoint,
                    imms,
                    &[ImplicitTargetId],
                    |ImplicitTargetId, _| None,
                    None,
                )
            }
        }
    }
}

impl Print for Exportee {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_, '_>) -> pretty::Fragment {
        match *self {
            Self::GlobalVar(gv) => gv.print(printer),
            Self::Func(func) => func.print(printer),
        }
    }
}

impl Print for InternedNode {
    type Output = AttrsAndDef;
    fn print(&self, printer: &Printer<'_, '_>) -> AttrsAndDef {
        match *self {
            Self::AttrSet(attrs) => AttrsAndDef {
                attrs: pretty::Fragment::default(),
                def: printer.cx[attrs].print(printer),
            },
            Self::Type(ty) => printer.cx[ty].print(printer),
            Self::Const(ct) => printer.cx[ct].print(printer),
        }
    }
}

impl Print for AttrSetDef {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_, '_>) -> pretty::Fragment {
        let Self { attrs } = self;

        let mut comments = SmallVec::<[_; 1]>::new();
        let mut non_comment_attrs = SmallVec::<[_; 4]>::new();
        for attr in attrs {
            let (attr_style, attr) = attr.print(printer);
            match attr_style {
                AttrStyle::Comment => comments.push(attr),
                AttrStyle::NonComment => non_comment_attrs.push(attr),
            }
        }

        let non_comment_attrs = if non_comment_attrs.is_empty() {
            None
        } else {
            // FIXME(eddyb) remove this special-case by having some mode for
            // "prefer multi-line but admit a single-element compact form"
            // (a comma that's always `,\n`, effectively)
            let per_attr_prefix = if non_comment_attrs.len() > 1 {
                Some(pretty::Node::ForceLineSeparation.into())
            } else {
                None
            };

            // FIXME(eddyb) apply `attr_style` to more than just `#{` and `}`.
            Some(pretty::join_comma_sep(
                printer.attr_style().apply("#{"),
                non_comment_attrs.into_iter().map(|attr| {
                    pretty::Fragment::new(per_attr_prefix.clone().into_iter().chain([attr]))
                }),
                printer.attr_style().apply("}"),
            ))
        };

        pretty::Fragment::new(
            non_comment_attrs
                .into_iter()
                .chain(comments)
                .flat_map(|entry| [entry, pretty::Node::ForceLineSeparation.into()]),
        )
    }
}

pub enum AttrStyle {
    Comment,
    NonComment,
}

impl Print for Attr {
    type Output = (AttrStyle, pretty::Fragment);
    fn print(&self, printer: &Printer<'_, '_>) -> (AttrStyle, pretty::Fragment) {
        match self {
            Attr::SpvAnnotation(spv::Inst { opcode, imms }) => {
                struct ImplicitTargetId;

                (
                    AttrStyle::NonComment,
                    printer.pretty_spv_inst(
                        printer.attr_style(),
                        *opcode,
                        imms,
                        &[ImplicitTargetId],
                        |ImplicitTargetId, _| None,
                        None,
                    ),
                )
            }
            &Attr::SpvDebugLine {
                file_path,
                line,
                col,
            } => {
                // HACK(eddyb) Rust-GPU's column numbers seem
                // off-by-one wrt what e.g. VSCode expects
                // for `:line:col` syntax, but it's hard to
                // tell from the spec and `glslang` doesn't
                // even emit column numbers at all!
                let col = col + 1;

                // HACK(eddyb) only use skip string quoting
                // and escaping for well-behaved file paths.
                let file_path = &printer.cx[file_path.0];
                let comment = if file_path.chars().all(|c| c.is_ascii_graphic() && c != ':') {
                    format!("// at {}:{}:{}", file_path, line, col)
                } else {
                    format!("// at {:?}:{}:{}", file_path, line, col)
                };
                (
                    AttrStyle::Comment,
                    printer.comment_style().apply(comment).into(),
                )
            }
            &Attr::SpvBitflagsOperand(imm) => (
                AttrStyle::NonComment,
                printer.pretty_spv_operand_from_imms([imm]),
            ),
        }
    }
}

impl Print for TypeDef {
    type Output = AttrsAndDef;
    fn print(&self, printer: &Printer<'_, '_>) -> AttrsAndDef {
        let Self {
            attrs,
            ctor,
            ctor_args,
        } = self;

        let wk = &spv::spec::Spec::get().well_known;

        // FIXME(eddyb) should this be done by lowering SPIR-V types to SPIR-T?
        let kw = |kw| printer.declarative_keyword_style().apply(kw).into();
        #[allow(irrefutable_let_patterns)]
        let compact_def = if let &TypeCtor::SpvInst(spv::Inst { opcode, ref imms }) = ctor {
            if opcode == wk.OpTypeBool {
                Some(kw("bool".into()))
            } else if opcode == wk.OpTypeInt {
                let (width, signed) = match imms[..] {
                    [spv::Imm::Short(_, width), spv::Imm::Short(_, signedness)] => {
                        (width, signedness != 0)
                    }
                    _ => unreachable!(),
                };

                Some(if signed {
                    kw(format!("s{}", width))
                } else {
                    kw(format!("u{}", width))
                })
            } else if opcode == wk.OpTypeFloat {
                let width = match imms[..] {
                    [spv::Imm::Short(_, width)] => width,
                    _ => unreachable!(),
                };

                Some(kw(format!("f{}", width)))
            } else if opcode == wk.OpTypeVector {
                let (elem_ty, elem_count) = match (&imms[..], &ctor_args[..]) {
                    (&[spv::Imm::Short(_, elem_count)], &[TypeCtorArg::Type(elem_ty)]) => {
                        (elem_ty, elem_count)
                    }
                    _ => unreachable!(),
                };

                Some(pretty::Fragment::new([
                    elem_ty.print(printer),
                    "×".into(),
                    printer
                        .numeric_literal_style()
                        .apply(format!("{}", elem_count))
                        .into(),
                ]))
            } else {
                None
            }
        } else {
            None
        };

        AttrsAndDef {
            attrs: attrs.print(printer),
            def: if let Some(def) = compact_def {
                def
            } else {
                match *ctor {
                    TypeCtor::SpvInst(spv::Inst { opcode, ref imms }) => printer.pretty_spv_inst(
                        printer.declarative_keyword_style(),
                        opcode,
                        imms,
                        ctor_args,
                        |&arg, printer| match arg {
                            TypeCtorArg::Type(ty) => ty.print(printer),
                            TypeCtorArg::Const(ct) => ct.print(printer),
                        },
                        None,
                    ),
                }
            },
        }
    }
}

impl Print for ConstDef {
    type Output = AttrsAndDef;
    fn print(&self, printer: &Printer<'_, '_>) -> AttrsAndDef {
        let Self {
            attrs,
            ty,
            ctor,
            ctor_args,
        } = self;

        let wk = &spv::spec::Spec::get().well_known;

        let kw = |kw| printer.declarative_keyword_style().apply(kw).into();
        let compact_def = if let &ConstCtor::SpvInst(spv::Inst { opcode, ref imms }) = ctor {
            if opcode == wk.OpConstantFalse {
                Some(kw("false"))
            } else if opcode == wk.OpConstantTrue {
                Some(kw("true"))
            } else if opcode == wk.OpConstant {
                // HACK(eddyb) it's simpler to only handle a limited subset of
                // integer/float bit-widths, for now.
                let raw_bits = match imms[..] {
                    [spv::Imm::Short(_, x)] => Some(u64::from(x)),
                    [spv::Imm::LongStart(_, lo), spv::Imm::LongCont(_, hi)] => {
                        Some(u64::from(lo) | (u64::from(hi) << 32))
                    }
                    _ => None,
                };

                if let (
                    Some(raw_bits),
                    &TypeCtor::SpvInst(spv::Inst {
                        opcode: ty_opcode,
                        imms: ref ty_imms,
                    }),
                ) = (raw_bits, &printer.cx[*ty].ctor)
                {
                    if ty_opcode == wk.OpTypeInt {
                        let (width, signed) = match ty_imms[..] {
                            [spv::Imm::Short(_, width), spv::Imm::Short(_, signedness)] => {
                                (width, signedness != 0)
                            }
                            _ => unreachable!(),
                        };

                        if width <= 64 {
                            Some(printer.numeric_literal_style().apply(if signed {
                                let sext_raw_bits =
                                    (raw_bits as u128 as i128) << (128 - width) >> (128 - width);
                                format!("{}s{}", sext_raw_bits, width)
                            } else {
                                format!("{}u{}", raw_bits, width)
                            }))
                        } else {
                            None
                        }
                    } else if ty_opcode == wk.OpTypeFloat {
                        let width = match ty_imms[..] {
                            [spv::Imm::Short(_, width)] => width,
                            _ => unreachable!(),
                        };

                        /// Check that parsing the result of printing produces
                        /// the original bits of the floating-point value, and
                        /// only return `Some` if that is the case.
                        fn bitwise_roundtrip_float_print<
                            BITS: Copy + PartialEq,
                            FLOAT: std::fmt::Debug + std::str::FromStr,
                        >(
                            bits: BITS,
                            float_from_bits: impl FnOnce(BITS) -> FLOAT,
                            float_to_bits: impl FnOnce(FLOAT) -> BITS,
                        ) -> Option<String> {
                            let float = float_from_bits(bits);
                            Some(format!("{:?}", float)).filter(|s| {
                                s.parse::<FLOAT>()
                                    .map(float_to_bits)
                                    .map_or(false, |roundtrip_bits| roundtrip_bits == bits)
                            })
                        }

                        let printed_value = match width {
                            32 => bitwise_roundtrip_float_print(
                                raw_bits as u32,
                                f32::from_bits,
                                f32::to_bits,
                            ),
                            64 => bitwise_roundtrip_float_print(
                                raw_bits,
                                f64::from_bits,
                                f64::to_bits,
                            ),
                            _ => None,
                        };
                        printed_value.map(|s| {
                            printer
                                .numeric_literal_style()
                                .apply(format!("{}f{}", s, width))
                        })
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        };

        AttrsAndDef {
            attrs: attrs.print(printer),
            def: if let Some(def) = compact_def {
                def.into()
            } else {
                match *ctor {
                    ConstCtor::PtrToGlobalVar(gv) => {
                        pretty::Fragment::new(["&".into(), gv.print(printer)])
                    }
                    ConstCtor::SpvInst(spv::Inst { opcode, ref imms }) => printer.pretty_spv_inst(
                        printer.declarative_keyword_style(),
                        opcode,
                        imms,
                        ctor_args,
                        Print::print,
                        Some(*ty),
                    ),
                }
            },
        }
    }
}

impl Print for Import {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_, '_>) -> pretty::Fragment {
        match self {
            &Self::LinkName(name) => pretty::Fragment::new([
                printer.declarative_keyword_style().apply("import"),
                " ".into(),
                printer
                    .string_literal_style()
                    .apply(format!("{:?}", &printer.cx[name])),
            ]),
        }
    }
}

impl Print for GlobalVarDecl {
    type Output = AttrsAndDef;
    fn print(&self, printer: &Printer<'_, '_>) -> AttrsAndDef {
        let Self {
            attrs,
            type_of_ptr_to,
            addr_space,
            def,
        } = self;

        let wk = &spv::spec::Spec::get().well_known;

        let type_ascription_suffix = {
            // HACK(eddyb) get the pointee type from SPIR-V `OpTypePointer`, but
            // ideally the `GlobalVarDecl` would hold that type itself.
            let type_of_ptr_to_def = &printer.cx[*type_of_ptr_to];

            match &type_of_ptr_to_def.ctor {
                TypeCtor::SpvInst(inst) if inst.opcode == wk.OpTypePointer => {
                    match type_of_ptr_to_def.ctor_args[..] {
                        [TypeCtorArg::Type(ty)] => printer.pretty_type_ascription_suffix(ty),
                        _ => unreachable!(),
                    }
                }
                _ => pretty::Fragment::new([
                    ": ".into(),
                    printer.error_style().apply("pointee_type_of").into(),
                    "(".into(),
                    type_of_ptr_to.print(printer),
                    ")".into(),
                ]),
            }
        };
        let addr_space = match *addr_space {
            AddrSpace::SpvStorageClass(sc) => printer.pretty_spv_imm(wk.StorageClass, sc),
        };
        let header = pretty::Fragment::new([" in ".into(), addr_space, type_ascription_suffix]);

        let body = match def {
            DeclDef::Imported(import) => {
                Some(pretty::Fragment::new(["= ".into(), import.print(printer)]))
            }
            DeclDef::Present(GlobalVarDefBody { initializer }) => {
                initializer.map(|initializer| {
                    // FIXME(eddyb) find a better syntax for this.
                    pretty::Fragment::new(["init=".into(), initializer.print(printer)])
                })
            }
        };

        let def = pretty::Fragment::new([header, pretty::join_space("", body)]);

        AttrsAndDef {
            attrs: attrs.print(printer),
            def,
        }
    }
}

impl Print for FuncDecl {
    type Output = AttrsAndDef;
    fn print(&self, printer: &Printer<'_, '_>) -> AttrsAndDef {
        let Self {
            attrs,
            ret_type,
            params,
            def,
        } = self;

        let sig = pretty::Fragment::new([
            pretty::join_comma_sep(
                "(",
                params.iter().enumerate().map(|(i, param)| {
                    let AttrsAndDef { attrs, def } = param.print(printer);
                    pretty::Fragment::new([
                        attrs,
                        Value::FuncParam {
                            idx: i.try_into().unwrap(),
                        }
                        .print(printer),
                        def.into(),
                    ])
                }),
                ")",
            ),
            " -> ".into(),
            ret_type.print(printer),
        ]);

        let def = match def {
            DeclDef::Imported(import) => {
                pretty::Fragment::new([sig, " = ".into(), import.print(printer).into()])
            }
            DeclDef::Present(
                def @ FuncDefBody {
                    data_insts: _,
                    control_nodes,
                    body: _,
                    cfg,
                },
            ) => pretty::Fragment::new([
                sig,
                " {".into(),
                pretty::Node::IndentedBlock(
                    cfg.rev_post_order(def)
                        .filter(|point| {
                            // HACK(eddyb) this needs to print `UnstructuredMerge`s on `Exit`
                            // instead of `Entry`, because they don't have have `Entry`s.
                            match control_nodes[point.control_node()].kind {
                                ControlNodeKind::UnstructuredMerge => {
                                    assert!(matches!(point, cfg::ControlPoint::Exit(_)));
                                    true
                                }
                                _ => matches!(point, cfg::ControlPoint::Entry(_)),
                            }
                        })
                        .map(|point| {
                            let label = Use::ControlPointLabel(point);
                            let label_header = if printer.use_styles.contains_key(&label) {
                                // FIXME(eddyb) `:` as used here for C-like "label syntax"
                                // interferes (in theory) with `e: T` "type ascription syntax".
                                Some(pretty::Fragment::new([
                                    label.print_as_def(printer),
                                    ":".into(),
                                ]))
                            } else {
                                None
                            };
                            let (entry_label_header, exit_label_header) = match point {
                                cfg::ControlPoint::Entry(_) => (label_header, None),
                                cfg::ControlPoint::Exit(_) => (None, label_header),
                            };

                            let control_node = point.control_node();
                            let control_node_body = def.at(control_node).print(printer);

                            pretty::Fragment::new(
                                [
                                    entry_label_header,
                                    Some(
                                        pretty::Node::IndentedBlock(vec![control_node_body.into()])
                                            .into(),
                                    ),
                                    exit_label_header,
                                    if let Some(control_inst) =
                                        cfg.control_insts.get(cfg::ControlPoint::Exit(control_node))
                                    {
                                        Some(control_inst.print(printer))
                                    } else {
                                        None
                                    },
                                ]
                                .into_iter()
                                .flatten()
                                .flat_map(|fragment| {
                                    [
                                        pretty::Node::ForceLineSeparation.into(),
                                        fragment,
                                        pretty::Node::ForceLineSeparation.into(),
                                    ]
                                }),
                            )
                        })
                        .intersperse({
                            // Separate (top-level) control nodes with empty lines.
                            // FIXME(eddyb) have an explicit `pretty::Node`
                            // for "vertical gap" instead.
                            "\n\n".into()
                        })
                        .collect(),
                )
                .into(),
                "}".into(),
            ]),
        };

        AttrsAndDef {
            attrs: attrs.print(printer),
            def,
        }
    }
}

impl Print for FuncParam {
    type Output = AttrsAndDef;
    fn print(&self, printer: &Printer<'_, '_>) -> AttrsAndDef {
        let Self { attrs, ty } = *self;

        AttrsAndDef {
            attrs: attrs.print(printer),
            def: printer.pretty_type_ascription_suffix(ty),
        }
    }
}

impl Print for FuncAt<'_, ControlNode> {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_, '_>) -> pretty::Fragment {
        let control_node = self.position;
        let ControlNodeDef { kind, outputs } = self.def();

        let outputs_header = if !outputs.is_empty() {
            let mut outputs = outputs.iter().enumerate().map(|(output_idx, output)| {
                let AttrsAndDef { attrs, def } = output.print(printer);
                pretty::Fragment::new([
                    attrs,
                    Value::ControlNodeOutput {
                        control_node,
                        output_idx: output_idx.try_into().unwrap(),
                    }
                    .print_as_def(printer),
                    def.into(),
                ])
            });
            let outputs_lhs = if outputs.len() == 1 {
                outputs.next().unwrap()
            } else {
                pretty::join_comma_sep("(", outputs, ")")
            };
            pretty::Fragment::new([outputs_lhs, " = ".into()])
        } else {
            pretty::Fragment::default()
        };

        let control_node_body = match *kind {
            ControlNodeKind::UnstructuredMerge => printer
                .comment_style()
                .apply("/* unstructured merge */")
                .into(),
            ControlNodeKind::Block { insts } => {
                assert!(outputs.is_empty());

                pretty::Fragment::new(
                    self.at(insts)
                        .into_iter()
                        .map(|func_at_inst| {
                            let data_inst_def = func_at_inst.def();
                            let AttrsAndDef { attrs, mut def } = data_inst_def.print(printer);

                            if data_inst_def.output_type.is_some() {
                                let header = pretty::Fragment::new([
                                    Use::DataInstOutput(func_at_inst.position)
                                        .print_as_def(printer),
                                    " =".into(),
                                ]);
                                // FIXME(eddyb) the reindenting here hurts more than
                                // it helps, maybe it needs some heuristics?
                                def = pretty::Fragment::new([
                                    header,
                                    if false {
                                        pretty::join_space("", [def])
                                    } else {
                                        pretty::Fragment::new([" ".into(), def])
                                    },
                                ]);
                            }

                            pretty::Fragment::new([attrs, def.into()])
                        })
                        .flat_map(|entry| [pretty::Node::ForceLineSeparation.into(), entry]),
                )
            }
        };
        pretty::Fragment::new([outputs_header, control_node_body])
    }
}

impl Print for ControlNodeOutputDecl {
    type Output = AttrsAndDef;
    fn print(&self, printer: &Printer<'_, '_>) -> AttrsAndDef {
        let Self { attrs, ty } = *self;

        AttrsAndDef {
            attrs: attrs.print(printer),
            def: printer.pretty_type_ascription_suffix(ty),
        }
    }
}

impl Print for DataInstDef {
    type Output = AttrsAndDef;
    fn print(&self, printer: &Printer<'_, '_>) -> AttrsAndDef {
        let Self {
            attrs,
            kind,
            output_type,
            inputs,
        } = self;

        let attrs = attrs.print(printer);

        let header = match *kind {
            DataInstKind::FuncCall(func) => pretty::Fragment::new([
                printer.declarative_keyword_style().apply("call").into(),
                " ".into(),
                func.print(printer),
            ]),
            DataInstKind::SpvInst(spv::Inst { opcode, ref imms }) => {
                return AttrsAndDef {
                    attrs,
                    def: printer.pretty_spv_inst(
                        printer.declarative_keyword_style(),
                        opcode,
                        imms,
                        inputs,
                        Print::print,
                        *output_type,
                    ),
                };
            }
            DataInstKind::SpvExtInst { ext_set, inst } => {
                // FIXME(eddyb) should this be rendered more compactly?
                pretty::Fragment::new([
                    "(".into(),
                    printer.declarative_keyword_style().apply("OpExtInstImport"),
                    "<".into(),
                    printer
                        .string_literal_style()
                        .apply(format!("{:?}", &printer.cx[ext_set])),
                    ">).".into(),
                    printer.declarative_keyword_style().apply("OpExtInst"),
                    "<".into(),
                    printer.numeric_literal_style().apply(format!("{}", inst)),
                    ">".into(),
                ])
            }
        };

        // FIXME(eddyb) deduplicate the "parens + optional type ascription"
        // logic with `pretty_spv_inst`.
        let def = pretty::Fragment::new([
            header,
            pretty::join_comma_sep("(", inputs.iter().map(|v| v.print(printer)), ")"),
            output_type
                .map(|ty| printer.pretty_type_ascription_suffix(ty))
                .unwrap_or_default(),
        ]);

        AttrsAndDef { attrs, def }
    }
}

impl Print for cfg::ControlInst {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_, '_>) -> pretty::Fragment {
        let Self {
            attrs,
            kind,
            inputs,
            targets,
            target_merge_outputs,
        } = self;

        let attrs = attrs.print(printer);

        let mut targets = targets.iter().map(|&point| {
            let mut target =
                pretty::Fragment::new(["=> ".into(), Use::ControlPointLabel(point).print(printer)]);
            if let cfg::ControlPoint::Exit(control_node) = point {
                if let Some(outputs) = target_merge_outputs.get(&control_node) {
                    target = pretty::Fragment::new([
                        target,
                        pretty::join_comma_sep(
                            "(",
                            outputs.iter().enumerate().map(|(output_idx, v)| {
                                pretty::Fragment::new([
                                    Value::ControlNodeOutput {
                                        control_node: control_node,
                                        output_idx: output_idx.try_into().unwrap(),
                                    }
                                    .print(printer),
                                    " <- ".into(),
                                    v.print(printer),
                                ])
                            }),
                            ")",
                        ),
                    ]);
                }
            }
            target
        });

        let kw_style = printer.imperative_keyword_style();
        let kw = |kw| kw_style.clone().apply(kw).into();
        let def = match *kind {
            cfg::ControlInstKind::Unreachable => {
                // FIXME(eddyb) use `targets.is_empty()` when that is stabilized.
                assert!(targets.len() == 0 && inputs.is_empty());
                kw("unreachable")
            }
            cfg::ControlInstKind::Return => {
                // FIXME(eddyb) use `targets.is_empty()` when that is stabilized.
                assert!(targets.len() == 0);
                match inputs[..] {
                    [] => kw("return"),
                    [v] => pretty::Fragment::new([kw("return"), " ".into(), v.print(printer)]),
                    _ => unreachable!(),
                }
            }
            cfg::ControlInstKind::ExitInvocation(cfg::ExitInvocationKind::SpvInst(spv::Inst {
                opcode,
                ref imms,
            })) => {
                // FIXME(eddyb) use `targets.is_empty()` when that is stabilized.
                assert!(targets.len() == 0);
                printer.pretty_spv_inst(kw_style, opcode, imms, inputs, Print::print, None)
            }

            cfg::ControlInstKind::Branch => {
                assert_eq!((targets.len(), inputs.len()), (1, 0));
                pretty::Fragment::new([kw("branch"), " ".into(), targets.nth(0).unwrap()])
            }

            cfg::ControlInstKind::SelectBranch(cfg::SelectionKind::BoolCond) => {
                assert_eq!((targets.len(), inputs.len()), (2, 1));
                let [target_then, target_else] = {
                    // HACK(eddyb) work around the lack of `Into<[T; N]>` on `SmallVec`.
                    let mut it = targets.into_iter();
                    [it.next().unwrap(), it.next().unwrap()]
                };
                pretty::Fragment::new([
                    kw("if"),
                    " ".into(),
                    inputs[0].print(printer),
                    " {".into(),
                    pretty::Node::IndentedBlock(vec![target_then]).into(),
                    "} ".into(),
                    kw("else"),
                    " {".into(),
                    pretty::Node::IndentedBlock(vec![target_else]).into(),
                    "}".into(),
                ])
            }
            cfg::ControlInstKind::SelectBranch(cfg::SelectionKind::SpvInst(spv::Inst {
                opcode,
                ref imms,
            })) => {
                #[derive(Copy, Clone)]
                struct TargetLabelId;

                let header = printer.pretty_spv_inst(
                    kw_style,
                    opcode,
                    imms,
                    inputs
                        .iter()
                        .map(Ok)
                        .chain((0..targets.len()).map(|_| Err(TargetLabelId))),
                    |id, printer| match id {
                        Ok(v) => Some(v.print(printer)),
                        Err(TargetLabelId) => None,
                    },
                    None,
                );

                pretty::Fragment::new([
                    header,
                    match targets.len() {
                        0 => pretty::Fragment::default(),
                        1 => pretty::Fragment::new([" ".into(), targets.nth(0).unwrap()]),
                        _ => pretty::join_comma_sep(
                            " {",
                            targets.map(|target| {
                                pretty::Fragment::new([
                                    pretty::Node::ForceLineSeparation.into(),
                                    target,
                                ])
                            }),
                            "}",
                        ),
                    },
                ])
            }
        };

        pretty::Fragment::new([attrs, def])
    }
}

impl Value {
    /// Common implementation for `Value::print` and `Value::print_as_def`.
    fn print_as_ref_or_def(&self, printer: &Printer<'_, '_>, is_def: bool) -> pretty::Fragment {
        let value_use = match *self {
            Self::Const(ct) => Use::Interned(InternedNode::Const(ct)),
            Self::FuncParam { idx } => return format!("param{}", idx).into(),
            Self::ControlNodeOutput {
                control_node,
                output_idx,
            } => Use::ControlNodeOutput {
                control_node,
                output_idx,
            },
            Self::DataInstOutput(inst) => Use::DataInstOutput(inst),
        };
        if is_def {
            value_use.print_as_def(printer)
        } else {
            value_use.print(printer)
        }
    }

    fn print_as_def(&self, printer: &Printer<'_, '_>) -> pretty::Fragment {
        self.print_as_ref_or_def(printer, true)
    }
}

impl Print for Value {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_, '_>) -> pretty::Fragment {
        self.print_as_ref_or_def(printer, false)
    }
}
