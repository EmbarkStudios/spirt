use crate::visit::{DynInnerVisit, InnerVisit, Visitor};
use crate::{
    cfg, spv, AddrSpace, Attr, AttrSet, AttrSetDef, Const, ConstCtor, ConstDef, Context,
    ControlNode, ControlNodeDef, ControlNodeKind, ControlNodeOutputDecl, DataInst, DataInstDef,
    DataInstKind, DeclDef, ExportKey, Exportee, Func, FuncDecl, FuncDefBody, FuncParam, FxIndexMap,
    GlobalVar, GlobalVarDecl, GlobalVarDefBody, Import, Module, ModuleDebugInfo, ModuleDialect,
    Type, TypeCtor, TypeCtorArg, TypeDef, Value,
};
use format::lazy_format;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use std::{fmt, iter};

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

trait DynNode<'a>: DynInnerVisit<'a, Plan<'a>> + Print<Output = String> {}
impl<'a, T: DynInnerVisit<'a, Plan<'a>> + Print<Output = String>> DynNode<'a> for T {}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
enum Use {
    Interned(InternedNode),

    GlobalVar(GlobalVar),
    Func(Func),

    ControlNode(ControlNode),
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
            // FIXME(eddyb) maybe generate C-style labels for non-structured CFGs?
            Self::ControlNode(_) => "ctl",
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
        root: &'a (impl DynInnerVisit<'a, Plan<'a>> + Print<Output = String>),
    ) -> Self {
        let mut plan = Self::empty(module);
        plan.use_node(Node::Dyn(root));
        plan
    }

    /// Like `for_root`, but without supporting anything module-stored (like global vars).
    pub fn for_root_outside_module(
        cx: &'a Context,
        root: &'a (impl DynInnerVisit<'a, Plan<'a>> + Print<Output = String>),
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

impl fmt::Display for Plan<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let printer = Printer::new(self);
        let mut ended_with_empty_line = false;
        for &node in &self.nodes {
            let AttrsAndDef { attrs, def } = node.print(&printer);

            // Visually isolate definitions with attributes.
            let empty_lines_before_and_after = !attrs.is_empty();
            if empty_lines_before_and_after && !ended_with_empty_line {
                writeln!(f)?;
            }

            let def = attrs + &def;
            if !def.is_empty() {
                writeln!(f, "{}", def)?;

                ended_with_empty_line = if empty_lines_before_and_after {
                    writeln!(f)?;
                    true
                } else {
                    false
                };
            }
        }
        Ok(())
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
    Anon { idx: usize },

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
                if let Use::ControlNode(_)
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
                    Use::ControlNode(_)
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
                        Use::ControlNode(_)
                        | Use::ControlNodeOutput { .. }
                        | Use::DataInstOutput(_) => {
                            unreachable!()
                        }
                    };
                    let idx = *counter;
                    *counter += 1;
                    UseStyle::Anon { idx }
                };
                (use_kind, style)
            })
            .collect();

        for (&_func, &func_decl) in &plan.func_decl_cache {
            if let DeclDef::Present(func_def_body) = &func_decl.def {
                let mut control_node_counter = 0;
                let mut value_counter = 0;

                for point in func_def_body.cfg.rev_post_order(func_def_body) {
                    let control_node = point.control_node();
                    let ControlNodeDef { kind, outputs } =
                        &*func_def_body.control_nodes[control_node];

                    // Only handle each `ControlNode` once.
                    if let cfg::ControlPoint::Exit(_) = point {
                        match kind {
                            // `ControlNodeKind::UnstructuredMerge` only has an `Exit`
                            // (see also `cfg::ControlPoint`'s doc comment).
                            ControlNodeKind::UnstructuredMerge => {}

                            _ => continue,
                        }
                    }

                    {
                        let idx = control_node_counter;
                        control_node_counter += 1;
                        use_styles.insert(Use::ControlNode(control_node), UseStyle::Anon { idx });
                    }

                    let block_insts = match kind {
                        ControlNodeKind::UnstructuredMerge => &[][..],
                        ControlNodeKind::Block { insts } => insts,
                    };

                    let defined_values =
                        block_insts
                            .iter()
                            .copied()
                            .filter(|&inst| func_def_body.data_insts[inst].output_type.is_some())
                            .map(Use::DataInstOutput)
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
                            *use_style = UseStyle::Anon { idx };
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

    /// Returns a concatenation of `pieces` using `.for_single_line()` if the
    /// resulting string can fit on one line, or a multi-line indented version
    /// otherwise (`.for_multi_line()` with reindented `Content` pieces).
    fn pretty_concat_pieces<'c>(
        &self,
        pieces: impl IntoIterator<Item = PrettyPiece<'c>>,
    ) -> String {
        let mut pieces: SmallVec<[_; 16]> = pieces.into_iter().collect();

        // FIXME(eddyb) make max line width configurable.
        let max_line_len = 80;
        let fits_on_single_line = pieces
            .iter()
            .map(|piece| piece.for_single_line())
            .try_fold(0usize, |single_line_len, piece| {
                if piece.contains("\n") {
                    return None;
                }
                single_line_len
                    .checked_add(piece.len())
                    .filter(|&len| len <= max_line_len)
            })
            .is_some();

        if !fits_on_single_line {
            // FIXME(eddyb) automate reindenting (and make it configurable).
            for piece in &mut pieces {
                if let PrettyPiece::Content(content) = piece {
                    *content = content.replace("\n", "\n  ");
                }
            }
        }

        let pieces = pieces.iter().map(|piece| {
            if fits_on_single_line {
                piece.for_single_line()
            } else {
                piece.for_multi_line()
            }
        });
        let mut combined = String::with_capacity(pieces.clone().map(|s| s.len()).sum());
        combined.extend(pieces);
        combined
    }

    /// Returns `header + " " + contents.join(" ")` if the resulting string can
    /// fit on one line, or a multi-line indented version otherwise.
    fn pretty_join_space(
        &self,
        header: &str,
        contents: impl IntoIterator<Item = String>,
    ) -> String {
        self.pretty_concat_pieces(
            iter::once(PrettyPiece::Joiner {
                single_line: header,
                multi_line: header,
            })
            .chain(contents.into_iter().flat_map(|entry| {
                [
                    PrettyPiece::Joiner {
                        single_line: " ",
                        multi_line: "\n  ",
                    },
                    PrettyPiece::Content(entry),
                ]
            })),
        )
    }

    /// Returns `prefix + contents.join(comma + " ") + suffix` if the resulting
    /// string can fit on one line, or a multi-line indented version otherwise.
    fn pretty_join_comma_sep(
        &self,
        prefix: &str,
        contents: impl IntoIterator<Item = String>,
        comma: &str,
        suffix: &str,
    ) -> String {
        // FIXME(eddyb) this is probably more complicated than it needs to be.
        self.pretty_concat_pieces(
            [
                PrettyPiece::Joiner {
                    single_line: prefix,
                    multi_line: prefix,
                },
                PrettyPiece::Joiner {
                    single_line: "",
                    multi_line: "\n  ",
                },
            ]
            .into_iter()
            .chain(contents.into_iter().enumerate().flat_map(|(i, entry)| {
                // FIXME(eddyb) use `Iterator::intersperse` when that's stable.
                let sep = if i == 0 {
                    None
                } else {
                    Some([
                        PrettyPiece::Joiner {
                            single_line: comma,
                            multi_line: comma,
                        },
                        PrettyPiece::Joiner {
                            single_line: " ",
                            multi_line: "\n  ",
                        },
                    ])
                };
                sep.into_iter()
                    .flatten()
                    .chain([PrettyPiece::Content(entry)])
            }))
            .chain([
                PrettyPiece::Joiner {
                    single_line: "",
                    multi_line: comma,
                },
                PrettyPiece::Joiner {
                    single_line: "",
                    multi_line: "\n",
                },
                PrettyPiece::Joiner {
                    single_line: suffix,
                    multi_line: suffix,
                },
            ]),
        )
    }

    /// Pretty-print a `: T` style "type ascription" suffix.
    ///
    /// This should be used everywhere some type ascription notation is needed,
    /// to ensure consistency across all such situations.
    fn pretty_type_ascription_suffix(&self, ty: Type) -> String {
        self.pretty_join_space(":", [ty.print(self)])
    }

    /// Pretty-print an arbitrary SPIR-V `opcode` with `imms` and `ids` as its
    /// SPIR-V operands (with each `ID` in `ids` passed through `print_id`),
    /// and optionally with a ` : ...` type ascription at the end (`result_type`).
    ///
    /// `print_id` can return `None` to indicate an ID operand is implicit in
    /// SPIR-T, and should not be printed (e.g. decorations' target IDs).
    /// But if `print_id` doesn't need to return `Option<String>` (for `None`),
    /// its return type can also be `String` (which allows passing in the
    /// `Print::print` method, instead of a closure, as `print_id`).
    ///
    /// Immediate operands are wrapped in angle brackets, while `ID` operands are
    /// wrapped in parentheses, e.g.: `OpFoo<Bar, 123, "baz">(v1, v2)`.
    ///
    /// This should be used everywhere a SPIR-V instruction needs to be printed,
    /// to ensure consistency across all such situations.
    fn pretty_spv_inst<ID: Copy, OS: Into<Option<String>>>(
        &self,
        opcode: spv::spec::Opcode,
        imms: &[spv::Imm],
        ids: impl IntoIterator<Item = ID>,
        print_id: impl Fn(ID, &Self) -> OS,
        result_type: Option<Type>,
    ) -> String {
        // Split operands into "angle brackets" (immediates) and "parens" (IDs),
        // with compound operands (i.e. enumerand with ID parameter) using both,
        // e.g: `OpFoo<Bar(/* #0 */)>(/* #0 */ v123)`.
        let mut next_extra_idx: usize = 0;
        let mut paren_operands = SmallVec::<[String; 16]>::new();
        let mut angle_bracket_operands =
            spv::print::inst_operands(opcode, imms.iter().copied(), ids)
                .filter_map(|operand| {
                    if let [spv::print::PrintOutPart::Id(id)] = operand.parts[..] {
                        paren_operands.extend(print_id(id, self).into());
                        None
                    } else {
                        Some(
                            operand
                                .parts
                                .into_iter()
                                .map(|part| match part {
                                    spv::print::PrintOutPart::Printed(s) => s,
                                    spv::print::PrintOutPart::Id(id) => {
                                        let comment = format!("/* #{} */", next_extra_idx);
                                        next_extra_idx += 1;

                                        let id = print_id(id, self)
                                            .into()
                                            .unwrap_or_else(|| "/* implicit ID */".to_string());
                                        paren_operands.push(format!("{} {}", comment, id));

                                        comment
                                    }
                                })
                                .reduce(|out, extra| out + &extra)
                                .unwrap_or_default(),
                        )
                    }
                })
                .peekable();

        // Put together all the pieces, angle-bracketed operands then parenthesized
        // ones, e.g.: `OpFoo<Bar, 123, "baz">(v1, v2)` (with either group optional).
        let mut out = opcode.name().to_string();

        if angle_bracket_operands.peek().is_some() {
            out = self.pretty_join_comma_sep(&(out + "<"), angle_bracket_operands, ",", ">");
        }

        let type_ascription_suffix = result_type.map(|ty| self.pretty_type_ascription_suffix(ty));

        if !paren_operands.is_empty() {
            out = self.pretty_join_comma_sep(
                &(out + "("),
                paren_operands,
                ",",
                type_ascription_suffix
                    .map(|s| format!("){}", s))
                    .as_deref()
                    .unwrap_or(")"),
            );
        } else {
            if let Some(type_ascription_suffix) = type_ascription_suffix {
                out = out + &type_ascription_suffix;
            }
        }

        out
    }
}

/// Helper type for for `pretty_concat_pieces`.
enum PrettyPiece<'a> {
    Content(String),
    Joiner {
        single_line: &'a str,
        multi_line: &'a str,
    },
}

impl PrettyPiece<'_> {
    fn for_single_line(&self) -> &str {
        match self {
            Self::Content(s) => s,
            Self::Joiner { single_line, .. } => single_line,
        }
    }
    fn for_multi_line(&self) -> &str {
        match self {
            Self::Content(s) => s,
            Self::Joiner { multi_line, .. } => multi_line,
        }
    }
}

pub trait Print {
    type Output;
    fn print(&self, printer: &Printer<'_, '_>) -> Self::Output;
}

impl<E: Print<Output = String>, F: Print<Output = String>> Print for ExpectedVsFound<E, F> {
    type Output = String;
    fn print(&self, printer: &Printer<'_, '_>) -> String {
        let Self { expected, found } = self;

        format!(
            "expected: {}\nfound: {}",
            expected.print(printer),
            found.print(printer)
        )
    }
}

/// A `Print` `Output` type that splits the attributes from the main body of the
/// definition, allowing additional processing before they get concatenated.
#[derive(Default)]
pub struct AttrsAndDef {
    pub attrs: String,
    pub def: String,
}

impl Print for Use {
    type Output = String;
    fn print(&self, printer: &Printer<'_, '_>) -> String {
        let style = printer
            .use_styles
            .get(self)
            .copied()
            .unwrap_or(UseStyle::Inline);
        let mut s = match style {
            UseStyle::Anon { idx } => {
                let prefix = match self {
                    Self::Interned(InternedNode::AttrSet(_)) => "#",
                    _ => "",
                };
                format!("{}{}{}", prefix, self.category(), idx)
            }
            UseStyle::Inline => match *self {
                Self::Interned(node) => {
                    let AttrsAndDef {
                        attrs: attrs_of_def,
                        def,
                    } = node.print(printer);
                    match node {
                        InternedNode::AttrSet(_) => def,
                        InternedNode::Type(_) | InternedNode::Const(_) => {
                            if attrs_of_def.is_empty() {
                                def
                            } else {
                                attrs_of_def + &def
                            }
                        }
                    }
                }
                Self::GlobalVar(_) => format!("/* unused global_var */_"),
                Self::Func(_) => format!("/* unused func */_"),
                Self::ControlNode(_) | Self::ControlNodeOutput { .. } | Self::DataInstOutput(_) => {
                    "_".to_string()
                }
            },
        };

        // Separate non-empty attributes from their targets.
        if let Self::Interned(InternedNode::AttrSet(_)) = self {
            if !s.is_empty() {
                s += "\n";
            }
        }

        s
    }
}

// Interned/module-stored nodes dispatch through the `Use` impl above.
impl Print for AttrSet {
    type Output = String;
    fn print(&self, printer: &Printer<'_, '_>) -> String {
        Use::Interned(InternedNode::AttrSet(*self)).print(printer)
    }
}
impl Print for Type {
    type Output = String;
    fn print(&self, printer: &Printer<'_, '_>) -> String {
        Use::Interned(InternedNode::Type(*self)).print(printer)
    }
}
impl Print for Const {
    type Output = String;
    fn print(&self, printer: &Printer<'_, '_>) -> String {
        Use::Interned(InternedNode::Const(*self)).print(printer)
    }
}
impl Print for GlobalVar {
    type Output = String;
    fn print(&self, printer: &Printer<'_, '_>) -> String {
        Use::GlobalVar(*self).print(printer)
    }
}
impl Print for Func {
    type Output = String;
    fn print(&self, printer: &Printer<'_, '_>) -> String {
        Use::Func(*self).print(printer)
    }
}

// NOTE(eddyb) the `Print` impl for `Node` is for the top-level definition,
// *not* any uses (which go through the `Print` impls above).
impl Print for Node<'_> {
    type Output = AttrsAndDef;
    fn print(&self, printer: &Printer<'_, '_>) -> AttrsAndDef {
        match *self {
            Self::Interned(node) => match printer.use_styles.get(&Use::Interned(node)).copied() {
                Some(UseStyle::Anon { idx }) => {
                    let AttrsAndDef {
                        attrs: attrs_of_def,
                        def,
                    } = node.print(printer);

                    AttrsAndDef {
                        attrs: attrs_of_def,
                        def: format!("{}{} = {}", node.category(), idx, def),
                    }
                }
                _ => AttrsAndDef::default(),
            },

            Self::GlobalVar(gv) => match printer.global_var_decl_cache.get(&gv) {
                Some(gv_decl) => {
                    let AttrsAndDef { attrs, def } = gv_decl.print(printer);
                    AttrsAndDef {
                        attrs,
                        def: gv.print(printer) + &def,
                    }
                }
                None => AttrsAndDef::default(),
            },

            Self::Func(func) => match printer.func_decl_cache.get(&func) {
                Some(func_decl) => {
                    let AttrsAndDef { attrs, def } = func_decl.print(printer);
                    AttrsAndDef {
                        attrs,
                        def: func.print(printer) + &def,
                    }
                }
                None => AttrsAndDef::default(),
            },

            Self::Dyn(node) => AttrsAndDef {
                attrs: String::new(),
                def: node.print(printer),
            },
        }
    }
}

impl Print for Module {
    type Output = String;
    fn print(&self, printer: &Printer<'_, '_>) -> String {
        lazy_format!(|f| {
            if self.exports.is_empty() {
                return Ok(());
            }
            writeln!(f, "export {{")?;
            for (export_key, exportee) in &self.exports {
                writeln!(
                    f,
                    "  {}: {},",
                    export_key.print(printer).replace("\n", "\n  "),
                    exportee.print(printer)
                )?;
            }
            write!(f, "}}")
        })
        .to_string()
    }
}

impl Print for ModuleDialect {
    type Output = String;
    fn print(&self, _printer: &Printer<'_, '_>) -> String {
        lazy_format!(|f| {
            write!(f, "module.dialect = ")?;
            match self {
                Self::Spv(spv::Dialect {
                    version_major,
                    version_minor,
                    capabilities,
                    extensions,
                    addressing_model,
                    memory_model,
                }) => {
                    let wk = &spv::spec::Spec::get().well_known;

                    writeln!(f, "SPIR-V {{")?;
                    writeln!(f, "  version: {}.{},", version_major, version_minor)?;
                    writeln!(f, "  extensions: {:?},", extensions)?;

                    write!(f, "  capabilities: ")?;
                    f.debug_set()
                        .entries(capabilities.iter().map(|&cap| {
                            format::Debug(move |f| {
                                write!(f, "{}", spv::print::imm(wk.Capability, cap))
                            })
                        }))
                        .finish()?;
                    writeln!(f, ",")?;

                    writeln!(
                        f,
                        "  addressing_model: {},",
                        spv::print::imm(wk.AddressingModel, *addressing_model)
                    )?;
                    writeln!(
                        f,
                        "  memory_model: {},",
                        spv::print::imm(wk.MemoryModel, *memory_model)
                    )?;
                    write!(f, "}}")
                }
            }
        })
        .to_string()
    }
}

impl Print for ModuleDebugInfo {
    type Output = String;
    fn print(&self, printer: &Printer<'_, '_>) -> String {
        lazy_format!(|f| {
            write!(f, "module.debug_info = ")?;
            match self {
                Self::Spv(spv::ModuleDebugInfo {
                    original_generator_magic,
                    source_languages,
                    source_extensions,
                    module_processes,
                }) => {
                    let wk = &spv::spec::Spec::get().well_known;

                    writeln!(f, "SPIR-V {{")?;

                    if let Some(generator_magic) = original_generator_magic {
                        let (tool_id, tool_version) =
                            (generator_magic.get() >> 16, generator_magic.get() as u16);
                        writeln!(
                            f,
                            "  generator: {{ tool_id: {}, version: {} }},",
                            tool_id, tool_version
                        )?;
                    }

                    write!(f, "  source_languages: {{")?;
                    if !source_languages.is_empty() {
                        writeln!(f)?;
                        for (lang, sources) in source_languages {
                            let spv::DebugSources { file_contents } = sources;
                            write!(
                                f,
                                "    {} {{ version: {} }}: {{",
                                spv::print::imm(wk.SourceLanguage, lang.lang),
                                lang.version
                            )?;
                            if !file_contents.is_empty() {
                                writeln!(f)?;
                                for (&file, contents) in file_contents {
                                    writeln!(f, "      {:?}: {:?},", &printer.cx[file], contents)?;
                                }
                                write!(f, "    ")?;
                            }
                            writeln!(f, "}},")?;
                        }
                        write!(f, "  ")?;
                    }
                    writeln!(f, "}},")?;

                    writeln!(f, "  source_extensions: {:?},", source_extensions)?;
                    writeln!(f, "  module_processes: {:?},", module_processes)?;
                    write!(f, "}}")
                }
            }
        })
        .to_string()
    }
}

impl Print for ExportKey {
    type Output = String;
    fn print(&self, printer: &Printer<'_, '_>) -> String {
        match self {
            &Self::LinkName(name) => format!("{:?}", &printer.cx[name]),

            // HACK(eddyb) `interface_global_vars` should be recomputed by
            // `spv::lift` anyway, so hiding them here mimics that.
            Self::SpvEntryPoint {
                imms,
                interface_global_vars: _,
            } => {
                let wk = &spv::spec::Spec::get().well_known;

                struct ImplicitTargetId;

                printer.pretty_spv_inst(
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
    type Output = String;
    fn print(&self, printer: &Printer<'_, '_>) -> String {
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
                attrs: String::new(),
                def: printer.cx[attrs].print(printer),
            },
            Self::Type(ty) => printer.cx[ty].print(printer),
            Self::Const(ct) => printer.cx[ct].print(printer),
        }
    }
}

impl Print for AttrSetDef {
    type Output = String;
    fn print(&self, printer: &Printer<'_, '_>) -> String {
        let Self { attrs } = self;

        let mut comments = SmallVec::<[_; 1]>::new();
        let mut non_comment_attrs = SmallVec::<[_; 4]>::new();
        for attr in attrs {
            let attr = attr.print(printer);
            if attr.starts_with("//") {
                comments.push(attr);
            } else {
                non_comment_attrs.push(attr);
            }
        }

        let non_comment_attrs = match &non_comment_attrs[..] {
            [] => String::new(),
            // FIXME(eddyb) this could use `pretty_join_comma_sep`, except that
            // will gladly put multiple attributes on the same line.
            [attr] if !attr.contains("\n") => format!("#{{{}}}", attr),
            _ => lazy_format!(|f| {
                writeln!(f, "#{{")?;
                for attr in &non_comment_attrs {
                    writeln!(f, "  {},", attr.replace("\n", "\n  "))?;
                }
                write!(f, "}}")
            })
            .to_string(),
        };

        let comments = comments.join("\n");

        if !non_comment_attrs.is_empty() && !comments.is_empty() {
            [non_comment_attrs, comments].join("\n")
        } else {
            non_comment_attrs + &comments
        }
    }
}

impl Print for Attr {
    type Output = String;
    fn print(&self, printer: &Printer<'_, '_>) -> String {
        match self {
            Attr::SpvAnnotation(spv::Inst { opcode, imms }) => {
                struct ImplicitTargetId;

                printer.pretty_spv_inst(
                    *opcode,
                    imms,
                    &[ImplicitTargetId],
                    |ImplicitTargetId, _| None,
                    None,
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
                if file_path.chars().all(|c| c.is_ascii_graphic() && c != ':') {
                    format!("// at {}:{}:{}", file_path, line, col)
                } else {
                    format!("// at {:?}:{}:{}", file_path, line, col)
                }
            }
            &Attr::SpvBitflagsOperand(imm) => spv::print::operand_from_imms([imm]),
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
        #[allow(irrefutable_let_patterns)]
        let compact_def = if let &TypeCtor::SpvInst(spv::Inst { opcode, ref imms }) = ctor {
            if opcode == wk.OpTypeBool {
                Some("bool".to_string())
            } else if opcode == wk.OpTypeInt {
                let (width, signed) = match imms[..] {
                    [spv::Imm::Short(_, width), spv::Imm::Short(_, signedness)] => {
                        (width, signedness != 0)
                    }
                    _ => unreachable!(),
                };

                Some(if signed {
                    format!("s{}", width)
                } else {
                    format!("u{}", width)
                })
            } else if opcode == wk.OpTypeFloat {
                let width = match imms[..] {
                    [spv::Imm::Short(_, width)] => width,
                    _ => unreachable!(),
                };

                Some(format!("f{}", width))
            } else if opcode == wk.OpTypeVector {
                let (elem_ty, elem_count) = match (&imms[..], &ctor_args[..]) {
                    (&[spv::Imm::Short(_, elem_count)], &[TypeCtorArg::Type(elem_ty)]) => {
                        (elem_ty, elem_count)
                    }
                    _ => unreachable!(),
                };

                Some(format!("{}x{}", elem_ty.print(printer), elem_count))
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

        let compact_def = if let &ConstCtor::SpvInst(spv::Inst { opcode, ref imms }) = ctor {
            if opcode == wk.OpConstantFalse {
                Some("false".to_string())
            } else if opcode == wk.OpConstantTrue {
                Some("true".to_string())
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
                            Some(if signed {
                                let sext_raw_bits =
                                    (raw_bits as u128 as i128) << (128 - width) >> (128 - width);
                                format!("{}s{}", sext_raw_bits, width)
                            } else {
                                format!("{}u{}", raw_bits, width)
                            })
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
                        printed_value.map(|s| format!("{}f{}", s, width))
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
                def
            } else {
                match *ctor {
                    ConstCtor::PtrToGlobalVar(gv) => format!("&{}", gv.print(printer)),
                    ConstCtor::SpvInst(spv::Inst { opcode, ref imms }) => {
                        printer.pretty_spv_inst(opcode, imms, ctor_args, Print::print, Some(*ty))
                    }
                }
            },
        }
    }
}

impl Print for Import {
    type Output = String;
    fn print(&self, printer: &Printer<'_, '_>) -> String {
        match self {
            &Self::LinkName(name) => format!("import {:?}", &printer.cx[name]),
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
                _ => format!(": pointee_type_of({})", type_of_ptr_to.print(printer)),
            }
        };
        let addr_space = match *addr_space {
            AddrSpace::SpvStorageClass(sc) => spv::print::imm(wk.StorageClass, sc),
        };
        let header = format!(" in {}{}", addr_space, type_ascription_suffix);

        let body = match def {
            DeclDef::Imported(import) => Some(format!("= {}", import.print(printer))),
            DeclDef::Present(GlobalVarDefBody { initializer }) => {
                initializer.map(|initializer| {
                    // FIXME(eddyb) find a better syntax for this.
                    format!("init={}", initializer.print(printer))
                })
            }
        };

        let def = if header.contains("\n") {
            // The last line of `header` likely only contains a single `)`,
            // no need to further indent the body in that case.
            match body {
                Some(body) => header + " " + &body,
                None => header,
            }
        } else {
            printer.pretty_join_space(&header, body)
        };

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

        let sig = printer.pretty_join_comma_sep(
            "(",
            params.iter().enumerate().map(|(i, param)| {
                let AttrsAndDef { attrs, def } = param.print(printer);
                attrs
                    + &Value::FuncParam {
                        idx: i.try_into().unwrap(),
                    }
                    .print(printer)
                    + &def
            }),
            ",",
            &format!(") -> {}", ret_type.print(printer)),
        );

        let def = match def {
            DeclDef::Imported(import) => sig + " = " + &import.print(printer),
            DeclDef::Present(
                def @ FuncDefBody {
                    data_insts,
                    control_nodes,
                    body: _,
                    cfg,
                },
            ) => lazy_format!(|f| {
                writeln!(f, "{} {{", sig)?;
                for point in cfg.rev_post_order(def) {
                    let control_node = point.control_node();
                    let ControlNodeDef { kind, outputs } = &*control_nodes[control_node];

                    // Only handle each `ControlNode` once.
                    if let cfg::ControlPoint::Exit(_) = point {
                        match kind {
                            // `ControlNodeKind::UnstructuredMerge` only has an `Exit`
                            // (see also `cfg::ControlPoint`'s doc comment).
                            ControlNodeKind::UnstructuredMerge => {}

                            _ => continue,
                        }
                    }

                    let mut header = Use::ControlNode(control_node).print(printer);
                    if !outputs.is_empty() {
                        let mut outputs = outputs.iter().enumerate().map(|(output_idx, output)| {
                            let AttrsAndDef { attrs, def } = output.print(printer);
                            attrs
                                + &Value::ControlNodeOutput {
                                    control_node,
                                    output_idx: output_idx.try_into().unwrap(),
                                }
                                .print(printer)
                                + &def
                        });
                        let outputs_lhs = if outputs.len() == 1 {
                            outputs.next().unwrap()
                        } else {
                            printer.pretty_join_comma_sep("(", outputs, ",", ")")
                        };
                        header = outputs_lhs + " = " + &header;
                    }
                    writeln!(f, "  {} {{", header.replace("\n", "\n    "))?;
                    match kind {
                        ControlNodeKind::UnstructuredMerge => {
                            writeln!(f, "    /* unstructured merge */")?;
                        }
                        ControlNodeKind::Block { insts } => {
                            for &inst in insts {
                                let data_inst_def = &data_insts[inst];
                                let AttrsAndDef { attrs, mut def } = data_inst_def.print(printer);

                                if data_inst_def.output_type.is_some() {
                                    let header =
                                        format!("{} =", Use::DataInstOutput(inst).print(printer));
                                    // FIXME(eddyb) the reindenting here hurts more than
                                    // it helps, maybe it eneds a heuristics?
                                    def = if false {
                                        printer.pretty_join_space(&header, [def])
                                    } else {
                                        header + " " + &def
                                    };
                                }
                                writeln!(f, "    {}", (attrs + &def).replace("\n", "\n    "))?;
                            }

                            // Visually isolate the control-flow instruction.
                            if !insts.is_empty() {
                                writeln!(f)?;
                            }
                        }
                    }
                    if let Some(control_inst) =
                        cfg.control_insts.get(cfg::ControlPoint::Exit(control_node))
                    {
                        writeln!(
                            f,
                            "    {}",
                            control_inst.print(printer).replace("\n", "\n    ")
                        )?;
                    }
                    writeln!(f, "  }}")?;
                }
                write!(f, "}}")
            })
            .to_string(),
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
            DataInstKind::FuncCall(func) => format!("call {}", func.print(printer)),
            DataInstKind::SpvInst(spv::Inst { opcode, ref imms }) => {
                return AttrsAndDef {
                    attrs,
                    def: printer.pretty_spv_inst(opcode, imms, inputs, Print::print, *output_type),
                };
            }
            DataInstKind::SpvExtInst { ext_set, inst } => {
                // FIXME(eddyb) should this be rendered more compactly?
                format!(
                    "(OpExtInstImport<{:?}>).OpExtInst<{}>",
                    &printer.cx[ext_set], inst
                )
            }
        };

        // FIXME(eddyb) deduplicate the "parens + optional type ascription"
        // logic with `pretty_spv_inst`.
        let def = printer.pretty_join_comma_sep(
            &(header + "("),
            inputs.iter().map(|v| v.print(printer)),
            ",",
            &output_type
                .map(|ty| format!("){}", printer.pretty_type_ascription_suffix(ty)))
                .as_deref()
                .unwrap_or(")"),
        );

        AttrsAndDef { attrs, def }
    }
}

impl Print for cfg::ControlInst {
    type Output = String;
    fn print(&self, printer: &Printer<'_, '_>) -> String {
        let Self {
            attrs,
            kind,
            inputs,
            targets,
            target_merge_outputs,
        } = self;

        let attrs = attrs.print(printer);

        let mut targets: SmallVec<[_; 4]> = targets
            .iter()
            .map(|&point| {
                let mut target = format!(
                    "=> {}",
                    Use::ControlNode(point.control_node()).print(printer)
                );
                if let cfg::ControlPoint::Exit(control_node) = point {
                    target += ".exit";
                    if let Some(outputs) = target_merge_outputs.get(&control_node) {
                        target = printer.pretty_join_comma_sep(
                            &(target + "("),
                            outputs.iter().enumerate().map(|(output_idx, v)| {
                                Value::ControlNodeOutput {
                                    control_node: control_node,
                                    output_idx: output_idx.try_into().unwrap(),
                                }
                                .print(printer)
                                    + " <- "
                                    + &v.print(printer)
                            }),
                            ",",
                            ")",
                        );
                    }
                }
                target
            })
            .collect();

        let def = match *kind {
            cfg::ControlInstKind::Unreachable => {
                assert!(targets.is_empty() && inputs.is_empty());
                "unreachable".to_string()
            }
            cfg::ControlInstKind::Return => {
                assert!(targets.is_empty());
                match inputs[..] {
                    [] => "return".to_string(),
                    [v] => format!("return {}", v.print(printer)),
                    _ => unreachable!(),
                }
            }
            cfg::ControlInstKind::ExitInvocation(cfg::ExitInvocationKind::SpvInst(spv::Inst {
                opcode,
                ref imms,
            })) => {
                assert!(targets.is_empty());
                printer.pretty_spv_inst(opcode, imms, inputs, Print::print, None)
            }

            cfg::ControlInstKind::Branch => {
                assert_eq!((targets.len(), inputs.len()), (1, 0));
                format!("branch {}", targets[0])
            }

            cfg::ControlInstKind::SelectBranch(cfg::SelectionKind::BoolCond) => {
                assert_eq!((targets.len(), inputs.len()), (2, 1));

                // FIXME(eddyb) automate reindenting (and make it configurable).
                for target in &mut targets {
                    *target = target.replace("\n", "\n  ");
                }

                format!(
                    "if {} {{\n  {}\n}} else {{\n  {}\n}}",
                    inputs[0].print(printer),
                    targets[0],
                    targets[1]
                )
            }
            cfg::ControlInstKind::SelectBranch(cfg::SelectionKind::SpvInst(spv::Inst {
                opcode,
                ref imms,
            })) => {
                #[derive(Copy, Clone)]
                struct TargetLabelId;

                let header = printer.pretty_spv_inst(
                    opcode,
                    imms,
                    inputs
                        .iter()
                        .map(Ok)
                        .chain(targets.iter().map(|_| Err(TargetLabelId))),
                    |id, printer| match id {
                        Ok(v) => Some(v.print(printer)),
                        Err(TargetLabelId) => None,
                    },
                    None,
                );

                match targets.len() {
                    0 => header,
                    1 => header + " " + &targets[0],
                    _ => {
                        // FIXME(eddyb) automate reindenting (and make it configurable).
                        for target in &mut targets {
                            *target = target.replace("\n", "\n  ");
                        }
                        header + " {\n  " + &targets.join(",\n  ") + ",\n}"
                    }
                }
            }
        };

        attrs + &def
    }
}

impl Print for Value {
    type Output = String;
    fn print(&self, printer: &Printer<'_, '_>) -> String {
        match *self {
            Self::Const(ct) => ct.print(printer),
            Self::FuncParam { idx } => format!("param{}", idx),
            Self::ControlNodeOutput {
                control_node,
                output_idx,
            } => Use::ControlNodeOutput {
                control_node,
                output_idx,
            }
            .print(printer),
            Self::DataInstOutput(inst) => Use::DataInstOutput(inst).print(printer),
        }
    }
}
