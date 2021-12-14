use crate::visit::{DynInnerVisit, InnerVisit, Visitor};
use crate::{
    spv, AddrSpace, Attr, AttrSet, AttrSetDef, Block, BlockDef, BlockInput, Const, ConstCtor,
    ConstCtorArg, ConstDef, Context, ControlInst, ControlInstInput, ControlInstKind, DataInst,
    DataInstDef, DataInstInput, DataInstKind, DeclDef, ExportKey, Exportee, Func, FuncDecl,
    FuncDefBody, FuncParam, GlobalVar, GlobalVarDecl, GlobalVarDefBody, Import, Module,
    ModuleDebugInfo, ModuleDialect, Type, TypeCtor, TypeCtorArg, TypeDef, Value,
};
use format::lazy_format;
use indexmap::IndexMap;
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
    use_counts: IndexMap<Use, usize>,
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

    Block(Block),
    BlockInput { block: Block, input_idx: u32 },
    DataInstOutput(DataInst),
}

impl Use {
    fn category(self) -> &'static str {
        match self {
            Self::Interned(node) => node.category(),
            Self::GlobalVar(_) => "global_var",
            Self::Func(_) => "func",
            Self::Block(_) => "block",
            Self::BlockInput { .. } | Self::DataInstOutput(_) => "v",
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
            use_counts: IndexMap::new(),
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
            use_counts: IndexMap::new(),
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

            Value::BlockInput { block, input_idx } => {
                *self
                    .use_counts
                    .entry(Use::BlockInput { block, input_idx })
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
                if let Use::Block(_) | Use::BlockInput { .. } | Use::DataInstOutput(_) = use_kind {
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
                                    let has_compact_print = match ty_def.ctor {
                                        TypeCtor::SpvInst(opcode) => [
                                            wk.OpTypeBool,
                                            wk.OpTypeInt,
                                            wk.OpTypeFloat,
                                            wk.OpTypeVector,
                                        ]
                                        .contains(&opcode),
                                    };

                                    has_compact_print
                                        || ty_def
                                            .ctor_args
                                            .iter()
                                            .all(|arg| matches!(arg, TypeCtorArg::SpvImm(_)))
                                }
                                InternedNode::Const(ct) => {
                                    let ct_def = &cx[ct];

                                    // FIXME(eddyb) remove the duplication between
                                    // here and `ConstDef`'s `Print` impl.
                                    let has_compact_print = match ct_def.ctor {
                                        ConstCtor::SpvInst(opcode) => {
                                            [wk.OpConstantFalse, wk.OpConstantTrue, wk.OpConstant]
                                                .contains(&opcode)
                                        }
                                        _ => false,
                                    };

                                    has_compact_print
                                        || ct_def
                                            .ctor_args
                                            .iter()
                                            .all(|arg| matches!(arg, ConstCtorArg::SpvImm(_)))
                                }
                            }
                    }
                    Use::GlobalVar(_) | Use::Func(_) => false,
                    Use::Block(_) | Use::BlockInput { .. } | Use::DataInstOutput(_) => {
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
                        Use::Block(_) | Use::BlockInput { .. } | Use::DataInstOutput(_) => {
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
                let mut block_counter = 0;
                let mut value_counter = 0;

                for &block in &func_def_body.all_blocks {
                    let BlockDef {
                        inputs,
                        insts,
                        terminator: _,
                    } = &func_def_body.blocks[block];

                    // FIXME(eddyb) only insert here if the block is actually "used".
                    {
                        let idx = block_counter;
                        block_counter += 1;
                        use_styles.insert(Use::Block(block), UseStyle::Anon { idx });
                    }

                    let defined_values = inputs
                        .iter()
                        .enumerate()
                        .map(|(i, _)| Use::BlockInput {
                            block,
                            input_idx: i.try_into().unwrap(),
                        })
                        .chain(
                            insts
                                .iter()
                                .copied()
                                .filter(|&inst| {
                                    func_def_body.data_insts[inst].output_type.is_some()
                                })
                                .map(Use::DataInstOutput),
                        );
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
                            let def = attrs_of_def + &def;
                            if !def.chars().any(|c| c.is_whitespace()) {
                                def
                            } else {
                                printer.pretty_join_comma_sep("(", [def], "", ")")
                            }
                        }
                    }
                }
                Self::GlobalVar(_) => format!("/* unused global_var */_"),
                Self::Func(_) => format!("/* unused func */_"),
                Self::Block(_) | Self::BlockInput { .. } | Self::DataInstOutput(_) => {
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

                    let def = {
                        let header = format!("{}{} =", node.category(), idx);
                        match node {
                            InternedNode::AttrSet(_) => header + " " + &def,
                            InternedNode::Type(_) | InternedNode::Const(_) => {
                                printer.pretty_join_space(&header, [def])
                            }
                        }
                    };

                    AttrsAndDef {
                        attrs: attrs_of_def,
                        def,
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

            Self::SpvEntryPoint {
                params,
                interface_global_vars,
            } => {
                printer.pretty_join_comma_sep(
                    "(",
                    [printer.pretty_join_space(
                        "OpEntryPoint",
                        spv::print::operands(
                            params
                                .iter()
                                .map(|&imm| spv::print::PrintOperand::Imm(imm))
                                .chain(interface_global_vars.iter().map(|&gv| {
                                    spv::print::PrintOperand::IdLike(gv.print(printer))
                                })),
                        ),
                    )],
                    "",
                    ")",
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
            Attr::SpvAnnotation { opcode, params } => printer.pretty_join_space(
                opcode.name(),
                spv::print::operands(params.iter().map(|&imm| spv::print::PrintOperand::Imm(imm))),
            ),
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
            &Attr::SpvBitflagsOperand(imm) => {
                spv::print::operands([imm].iter().map(|&imm| spv::print::PrintOperand::Imm(imm)))
                    .collect::<SmallVec<[_; 1]>>()
                    .join(" ")
            }
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
        let compact_def = if let &TypeCtor::SpvInst(opcode) = ctor {
            if opcode == wk.OpTypeBool {
                Some("bool".to_string())
            } else if opcode == wk.OpTypeInt {
                let (width, signed) = match ctor_args[..] {
                    [
                        TypeCtorArg::SpvImm(spv::Imm::Short(_, width)),
                        TypeCtorArg::SpvImm(spv::Imm::Short(_, signedness)),
                    ] => (width, signedness != 0),
                    _ => unreachable!(),
                };

                Some(if signed {
                    format!("s{}", width)
                } else {
                    format!("u{}", width)
                })
            } else if opcode == wk.OpTypeFloat {
                let width = match ctor_args[..] {
                    [TypeCtorArg::SpvImm(spv::Imm::Short(_, width))] => width,
                    _ => unreachable!(),
                };

                Some(format!("f{}", width))
            } else if opcode == wk.OpTypeVector {
                let (elem_ty, elem_count) = match ctor_args[..] {
                    [
                        TypeCtorArg::Type(elem_ty),
                        TypeCtorArg::SpvImm(spv::Imm::Short(_, elem_count)),
                    ] => (elem_ty, elem_count),
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
                printer.pretty_join_space(
                    ctor.name(),
                    spv::print::operands(ctor_args.iter().map(|&arg| match arg {
                        TypeCtorArg::Type(ty) => {
                            spv::print::PrintOperand::IdLike(ty.print(printer))
                        }
                        TypeCtorArg::Const(ct) => {
                            spv::print::PrintOperand::IdLike(ct.print(printer))
                        }

                        TypeCtorArg::SpvImm(imm) => spv::print::PrintOperand::Imm(imm),
                    })),
                )
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

        let compact_def = if let &ConstCtor::SpvInst(opcode) = ctor {
            if opcode == wk.OpConstantFalse {
                Some("false".to_string())
            } else if opcode == wk.OpConstantTrue {
                Some("true".to_string())
            } else if opcode == wk.OpConstant {
                // HACK(eddyb) it's simpler to only handle a limited subset of
                // integer/float bit-widths, for now.
                let raw_bits = match ctor_args[..] {
                    [ConstCtorArg::SpvImm(spv::Imm::Short(_, x))] => Some(u64::from(x)),
                    [
                        ConstCtorArg::SpvImm(spv::Imm::LongStart(_, lo)),
                        ConstCtorArg::SpvImm(spv::Imm::LongCont(_, hi)),
                    ] => Some(u64::from(lo) | (u64::from(hi) << 32)),
                    _ => None,
                };

                let ty_def = &printer.cx[*ty];
                if let (Some(raw_bits), &TypeCtor::SpvInst(ty_opcode)) = (raw_bits, &ty_def.ctor) {
                    if ty_opcode == wk.OpTypeInt {
                        let (width, signed) = match ty_def.ctor_args[..] {
                            [
                                TypeCtorArg::SpvImm(spv::Imm::Short(_, width)),
                                TypeCtorArg::SpvImm(spv::Imm::Short(_, signedness)),
                            ] => (width, signedness != 0),
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
                        let width = match ty_def.ctor_args[..] {
                            [TypeCtorArg::SpvImm(spv::Imm::Short(_, width))] => width,
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
                printer.pretty_join_space(
                    &match ctor {
                        ConstCtor::PtrToGlobalVar(gv) => format!("&{}", gv.print(printer)),
                        ConstCtor::SpvInst(opcode) => opcode.name().to_string(),
                    },
                    spv::print::operands(ctor_args.iter().map(|&arg| match arg {
                        ConstCtorArg::Const(ct) => {
                            spv::print::PrintOperand::IdLike(ct.print(printer))
                        }

                        ConstCtorArg::SpvImm(imm) => spv::print::PrintOperand::Imm(imm),
                    }))
                    .chain([format!(": {}", ty.print(printer))]),
                )
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

        let ty = {
            // HACK(eddyb) get the pointee type from SPIR-V `OpTypePointer`, but
            // ideally the `GlobalVarDecl` would hold that type itself.
            let type_of_ptr_to_def = &printer.cx[*type_of_ptr_to];

            if type_of_ptr_to_def.ctor == TypeCtor::SpvInst(wk.OpTypePointer) {
                match type_of_ptr_to_def.ctor_args[1] {
                    TypeCtorArg::Type(ty) => ty.print(printer),
                    _ => unreachable!(),
                }
            } else {
                format!("pointee type of {}", type_of_ptr_to.print(printer))
            }
        };
        let addr_space = match *addr_space {
            AddrSpace::SpvStorageClass(sc) => spv::print::imm(wk.StorageClass, sc),
        };
        let header = format!(" in {}: {}", addr_space, ty);

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
            DeclDef::Present(FuncDefBody {
                data_insts,
                blocks,
                all_blocks,
            }) => lazy_format!(|f| {
                writeln!(f, "{} {{", sig)?;
                for &block in all_blocks {
                    let BlockDef {
                        inputs,
                        insts,
                        terminator,
                    } = &blocks[block];

                    let mut block_header = Use::Block(block).print(printer);
                    if !inputs.is_empty() {
                        block_header = printer.pretty_join_comma_sep(
                            &(block_header + "("),
                            inputs.iter().enumerate().map(|(input_idx, input)| {
                                let AttrsAndDef { attrs, def } = input.print(printer);
                                attrs
                                    + &Value::BlockInput {
                                        block,
                                        input_idx: input_idx.try_into().unwrap(),
                                    }
                                    .print(printer)
                                    + &def
                            }),
                            ",",
                            ")",
                        );
                    }
                    writeln!(f, "  {} {{", block_header)?;
                    for &inst in insts {
                        let data_inst_def = &data_insts[inst];
                        let AttrsAndDef { attrs, mut def } = data_inst_def.print(printer);

                        if data_inst_def.output_type.is_some() {
                            let header = format!("{} =", Use::DataInstOutput(inst).print(printer));
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

                    // Visually isolate the terminator
                    if !insts.is_empty() {
                        writeln!(f)?;
                    }

                    writeln!(
                        f,
                        "    {}",
                        terminator.print(printer).replace("\n", "\n    ")
                    )?;

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
        let Self { attrs, ty } = self;

        AttrsAndDef {
            attrs: attrs.print(printer),
            def: format!(": {}", ty.print(printer)),
        }
    }
}

impl Print for BlockInput {
    type Output = AttrsAndDef;
    fn print(&self, printer: &Printer<'_, '_>) -> AttrsAndDef {
        let Self { attrs, ty } = self;

        AttrsAndDef {
            attrs: attrs.print(printer),
            def: format!(": {}", ty.print(printer)),
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

        let inputs = spv::print::operands(inputs.iter().map(|input| match *input {
            DataInstInput::Value(v) => spv::print::PrintOperand::IdLike(v.print(printer)),

            DataInstInput::SpvImm(imm) => spv::print::PrintOperand::Imm(imm),
        }));
        let output_type = output_type.map(|ty| ty.print(printer));

        let def = match *kind {
            DataInstKind::FuncCall(func) => printer.pretty_join_comma_sep(
                &format!("call {}(", func.print(printer)),
                inputs,
                ",",
                &output_type.map_or(")".to_string(), |ty| format!(") : {}", ty)),
            ),
            DataInstKind::SpvInst(opcode) => printer.pretty_join_space(
                opcode.name(),
                inputs.chain(output_type.map(|ty| format!(": {}", ty))),
            ),
            DataInstKind::SpvExtInst { ext_set, inst } => {
                // FIXME(eddyb) should this be rendered more compactly?
                printer.pretty_join_space(
                    &format!(
                        "OpExtInst (OpExtInstImport {:?}) {}",
                        &printer.cx[ext_set], inst
                    ),
                    inputs.chain(output_type.map(|ty| format!(": {}", ty))),
                )
            }
        };

        AttrsAndDef { attrs, def }
    }
}

impl Print for ControlInst {
    type Output = String;
    fn print(&self, printer: &Printer<'_, '_>) -> String {
        let Self {
            attrs,
            kind,
            inputs,
            target_block_inputs,
        } = self;

        let attrs = attrs.print(printer);

        let def = printer.pretty_join_space(
            match kind {
                ControlInstKind::SpvInst(opcode) => opcode.name(),
            },
            spv::print::operands(inputs.iter().map(|input| match *input {
                ControlInstInput::Value(v) => spv::print::PrintOperand::IdLike(v.print(printer)),

                ControlInstInput::TargetBlock(block) => {
                    let block_header = Use::Block(block).print(printer);
                    spv::print::PrintOperand::IdLike(match target_block_inputs.get(&block) {
                        Some(block_inputs) => printer.pretty_join_comma_sep(
                            &(block_header + "("),
                            block_inputs.iter().map(|v| v.print(printer)),
                            ",",
                            ")",
                        ),
                        None => block_header,
                    })
                }

                ControlInstInput::SpvImm(imm) => spv::print::PrintOperand::Imm(imm),
            })),
        );

        attrs + &def
    }
}

impl Print for Value {
    type Output = String;
    fn print(&self, printer: &Printer<'_, '_>) -> String {
        match *self {
            Self::Const(ct) => ct.print(printer),
            Self::FuncParam { idx } => format!("param{}", idx),
            Self::BlockInput { block, input_idx } => {
                Use::BlockInput { block, input_idx }.print(printer)
            }
            Self::DataInstOutput(inst) => Use::DataInstOutput(inst).print(printer),
        }
    }
}
