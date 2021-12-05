use crate::visit::{DynInnerVisit, InnerVisit, Visitor};
use crate::{
    spv, AddrSpace, Attr, AttrSet, AttrSetDef, Const, ConstCtor, ConstCtorArg, ConstDef, Context,
    DeclDef, ExportKey, Exportee, Func, FuncDecl, FuncDefBody, GlobalVar, GlobalVarDecl,
    GlobalVarDefBody, Import, Misc, MiscInput, MiscKind, MiscOutput, Module, ModuleDebugInfo,
    ModuleDialect, Type, TypeCtor, TypeCtorArg, TypeDef,
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

    // HACK(eddyb) scope `MiscOutput` names per-function.
    current_func: Option<Func>,
    misc_output_by_spv_result_id: IndexMap<spv::Id, (Option<Func>, MiscOutput)>,
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

    // HACK(eddyb) this should be replaced by a proper non-ID def-use graph.
    MiscOutput { result_id: spv::Id },
}

impl Use {
    fn category(self) -> &'static str {
        match self {
            Self::Interned(node) => node.category(),
            Self::GlobalVar(_) => "global_var",
            Self::Func(_) => "func",
            Self::MiscOutput { .. } => unreachable!(),
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
            current_func: None,
            misc_output_by_spv_result_id: IndexMap::default(),
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
            current_func: None,
            misc_output_by_spv_result_id: IndexMap::default(),
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
                Some(func_decl) => {
                    let old_func = self.current_func.replace(func);
                    self.visit_func_decl(func_decl);
                    self.current_func = old_func;
                }

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

    fn visit_misc_output(&mut self, output: &'a MiscOutput) {
        match *output {
            MiscOutput::SpvValueResult { result_id, .. }
            | MiscOutput::SpvLabelResult { result_id } => {
                self.misc_output_by_spv_result_id
                    .insert(result_id, (self.current_func, *output));
            }
        }
        output.inner_visit_with(self);
    }

    fn visit_misc_input(&mut self, input: &'a MiscInput) {
        match *input {
            MiscInput::Const(_) => {}

            MiscInput::SpvImm(_) => {}

            // HACK(eddyb) assume that this ID matches `MiscOutput` of a `Misc`,
            // but this should be replaced by a proper non-ID def-use graph.
            MiscInput::SpvUntrackedId(id) => {
                *self
                    .use_counts
                    .entry(Use::MiscOutput { result_id: id })
                    .or_default() += 1;
            }
        }
        input.inner_visit_with(self);
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
    use_styles: IndexMap<Use, UseStyle>,

    global_var_decl_cache: &'b FxHashMap<GlobalVar, &'a GlobalVarDecl>,
    func_decl_cache: &'b FxHashMap<Func, &'a FuncDecl>,

    misc_output_by_spv_result_id: &'b IndexMap<spv::Id, (Option<Func>, MiscOutput)>,
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

        #[derive(Default)]
        struct AnonCounters {
            attr_sets: usize,
            types: usize,
            consts: usize,

            global_vars: usize,
            funcs: usize,
        }
        let mut anon_counters = AnonCounters::default();

        let mut use_styles: IndexMap<_, _> = plan
            .use_counts
            .iter()
            .map(|(&use_kind, &use_count)| {
                // HACK(eddyb) these are assigned later.
                if let Use::MiscOutput { .. } = use_kind {
                    return (use_kind, UseStyle::Inline);
                }

                let inline = match use_kind {
                    Use::Interned(node) => {
                        use_count == 1
                            || match node {
                                InternedNode::AttrSet(attrs) => cx[attrs].attrs.len() <= 1,
                                InternedNode::Type(ty) => {
                                    let ty_def = &cx[ty];
                                    ty_def
                                        .ctor_args
                                        .iter()
                                        .all(|arg| matches!(arg, TypeCtorArg::SpvImm(_)))
                                }
                                InternedNode::Const(ct) => {
                                    let ct_def = &cx[ct];
                                    ct_def
                                        .ctor_args
                                        .iter()
                                        .all(|arg| matches!(arg, ConstCtorArg::SpvImm(_)))
                                }
                            }
                    }
                    Use::GlobalVar(_) | Use::Func(_) | Use::MiscOutput { .. } => false,
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
                        Use::MiscOutput { .. } => unreachable!(),
                    };
                    let idx = *counter;
                    *counter += 1;
                    UseStyle::Anon { idx }
                };
                (use_kind, style)
            })
            .collect();

        #[derive(Default)]
        struct PerFuncAnonCounters {
            misc_spv_value_outputs: usize,
            misc_spv_label_outputs: usize,
        }
        let mut per_func_anon_counters = FxHashMap::<Option<Func>, PerFuncAnonCounters>::default();

        for (&result_id, &(maybe_func, misc_output)) in &plan.misc_output_by_spv_result_id {
            let ac = per_func_anon_counters.entry(maybe_func).or_default();
            let counter = match misc_output {
                MiscOutput::SpvValueResult { .. } => &mut ac.misc_spv_value_outputs,
                MiscOutput::SpvLabelResult { .. } => &mut ac.misc_spv_label_outputs,
            };
            let idx = *counter;
            *counter += 1;
            use_styles.insert(Use::MiscOutput { result_id }, UseStyle::Anon { idx });
        }

        Self {
            cx,
            use_styles,
            global_var_decl_cache: &plan.global_var_decl_cache,
            func_decl_cache: &plan.func_decl_cache,
            misc_output_by_spv_result_id: &plan.misc_output_by_spv_result_id,
        }
    }

    pub fn cx(&self) -> &'a Context {
        self.cx
    }

    /// Returns `header + " " + contents.join(" ")` if the resulting string can
    /// fit on one line, or a multi-line indented version otherwise.
    fn pretty_join_space(
        &self,
        header: &str,
        contents: impl IntoIterator<Item = String>,
    ) -> String {
        let mut contents: SmallVec<[_; 16]> = contents.into_iter().collect();

        // FIXME(eddyb) make max line width configurable.
        let max_line_len = 80;
        let fits_on_single_line = contents
            .iter()
            .try_fold(header.len(), |single_line_len, entry| {
                if entry.contains("\n") {
                    return None;
                }
                single_line_len
                    .checked_add(1)?
                    .checked_add(entry.len())
                    .filter(|&len| len <= max_line_len)
            })
            .is_some();

        let sep = if fits_on_single_line {
            " "
        } else {
            // FIXME(eddyb) automate reindenting (and make it configurable).
            for entry in &mut contents {
                *entry = entry.replace("\n", "\n  ");
            }
            "\n  "
        };
        let pieces = iter::once(header).chain(contents.iter().flat_map(|entry| [sep, entry]));

        let mut combined = String::with_capacity(pieces.clone().map(|s| s.len()).sum());
        combined.extend(pieces);
        combined
    }
}

pub trait Print {
    type Output;
    fn print(&self, printer: &Printer<'_, '_>) -> Self::Output;
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
                let category = match self {
                    Self::MiscOutput { result_id } => {
                        match printer.misc_output_by_spv_result_id[result_id].1 {
                            MiscOutput::SpvValueResult { .. } => "v",
                            MiscOutput::SpvLabelResult { .. } => "block",
                        }
                    }
                    _ => self.category(),
                };
                format!("{}{}{}", prefix, category, idx)
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
                            // FIXME(eddyb) automate reindenting (and make it configurable).
                            if def.contains("\n") {
                                format!("(\n  {}\n)", def.replace("\n", "\n  "))
                            } else {
                                format!("({})", def)
                            }
                        }
                    }
                }
                Self::GlobalVar(_) => format!("/* unused global_var */_"),
                Self::Func(_) => format!("/* unused func */_"),
                Self::MiscOutput { .. } => "_".to_string(),
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

                    // FIXME(eddyb) automate reindenting (and make it configurable).
                    let reindent_def = match node {
                        InternedNode::AttrSet(_) => false,
                        InternedNode::Type(_) | InternedNode::Const(_) => def.contains("\n"),
                    };
                    let def = if reindent_def {
                        format!(
                            "{}{} =\n  {}",
                            node.category(),
                            idx,
                            def.replace("\n", "\n  ")
                        )
                    } else {
                        format!("{}{} = {}", node.category(), idx, def)
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
                            // FIXME(eddyb) this prints as `Display(...)`, as if
                            // the `fmt::Debug` impl was `#[derive]`'d on it.
                            lazy_format!(move |f| {
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
                let key =
                    printer.pretty_join_space(
                        "OpEntryPoint",
                        spv::print::operands(
                            params
                                .iter()
                                .map(|&imm| spv::print::PrintOperand::Imm(imm))
                                .chain(interface_global_vars.iter().map(|&gv| {
                                    spv::print::PrintOperand::IdLike(gv.print(printer))
                                })),
                        ),
                    );

                // FIXME(eddyb) automate reindenting (and make it configurable).
                if key.contains("\n") {
                    format!("(\n  {}\n)", key.replace("\n", "\n  "))
                } else {
                    format!("({})", key)
                }
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
        lazy_format!(|f| {
            let Self { attrs } = self;

            // Avoid printing anything instead of `#{}`.
            if attrs.is_empty() {
                return Ok(());
            }

            let force_multiline = attrs.len() > 1;
            write!(f, "#{{")?;
            if force_multiline {
                writeln!(f)?;
            }
            for attr in attrs {
                let attr = match attr {
                    Attr::SpvAnnotation { opcode, params } => printer.pretty_join_space(
                        opcode.name(),
                        spv::print::operands(
                            params.iter().map(|&imm| spv::print::PrintOperand::Imm(imm)),
                        ),
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
                            format!("/* at {}:{}:{} */", file_path, line, col)
                        } else {
                            format!("/* at {:?}:{}:{} */", file_path, line, col)
                        }
                    }
                    &Attr::SpvBitflagsOperand(imm) => spv::print::operands(
                        [imm].iter().map(|&imm| spv::print::PrintOperand::Imm(imm)),
                    )
                    .collect::<SmallVec<[_; 1]>>()
                    .join(" "),
                };
                if force_multiline || attr.contains("\n") {
                    if !force_multiline {
                        writeln!(f)?;
                    }
                    writeln!(f, "  {},", attr.replace("\n", "\n  "))?;
                } else {
                    write!(f, "{}", attr)?;
                }
            }
            write!(f, "}}")
        })
        .to_string()
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

        AttrsAndDef {
            attrs: attrs.print(printer),
            def: printer.pretty_join_space(
                ctor.name(),
                spv::print::operands(ctor_args.iter().map(|&arg| match arg {
                    TypeCtorArg::Type(ty) => spv::print::PrintOperand::IdLike(ty.print(printer)),
                    TypeCtorArg::Const(ct) => spv::print::PrintOperand::IdLike(ct.print(printer)),

                    TypeCtorArg::SpvImm(imm) => spv::print::PrintOperand::Imm(imm),
                })),
            ),
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

        AttrsAndDef {
            attrs: attrs.print(printer),
            def: printer.pretty_join_space(
                &match ctor {
                    ConstCtor::PtrToGlobalVar(gv) => format!("&{}", gv.print(printer)),
                    ConstCtor::SpvInst(opcode) => opcode.name().to_string(),
                },
                spv::print::operands(ctor_args.iter().map(|&arg| match arg {
                    ConstCtorArg::Const(ct) => spv::print::PrintOperand::IdLike(ct.print(printer)),

                    ConstCtorArg::SpvImm(imm) => spv::print::PrintOperand::Imm(imm),
                }))
                .chain([format!(": {}", ty.print(printer))]),
            ),
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
            ret_type: _,
            ty,
            def,
        } = self;

        let wk = &spv::spec::Spec::get().well_known;

        let sig = {
            // HACK(eddyb) get the signature from SPIR-V `OpTypeFunction`, but
            // ideally the `FuncDecl` would hold all of the types itself.
            let func_ty_def = &printer.cx[*ty];

            if func_ty_def.ctor == TypeCtor::SpvInst(wk.OpTypeFunction) {
                let mut types = func_ty_def.ctor_args.iter().map(|&arg| match arg {
                    TypeCtorArg::Type(ty) => ty.print(printer),
                    _ => unreachable!(),
                });
                let ret_type = types.next().unwrap();
                let param_types: SmallVec<[_; 16]> = types.collect();

                // FIXME(eddyb) enforce a max line width - sadly, this cannot
                // just use `pretty_join_space`, because that doesn't do commas.
                let fits_on_single_line = param_types.iter().all(|ty| !ty.contains("\n"));

                let params = if fits_on_single_line {
                    format!("({})", param_types.join(", "))
                } else {
                    // FIXME(eddyb) automate reindenting (and make it configurable).
                    format!("(\n  {},\n)", param_types.join(",\n").replace("\n", "\n  "))
                };
                params + " -> " + &ret_type
            } else {
                format!("(...): {}", ty.print(printer))
            }
        };

        let def = match def {
            DeclDef::Imported(import) => sig + " = " + &import.print(printer),
            DeclDef::Present(FuncDefBody { insts }) => lazy_format!(|f| {
                writeln!(f, "{} {{", sig)?;
                let mut in_block = false;
                for misc in insts {
                    // HACK(eddyb) special-case `OpLabel` to be like explicit blocks.
                    if let Some(MiscOutput::SpvLabelResult { result_id }) = misc.output {
                        assert!(misc.kind == MiscKind::SpvInst(wk.OpLabel));
                        assert!(misc.inputs.is_empty());

                        if in_block {
                            writeln!(f, "  }}")?;
                        }

                        writeln!(f, "  {} {{", Use::MiscOutput { result_id }.print(printer))?;
                        in_block = true;
                        continue;
                    }

                    let inst = misc.print(printer);
                    if in_block {
                        writeln!(f, "    {}", inst.replace("\n", "\n    "))?;
                    } else {
                        writeln!(f, "  {}", inst.replace("\n", "\n  "))?;
                    }
                }
                if in_block {
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

impl Print for Misc {
    type Output = String;
    fn print(&self, printer: &Printer<'_, '_>) -> String {
        let Self {
            attrs,
            kind,
            output,
            inputs,
        } = self;

        let attrs = attrs.print(printer);

        // HACK(eddyb) assume that these IDs match `MiscOutput` of `Misc`s,
        // but this should be replaced by a proper non-ID def-use graph.
        let spv_id_to_string = |id| Use::MiscOutput { result_id: id }.print(printer);

        let (lhs, result_type) = match *output {
            Some(MiscOutput::SpvValueResult {
                result_type,
                result_id,
            }) => (
                Some(spv_id_to_string(result_id)),
                Some(format!(": {}", result_type.print(printer))),
            ),
            Some(MiscOutput::SpvLabelResult { result_id }) => {
                (Some(spv_id_to_string(result_id)), None)
            }
            None => (None, None),
        };

        let rhs = printer.pretty_join_space(
            &match *kind {
                MiscKind::FuncCall(func) => format!("call {}", func.print(printer)),
                MiscKind::SpvInst(opcode) => opcode.name().to_string(),
                MiscKind::SpvExtInst { ext_set, inst } => {
                    // FIXME(eddyb) should this be rendered more compactly?
                    format!(
                        "OpExtInst (OpExtInstImport {:?}) {}",
                        &printer.cx[ext_set], inst
                    )
                }
            },
            spv::print::operands(inputs.iter().map(|input| match *input {
                MiscInput::Const(ct) => spv::print::PrintOperand::IdLike(ct.print(printer)),

                MiscInput::SpvImm(imm) => spv::print::PrintOperand::Imm(imm),
                MiscInput::SpvUntrackedId(id) => {
                    spv::print::PrintOperand::IdLike(spv_id_to_string(id))
                }
            }))
            .chain(result_type),
        );

        let def = match lhs {
            Some(lhs) => printer.pretty_join_space(&format!("{} =", lhs), [rhs]),
            None => rhs,
        };

        attrs + &def
    }
}
