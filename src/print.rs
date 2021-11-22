use crate::visit::{DynInnerVisit, InnerVisit, Visitor};
use crate::{
    spv, AddrSpace, Attr, AttrSet, AttrSetDef, Const, ConstCtor, ConstCtorArg, ConstDef, Context,
    Func, GlobalVar, GlobalVarDef, Misc, MiscInput, MiscOutput, Module, ModuleDebugInfo,
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

    /// When visiting anything module-stored (such as global vars), the module
    /// is needed to go from the index to the definition, which is then cached.
    current_module: Option<&'a Module>,
    global_var_def_cache: FxHashMap<GlobalVar, &'a GlobalVarDef>,

    nodes: Vec<Node<'a>>,
    use_counts: IndexMap<Use, usize>,
}

/// Printing `Plan` entry, an effective reification of SPIR-T's implicit DAG.
#[derive(Copy, Clone)]
enum Node<'a> {
    /// Nodes that involve interning and require extra processing to print
    /// (see also `InternedNode`).
    Interned(InternedNode),

    GlobalVar(GlobalVar),

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

trait DynNode<'a>: DynInnerVisit<'a, Plan<'a>> + Print {}
impl<'a, T: DynInnerVisit<'a, Plan<'a>> + Print> DynNode<'a> for T {}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
enum Use {
    Interned(InternedNode),

    GlobalVar(GlobalVar),

    // HACK(eddyb) this should be replaced by a proper non-ID def-use graph.
    MiscOutput { result_id: spv::Id },
}

impl Use {
    fn category(self) -> &'static str {
        match self {
            Self::Interned(node) => node.category(),
            Self::GlobalVar(..) => "global_var",
            Self::MiscOutput { .. } => "misc",
        }
    }
}

impl<'a> Plan<'a> {
    pub fn empty(module: &'a Module) -> Self {
        Self {
            cx: module.cx_ref(),
            current_module: Some(module),
            global_var_def_cache: FxHashMap::default(),
            nodes: vec![],
            use_counts: IndexMap::new(),
        }
    }

    /// Like `empty`, but without supporting anything module-stored (like global vars).
    pub fn empty_outside_module(cx: &'a Context) -> Self {
        Self {
            cx,
            current_module: None,
            global_var_def_cache: FxHashMap::default(),
            nodes: vec![],
            use_counts: IndexMap::new(),
        }
    }

    /// Create a `Plan` with all of `root`'s dependencies, followed by `root` itself.
    pub fn for_root(
        module: &'a Module,
        root: &'a (impl DynInnerVisit<'a, Plan<'a>> + Print),
    ) -> Self {
        let mut plan = Self::empty(module);
        plan.use_node(Node::Dyn(root));
        plan
    }

    /// Like `for_root`, but without supporting anything module-stored (like global vars).
    pub fn for_root_outside_module(
        cx: &'a Context,
        root: &'a (impl DynInnerVisit<'a, Plan<'a>> + Print),
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

            Node::GlobalVar(gv) => match self.global_var_def_cache.get(&gv).copied() {
                Some(gv_def) => self.visit_global_var_def(gv_def),

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
                self.global_var_def_cache
                    .insert(gv, &module.global_vars[gv]);
            }

            // FIXME(eddyb) should this be a hard error?
            None => {}
        }
        self.use_node(Node::GlobalVar(gv));
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
    fn visit_func(&mut self, func: &'a Func) {
        self.use_node(Node::Dyn(func));
    }

    fn visit_misc_input(&mut self, input: &'a MiscInput) {
        match *input {
            MiscInput::Type(_) | MiscInput::Const(_) => {}

            MiscInput::SpvImm(_) | MiscInput::SpvExtInstImport(_) => {}

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
        for &node in &self.nodes {
            let def = match node {
                Node::Interned(node) => match printer.use_styles.get(&Use::Interned(node)).copied()
                {
                    Some(style @ UseStyle::Anon { .. }) => {
                        printer.interned_node_def_to_string(node, style)
                    }
                    _ => String::new(),
                },

                Node::GlobalVar(gv) => match self.global_var_def_cache.get(&gv) {
                    Some(gv_def) => {
                        let attrs = gv_def.attrs.print_to_string(&printer);
                        let def = printer.pretty_join_space(
                            &format!("{} =", gv.print_to_string(&printer)),
                            [gv_def.print_to_string(&printer)],
                        );
                        attrs + &def
                    }
                    None => String::new(),
                },

                Node::Dyn(node) => node.print_to_string(&printer),
            };
            if !def.is_empty() {
                writeln!(f, "{}", def)?;
            }
        }
        Ok(())
    }
}

pub struct Printer<'a> {
    cx: &'a Context,
    use_styles: IndexMap<Use, UseStyle>,
}

/// How an use of a node should be printed.
#[derive(Copy, Clone)]
enum UseStyle {
    /// Refer to this node by its category and an `idx` (e.g. `"attrs123"`).
    Anon { idx: usize },

    /// Print this node inline at the use site.
    Inline,
}

impl<'a> Printer<'a> {
    fn new(plan: &Plan<'a>) -> Self {
        let cx = plan.cx;

        #[derive(Default)]
        struct AnonCounters {
            attr_sets: usize,
            types: usize,
            consts: usize,

            global_vars: usize,

            misc_outputs: usize,
        }
        let mut anon_counters = AnonCounters::default();

        let use_styles = plan
            .use_counts
            .iter()
            .map(|(&use_kind, &use_count)| {
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
                    Use::GlobalVar(_) | Use::MiscOutput { .. } => false,
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
                        Use::MiscOutput { .. } => &mut ac.misc_outputs,
                    };
                    let idx = *counter;
                    *counter += 1;
                    UseStyle::Anon { idx }
                };
                (use_kind, style)
            })
            .collect();

        Self { cx, use_styles }
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

    fn interned_node_def_to_string(&self, node: InternedNode, style: UseStyle) -> String {
        let (attrs_of_def, def) = match node {
            InternedNode::AttrSet(attrs) => (None, self.cx[attrs].print_to_string(self)),
            InternedNode::Type(ty) => {
                let ty_def = &self.cx[ty];
                (Some(ty_def.attrs), ty_def.print_to_string(self))
            }
            InternedNode::Const(ct) => {
                let ct_def = &self.cx[ct];
                (Some(ct_def.attrs), ct_def.print_to_string(self))
            }
        };
        let attrs_of_def = attrs_of_def.map_or(String::new(), |attrs| attrs.print_to_string(self));

        match style {
            UseStyle::Anon { idx } => {
                // FIXME(eddyb) automate reindenting (and make it configurable).
                let reindent_def = match node {
                    InternedNode::AttrSet(_) => false,
                    InternedNode::Type(_) | InternedNode::Const(_) => def.contains("\n"),
                };
                if reindent_def {
                    format!(
                        "{}{}{} =\n  {}",
                        attrs_of_def,
                        node.category(),
                        idx,
                        def.replace("\n", "\n  ")
                    )
                } else {
                    format!("{}{}{} = {}", attrs_of_def, node.category(), idx, def)
                }
            }
            UseStyle::Inline => match node {
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
            },
        }
    }
}

pub trait Print {
    fn print_to_string(&self, printer: &Printer<'_>) -> String;
}

impl Print for Use {
    fn print_to_string(&self, printer: &Printer<'_>) -> String {
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
                Self::Interned(node) => printer.interned_node_def_to_string(node, style),
                Self::GlobalVar(_) => format!("/* unused global_var */_"),
                Self::MiscOutput { result_id } => format!("/* unused %{} */_", result_id),
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
    fn print_to_string(&self, printer: &Printer<'_>) -> String {
        Use::Interned(InternedNode::AttrSet(*self)).print_to_string(printer)
    }
}
impl Print for Type {
    fn print_to_string(&self, printer: &Printer<'_>) -> String {
        Use::Interned(InternedNode::Type(*self)).print_to_string(printer)
    }
}
impl Print for Const {
    fn print_to_string(&self, printer: &Printer<'_>) -> String {
        Use::Interned(InternedNode::Const(*self)).print_to_string(printer)
    }
}
impl Print for GlobalVar {
    fn print_to_string(&self, printer: &Printer<'_>) -> String {
        Use::GlobalVar(*self).print_to_string(printer)
    }
}

impl Print for Module {
    fn print_to_string(&self, _printer: &Printer<'_>) -> String {
        lazy_format!(|_f| {
            // Nothing left to print at the end of the module.
            Ok(())
        })
        .to_string()
    }
}

impl Print for ModuleDialect {
    fn print_to_string(&self, _printer: &Printer<'_>) -> String {
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
    fn print_to_string(&self, printer: &Printer<'_>) -> String {
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

impl Print for TypeDef {
    fn print_to_string(&self, printer: &Printer<'_>) -> String {
        let Self {
            ctor,
            ctor_args,
            attrs: _,
        } = self;

        printer.pretty_join_space(
            ctor.name(),
            spv::print::operands(ctor_args.iter().map(|&arg| match arg {
                TypeCtorArg::Type(ty) => {
                    spv::print::PrintOperand::IdLike(ty.print_to_string(printer))
                }
                TypeCtorArg::Const(ct) => {
                    spv::print::PrintOperand::IdLike(ct.print_to_string(printer))
                }

                TypeCtorArg::SpvImm(imm) => spv::print::PrintOperand::Imm(imm),
            })),
        )
    }
}

impl Print for ConstDef {
    fn print_to_string(&self, printer: &Printer<'_>) -> String {
        let Self {
            ty,
            ctor,
            ctor_args,
            attrs: _,
        } = self;

        printer.pretty_join_space(
            &match ctor {
                ConstCtor::PtrToGlobalVar(gv) => format!("&{}", gv.print_to_string(printer)),
                ConstCtor::SpvInst(opcode) => opcode.name().to_string(),
            },
            spv::print::operands(ctor_args.iter().map(|&arg| match arg {
                ConstCtorArg::Const(ct) => {
                    spv::print::PrintOperand::IdLike(ct.print_to_string(printer))
                }

                ConstCtorArg::SpvImm(imm) => spv::print::PrintOperand::Imm(imm),
            }))
            .chain([format!(": {}", ty.print_to_string(printer))]),
        )
    }
}

impl Print for GlobalVarDef {
    fn print_to_string(&self, printer: &Printer<'_>) -> String {
        let Self {
            type_of_ptr_to,
            addr_space,
            initializer,
            attrs: _,
        } = self;

        let wk = &spv::spec::Spec::get().well_known;

        let ty = {
            // HACK(eddyb) get the pointee type from SPIR-V `OpTypePointer`, but
            // ideally the `GlobalVarDef` would hold that type itself.
            let type_of_ptr_to_def = &printer.cx[*type_of_ptr_to];

            if type_of_ptr_to_def.ctor == TypeCtor::SpvInst(wk.OpTypePointer) {
                match type_of_ptr_to_def.ctor_args[1] {
                    TypeCtorArg::Type(ty) => ty.print_to_string(printer),
                    _ => unreachable!(),
                }
            } else {
                format!(
                    "pointee type of {}",
                    type_of_ptr_to.print_to_string(printer)
                )
            }
        };
        let addr_space = match *addr_space {
            AddrSpace::SpvStorageClass(sc) => spv::print::imm(wk.StorageClass, sc),
        };
        let initializer = initializer.map(|initializer| {
            // FIXME(eddyb) find a better syntax for this.
            format!("init={}", initializer.print_to_string(printer))
        });

        printer.pretty_join_space(
            &format!("var({})", addr_space),
            initializer.into_iter().chain([format!(": {}", ty)]),
        )
    }
}

impl Print for Func {
    fn print_to_string(&self, printer: &Printer<'_>) -> String {
        lazy_format!(|f| {
            let Self { insts } = self;

            // FIXME(eddyb) describe the function outside of its `insts`.
            writeln!(f, "func {{")?;
            for misc in insts {
                writeln!(
                    f,
                    "  {}",
                    misc.print_to_string(printer).replace("\n", "\n  ")
                )?;
            }
            write!(f, "}}")
        })
        .to_string()
    }
}

impl Print for Misc {
    fn print_to_string(&self, printer: &Printer<'_>) -> String {
        let Self {
            kind,
            output,
            inputs,
            attrs,
        } = self;

        let attrs = attrs.print_to_string(printer);

        // HACK(eddyb) assume that these IDs match `MiscOutput` of `Misc`s,
        // but this should be replaced by a proper non-ID def-use graph.
        let spv_id_to_string = |id| Use::MiscOutput { result_id: id }.print_to_string(printer);

        let lhs = output.map(|output| match output {
            MiscOutput::SpvResult {
                result_type,
                result_id,
            } => {
                let result = spv_id_to_string(result_id);
                match result_type {
                    Some(ty) => format!("{}: {}", result, ty.print_to_string(printer)),
                    None => result,
                }
            }
        });

        let rhs = printer.pretty_join_space(
            kind.name(),
            spv::print::operands(inputs.iter().map(|input| match *input {
                MiscInput::Type(ty) => {
                    spv::print::PrintOperand::IdLike(ty.print_to_string(printer))
                }
                MiscInput::Const(ct) => {
                    spv::print::PrintOperand::IdLike(ct.print_to_string(printer))
                }

                MiscInput::SpvImm(imm) => spv::print::PrintOperand::Imm(imm),
                MiscInput::SpvUntrackedId(id) => {
                    spv::print::PrintOperand::IdLike(spv_id_to_string(id))
                }
                MiscInput::SpvExtInstImport(name) => spv::print::PrintOperand::IdLike(format!(
                    "(OpExtInstImport {:?})",
                    &printer.cx[name]
                )),
            })),
        );

        let def = match lhs {
            Some(lhs) => printer.pretty_join_space(&format!("{} =", lhs), [rhs]),
            None => rhs,
        };

        attrs + &def
    }
}

impl Print for AttrSetDef {
    fn print_to_string(&self, printer: &Printer<'_>) -> String {
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
                    Attr::SpvEntryPoint {
                        params,
                        interface_global_vars,
                    } => printer.pretty_join_space(
                        "OpEntryPoint",
                        spv::print::operands(
                            params
                                .iter()
                                .map(|&imm| spv::print::PrintOperand::Imm(imm))
                                .chain(interface_global_vars.0.iter().map(|&gv| {
                                    spv::print::PrintOperand::IdLike(gv.print_to_string(printer))
                                })),
                        ),
                    ),
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
