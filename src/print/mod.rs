//! Pretty-printing anything in the IR, from whole [`Module`]s to their leaves.
//!
//! # Usage
//!
//! To start, create a [`Plan`] (through e.g. [`Plan::for_root`] or [`Plan::for_module`]),
//! which will track the entire (transitive) set of (interned/entity) dependencies
//! required to produce complete pretty-printing outputs.
//!
//! On a [`Plan`], use [`.pretty_print()`](Plan::pretty_print) to print everything,
//! and get a "pretty document", with layout (inline-vs-multi-line decisions,
//! auto-indentation, etc.) already performed, and which supports outputting:
//! * plain text: `fmt::Display` (`{}` formatting) or `.to_string()`
//! * HTML (styled and hyperlinked): [`.render_to_html()`](Versions::render_to_html)
#![allow(rustdoc::private_intra_doc_links)]
//!   (returning a [`pretty::HtmlSnippet`])

// FIXME(eddyb) stop using `itertools` for methods like `intersperse` when they
// get stabilized on `Iterator` instead.
#![allow(unstable_name_collisions)]
use itertools::Itertools as _;

use crate::func_at::FuncAt;
use crate::print::multiversion::Versions;
use crate::qptr::{self, QPtrAttr, QPtrMemUsage, QPtrMemUsageKind, QPtrOp, QPtrUsage};
use crate::visit::{DynVisit, InnerVisit, Visit, Visitor};
use crate::{
    cfg, spv, AddrSpace, Attr, AttrSet, AttrSetDef, Const, ConstCtor, ConstDef, Context,
    ControlNode, ControlNodeDef, ControlNodeKind, ControlNodeOutputDecl, ControlRegion,
    ControlRegionDef, ControlRegionInputDecl, DataInst, DataInstDef, DataInstForm, DataInstFormDef,
    DataInstKind, DeclDef, Diag, DiagLevel, DiagMsgPart, EntityListIter, ExportKey, Exportee, Func,
    FuncDecl, FuncParam, FxIndexMap, GlobalVar, GlobalVarDecl, GlobalVarDefBody, Import, Module,
    ModuleDebugInfo, ModuleDialect, OrdAssertEq, SelectionKind, Type, TypeCtor, TypeCtorArg,
    TypeDef, Value,
};
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use std::collections::hash_map::Entry;
use std::mem;

mod multiversion;
mod pretty;

/// "Definitions-before-uses" / "topo-sorted" printing plan.
///
/// In order to represent parts of a DAG textually, it first needs to have its
/// nodes "flattened" into an order (also known as "topo(logical) sorting"),
/// which [`Plan`] wholly records, before any printing can commence.
///
/// Additionally, nodes without a significant identity (i.e. interned ones) may
/// have their separate definition omitted in some cases where printing them
/// inline at their use site(s) is preferred (e.g. when they have a single use).
///
/// Once a [`Plan`] contains everything that needs to be printed, calling the
/// [`.pretty_print()`](Plan::pretty_print) method will print all of the nodes
/// in the [`Plan`], and its return value can be e.g. formatted with [`fmt::Display`].
pub struct Plan<'a> {
    cx: &'a Context,

    /// When visiting module-stored nodes, the [`Module`] is needed to map the
    /// [`Node`] to the (per-version) definition, which is then stored in the
    /// (per-version) [`FxHashMap`] within `per_version_name_and_node_defs`.
    current_module: Option<&'a Module>,

    /// Versions allow comparing multiple copies of the same e.g. [`Module`],
    /// with definitions sharing a [`Node`] key being shown together.
    ///
    /// Each `per_version_name_and_node_defs` entry contains a "version" with:
    /// * a descriptive name (e.g. the name of a pass that produced that version)
    ///   * the name is left empty in the default single-version mode
    /// * its [`Node`] definitions (dynamic via the [`DynNodeDef`] helper trait)
    ///
    /// Specific [`Node`]s may be present in only a subset of versions, and such
    /// a distinction will be reflected in the output.
    ///
    /// For [`Node`] collection, the last entry consistutes the "active" version.
    per_version_name_and_node_defs: Vec<(String, FxHashMap<Node, &'a dyn DynNodeDef<'a>>)>,

    /// Merged per-[`Use`] counts across all versions.
    ///
    /// That is, each [`Use`] maps to the largest count of that [`Use`] in any version,
    /// as opposed to their sum. This approach avoids pessimizing e.g. inline
    /// printing of interned definitions, which may need the use count to be `1`.
    use_counts: FxIndexMap<Use, usize>,
}

/// Helper for printing a mismatch error between two nodes (e.g. types), while
/// taking advantage of the print infrastructure that will print all dependencies.
pub struct ExpectedVsFound<E, F> {
    pub expected: E,
    pub found: F,
}

/// Print [`Plan`] top-level entry, an effective reification of SPIR-T's implicit DAG.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
enum Node {
    /// Either a whole [`Module`], or some other printable type passed to
    /// [`Plan::for_root`] (e.g. [`ExpectedVsFound`]).
    Root,

    /// Definitions for all [`CxInterned`] that need them, grouped together.
    AllCxInterned,

    // FIXME(eddyb) these do not support multiple `Module`s as they don't have
    // any way to distinguish between instances of them from different `Module`s.
    ModuleDialect,
    ModuleDebugInfo,

    GlobalVar(GlobalVar),
    Func(Func),
}

impl Node {
    fn category(self) -> Result<&'static str, &'static str> {
        match self {
            Self::Root => Err("Node::Root"),

            Self::AllCxInterned => Err("Node::AllCxInterned"),

            // FIXME(eddyb) these don't have the same kind of `{category}{idx}`
            // formatting, so maybe they don't belong in here to begin with?
            Self::ModuleDialect => Ok("module.dialect"),
            Self::ModuleDebugInfo => Ok("module.debug_info"),

            Self::GlobalVar(_) => Ok("global_var"),
            Self::Func(_) => Ok("func"),
        }
    }
}

/// Helper for [`Node::AllCxInterned`]'s definition, to  be used in `node_defs`.
struct AllCxInterned;

/// Anything interned in [`Context`], that might need to be printed once
/// (as part of [`Node::AllCxInterned`]) and referenced multiple times.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
enum CxInterned {
    AttrSet(AttrSet),
    Type(Type),
    Const(Const),
}

impl CxInterned {
    fn category(self) -> &'static str {
        match self {
            Self::AttrSet(_) => "attrs",
            Self::Type(_) => "type",
            Self::Const(_) => "const",
        }
    }
}

/// A [`Print`] `Output` type that splits the attributes from the main body of the
/// definition, allowing additional processing before they get concatenated.
#[derive(Default)]
pub struct AttrsAndDef {
    pub attrs: pretty::Fragment,

    /// Definition that typically looks like one of these cases:
    /// * ` = ...` for `name = ...`
    /// * `(...) {...}` for `name(...) {...}` (i.e. functions)
    ///
    /// Where `name` is added later (i.e. between `attrs` and `def_without_name`).
    pub def_without_name: pretty::Fragment,
}

trait DynNodeDef<'a>: DynVisit<'a, Plan<'a>> + Print<Output = AttrsAndDef> {}
impl<'a, T: DynVisit<'a, Plan<'a>> + Print<Output = AttrsAndDef>> DynNodeDef<'a> for T {}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
enum Use {
    Node(Node),

    CxInterned(CxInterned),

    ControlRegionLabel(ControlRegion),

    // FIXME(eddyb) these are `Value`'s variants except `Const`, maybe `Use`
    // should just use `Value` and assert it's never `Const`?
    ControlRegionInput {
        region: ControlRegion,
        input_idx: u32,
    },
    ControlNodeOutput {
        control_node: ControlNode,
        output_idx: u32,
    },
    DataInstOutput(DataInst),

    // NOTE(eddyb) these overlap somewhat with other cases, but they're always
    // generated, even when there is no "use", for `multiversion` alignment.
    AlignmentAnchorForControlRegion(ControlRegion),
    AlignmentAnchorForControlNode(ControlNode),
    AlignmentAnchorForDataInst(DataInst),
}

impl From<Value> for Use {
    fn from(value: Value) -> Self {
        match value {
            Value::Const(ct) => Use::CxInterned(CxInterned::Const(ct)),
            Value::ControlRegionInput { region, input_idx } => {
                Use::ControlRegionInput { region, input_idx }
            }
            Value::ControlNodeOutput {
                control_node,
                output_idx,
            } => Use::ControlNodeOutput {
                control_node,
                output_idx,
            },
            Value::DataInstOutput(inst) => Use::DataInstOutput(inst),
        }
    }
}

impl Use {
    // HACK(eddyb) this is used in `AttrsAndDef::insert_name_before_def` to
    // detect alignment anchors specifically, so it needs to not overlap with
    // any other category name.
    const ANCHOR_ALIGNMENT_CATEGORY: &str = "AA";

    fn category(self) -> &'static str {
        match self {
            Self::Node(node) => node.category().unwrap(),
            Self::CxInterned(interned) => interned.category(),
            Self::ControlRegionLabel(_) => "label",

            Self::ControlRegionInput { .. }
            | Self::ControlNodeOutput { .. }
            | Self::DataInstOutput(_) => "v",

            Self::AlignmentAnchorForControlRegion(_)
            | Self::AlignmentAnchorForControlNode(_)
            | Self::AlignmentAnchorForDataInst(_) => Self::ANCHOR_ALIGNMENT_CATEGORY,
        }
    }
}

impl<'a> Plan<'a> {
    /// Create a [`Plan`] with all of `root`'s dependencies, followed by `root` itself.
    //
    // FIXME(eddyb) consider renaming this and removing the `for_module` shorthand.
    pub fn for_root(
        cx: &'a Context,
        root: &'a (impl DynVisit<'a, Plan<'a>> + Print<Output = AttrsAndDef>),
    ) -> Self {
        let mut plan = Self {
            cx,
            current_module: None,
            per_version_name_and_node_defs: vec![(String::new(), FxHashMap::default())],
            use_counts: FxIndexMap::default(),
        };
        plan.use_node(Node::Root, root);
        plan
    }

    /// Create a [`Plan`] with all of `module`'s contents.
    ///
    /// Shorthand for `Plan::for_root(module.cx_ref(), module)`.
    pub fn for_module(module: &'a Module) -> Self {
        Self::for_root(module.cx_ref(), module)
    }

    /// Create a [`Plan`] that combines [`Plan::for_root`] from each version.
    ///
    /// Each version has a string, which should contain a descriptive name
    /// (e.g. the name of a pass that produced that version).
    ///
    /// While the roots (and their dependencies) can be entirely unrelated, the
    /// output won't be very useful in that case. For ideal results, most of the
    /// same entities (e.g. [`GlobalVar`] or [`Func`]) should be in most versions,
    /// with most of the changes being limited to within their definitions.
    pub fn for_versions(
        cx: &'a Context,
        versions: impl IntoIterator<
            Item = (
                impl Into<String>,
                &'a (impl DynVisit<'a, Plan<'a>> + Print<Output = AttrsAndDef> + 'a),
            ),
        >,
    ) -> Self {
        let mut plan = Self {
            cx,
            current_module: None,
            per_version_name_and_node_defs: vec![],
            use_counts: FxIndexMap::default(),
        };
        for (version_name, version_root) in versions {
            let mut combined_use_counts = mem::take(&mut plan.use_counts);
            plan.per_version_name_and_node_defs
                .push((version_name.into(), FxHashMap::default()));

            plan.use_node(Node::Root, version_root);

            // Merge use counts (from second version onward).
            if !combined_use_counts.is_empty() {
                for (use_kind, new_count) in plan.use_counts.drain(..) {
                    let count = combined_use_counts.entry(use_kind).or_default();
                    *count = new_count.max(*count);
                }
                plan.use_counts = combined_use_counts;
            }
        }

        // HACK(eddyb) avoid having `Node::Root` before any of its dependencies,
        // but without having to go through the non-trivial approach of properly
        // interleaving all the nodes, from each version, together.
        {
            let (map, k) = (&mut plan.use_counts, Use::Node(Node::Root));
            // FIXME(eddyb) this is effectively a "rotate" operation.
            map.shift_remove(&k).map(|v| map.insert(k, v));
        }

        plan
    }

    /// Add `interned` to the plan, after all of its dependencies.
    ///
    /// Only the first call recurses into the definition, subsequent calls only
    /// update its (internally tracked) "use count".
    fn use_interned(&mut self, interned: CxInterned) {
        let use_kind = Use::CxInterned(interned);
        if let Some(use_count) = self.use_counts.get_mut(&use_kind) {
            *use_count += 1;
            return;
        }

        match interned {
            CxInterned::AttrSet(attrs) => {
                self.visit_attr_set_def(&self.cx[attrs]);
            }
            CxInterned::Type(ty) => {
                self.visit_type_def(&self.cx[ty]);
            }
            CxInterned::Const(ct) => {
                self.visit_const_def(&self.cx[ct]);
            }
        }

        // Group all `CxInterned`s in a single top-level `Node`.
        self.use_node(Node::AllCxInterned, &AllCxInterned);

        *self.use_counts.entry(use_kind).or_default() += 1;
    }

    /// Add `node` to the plan, after all of its dependencies.
    ///
    /// Only the first call recurses into the definition, subsequent calls only
    /// update its (internally tracked) "use count".
    fn use_node(&mut self, node: Node, node_def: &'a dyn DynNodeDef<'a>) {
        if let Some(use_count) = self.use_counts.get_mut(&Use::Node(node)) {
            *use_count += 1;
            return;
        }

        let (_, node_defs) = self.per_version_name_and_node_defs.last_mut().unwrap();
        match node_defs.entry(node) {
            Entry::Occupied(entry) => {
                let dyn_data_ptr = |r| (r as *const dyn DynNodeDef<'_>).cast::<()>();
                assert!(
                    std::ptr::eq(dyn_data_ptr(*entry.get()), dyn_data_ptr(node_def)),
                    "print: same `{}` node has multiple distinct definitions in `Plan`",
                    node.category().unwrap_or_else(|s| s)
                );

                // Avoid infinite recursion for e.g. recursive functions.
                return;
            }
            Entry::Vacant(entry) => {
                entry.insert(node_def);
            }
        }

        node_def.dyn_visit_with(self);

        *self.use_counts.entry(Use::Node(node)).or_default() += 1;
    }
}

impl<'a> Visitor<'a> for Plan<'a> {
    fn visit_attr_set_use(&mut self, attrs: AttrSet) {
        self.use_interned(CxInterned::AttrSet(attrs));
    }
    fn visit_type_use(&mut self, ty: Type) {
        self.use_interned(CxInterned::Type(ty));
    }
    fn visit_const_use(&mut self, ct: Const) {
        self.use_interned(CxInterned::Const(ct));
    }
    fn visit_data_inst_form_use(&mut self, data_inst_form: DataInstForm) {
        // NOTE(eddyb) this contains no deduplication because each `DataInstDef`
        // will be pretty-printed separately, so everything in its `form` also
        // needs to get use counts incremented separately per-`DataInstDef`.
        self.visit_data_inst_form_def(&self.cx[data_inst_form]);
    }

    fn visit_global_var_use(&mut self, gv: GlobalVar) {
        if let Some(module) = self.current_module {
            self.use_node(Node::GlobalVar(gv), &module.global_vars[gv]);
        } else {
            // FIXME(eddyb) should this be a hard error?
        }
    }

    fn visit_func_use(&mut self, func: Func) {
        if let Some(module) = self.current_module {
            self.use_node(Node::Func(func), &module.funcs[func]);
        } else {
            // FIXME(eddyb) should this be a hard error?
        }
    }

    fn visit_module(&mut self, module: &'a Module) {
        assert!(
            std::ptr::eq(self.cx, &**module.cx_ref()),
            "print: `Plan::visit_module` does not support `Module`s from a \
             different `Context` than the one it was initially created with",
        );

        let old_module = self.current_module.replace(module);
        module.inner_visit_with(self);
        self.current_module = old_module;
    }
    fn visit_module_dialect(&mut self, dialect: &'a ModuleDialect) {
        self.use_node(Node::ModuleDialect, dialect);
    }
    fn visit_module_debug_info(&mut self, debug_info: &'a ModuleDebugInfo) {
        self.use_node(Node::ModuleDebugInfo, debug_info);
    }

    fn visit_attr(&mut self, attr: &'a Attr) {
        attr.inner_visit_with(self);

        // HACK(eddyb) the interpolated parts aren't visited by default
        // (as they're "inert data").
        if let Attr::Diagnostics(OrdAssertEq(diags)) = attr {
            for diag in diags {
                let Diag { level, message } = diag;
                match level {
                    DiagLevel::Bug(_) | DiagLevel::Error | DiagLevel::Warning => {}
                }
                message.inner_visit_with(self);
            }
        }
    }

    fn visit_func_decl(&mut self, func_decl: &'a FuncDecl) {
        if let DeclDef::Present(func_def_body) = &func_decl.def {
            if let Some(cfg) = &func_def_body.unstructured_cfg {
                for region in cfg.rev_post_order(func_def_body) {
                    if let Some(control_inst) = cfg.control_inst_on_exit_from.get(region) {
                        for &target in &control_inst.targets {
                            *self
                                .use_counts
                                .entry(Use::ControlRegionLabel(target))
                                .or_default() += 1;
                        }
                    }
                }
            }
        }

        func_decl.inner_visit_with(self);
    }
    fn visit_value_use(&mut self, v: &'a Value) {
        match *v {
            Value::Const(_) => {}
            _ => *self.use_counts.entry(Use::from(*v)).or_default() += 1,
        }
        v.inner_visit_with(self);
    }
}

impl<E: Visit, F: Visit> Visit for ExpectedVsFound<E, F> {
    fn visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        self.inner_visit_with(visitor);
    }
}

impl<E: Visit, F: Visit> InnerVisit for ExpectedVsFound<E, F> {
    fn inner_visit_with<'a>(&'a self, visitor: &mut impl Visitor<'a>) {
        let Self { expected, found } = self;

        expected.visit_with(visitor);
        found.visit_with(visitor);
    }
}

impl Visit for AllCxInterned {
    fn visit_with<'a>(&'a self, _visitor: &mut impl Visitor<'a>) {}
}

// FIXME(eddyb) make max line width configurable.
const MAX_LINE_WIDTH: usize = 100;

impl Plan<'_> {
    #[allow(rustdoc::private_intra_doc_links)]
    /// Print the whole [`Plan`] to a [`Versions<pretty::Fragment>`] and perform
    /// layout on its [`pretty::Fragment`]s.
    ///
    /// The resulting [`Versions<pretty::FragmentPostLayout>`] value supports
    /// [`fmt::Display`] for convenience, but also more specific methods
    /// (e.g. HTML output).
    pub fn pretty_print(&self) -> Versions<pretty::FragmentPostLayout> {
        self.print(&Printer::new(self))
            .map_pretty_fragments(|fragment| fragment.layout_with_max_line_width(MAX_LINE_WIDTH))
    }

    /// Like `pretty_print`, but separately pretty-printing "root dependencies"
    /// and the "root" itself (useful for nesting pretty-printed SPIR-T elsewhere).
    pub fn pretty_print_deps_and_root_separately(
        &self,
    ) -> (
        Versions<pretty::FragmentPostLayout>,
        Versions<pretty::FragmentPostLayout>,
    ) {
        let printer = Printer::new(self);
        (
            self.print_with_node_filter(&printer, |node| !matches!(node, Node::Root))
                .map_pretty_fragments(|fragment| {
                    fragment.layout_with_max_line_width(MAX_LINE_WIDTH)
                }),
            self.print_with_node_filter(&printer, |node| matches!(node, Node::Root))
                .map_pretty_fragments(|fragment| {
                    fragment.layout_with_max_line_width(MAX_LINE_WIDTH)
                }),
        )
    }
}

pub struct Printer<'a> {
    cx: &'a Context,
    use_styles: FxIndexMap<Use, UseStyle>,
}

/// How an [`Use`] of a definition should be printed.
#[derive(Copy, Clone)]
enum UseStyle {
    /// Refer to the definition by its category and an `idx` (e.g. `"type123"`).
    Anon {
        /// For intra-function [`Use`]s (i.e. [`Use::ControlRegionLabel`] and values),
        /// this disambiguates the parent function (for e.g. anchors).
        parent_func: Option<Func>,

        idx: usize,
    },

    /// Print the definition inline at the use site.
    Inline,
}

impl<'a> Printer<'a> {
    fn new(plan: &Plan<'a>) -> Self {
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

        let mut use_styles: FxIndexMap<_, _> = plan
            .use_counts
            .iter()
            .map(|(&use_kind, &use_count)| {
                // HACK(eddyb) these are assigned later.
                if let Use::ControlRegionLabel(_)
                | Use::ControlRegionInput { .. }
                | Use::ControlNodeOutput { .. }
                | Use::DataInstOutput(_) = use_kind
                {
                    return (use_kind, UseStyle::Inline);
                }

                // HACK(eddyb) these are "global" to the whole print `Plan`.
                if let Use::Node(
                    Node::Root | Node::AllCxInterned | Node::ModuleDialect | Node::ModuleDebugInfo,
                ) = use_kind
                {
                    return (
                        use_kind,
                        UseStyle::Anon {
                            parent_func: None,
                            idx: 0,
                        },
                    );
                }

                let inline = match use_kind {
                    Use::CxInterned(interned) => {
                        use_count == 1
                            || match interned {
                                CxInterned::AttrSet(attrs) => {
                                    let AttrSetDef { attrs } = &cx[attrs];
                                    attrs.len() <= 1
                                        || attrs.iter().any(|attr| {
                                            // HACK(eddyb) because of how these
                                            // are printed as comments outside
                                            // the `#{...}` syntax, they can't
                                            // work unless they're printed inline.
                                            matches!(
                                                attr,
                                                Attr::Diagnostics(_) | Attr::SpvDebugLine { .. }
                                            )
                                        })
                                }
                                CxInterned::Type(ty) => {
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

                                        TypeCtor::QPtr | TypeCtor::SpvStringLiteralForExtInst => {
                                            true
                                        }
                                    };

                                    ty_def.attrs == AttrSet::default()
                                        && (has_compact_print || ty_def.ctor_args.is_empty())
                                }
                                CxInterned::Const(ct) => {
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

                                    ct_def.attrs == AttrSet::default()
                                        && (has_compact_print || ct_def.ctor_args.is_empty())
                                }
                            }
                    }
                    Use::Node(_) => false,
                    Use::ControlRegionLabel(_)
                    | Use::ControlRegionInput { .. }
                    | Use::ControlNodeOutput { .. }
                    | Use::DataInstOutput(_)
                    | Use::AlignmentAnchorForControlRegion(_)
                    | Use::AlignmentAnchorForControlNode(_)
                    | Use::AlignmentAnchorForDataInst(_) => {
                        unreachable!()
                    }
                };
                let style = if inline {
                    UseStyle::Inline
                } else {
                    let ac = &mut anon_counters;
                    let counter = match use_kind {
                        Use::CxInterned(CxInterned::AttrSet(_)) => &mut ac.attr_sets,
                        Use::CxInterned(CxInterned::Type(_)) => &mut ac.types,
                        Use::CxInterned(CxInterned::Const(_)) => &mut ac.consts,
                        Use::Node(Node::GlobalVar(_)) => &mut ac.global_vars,
                        Use::Node(Node::Func(_)) => &mut ac.funcs,

                        Use::Node(
                            Node::Root
                            | Node::AllCxInterned
                            | Node::ModuleDialect
                            | Node::ModuleDebugInfo,
                        )
                        | Use::ControlRegionLabel(_)
                        | Use::ControlRegionInput { .. }
                        | Use::ControlNodeOutput { .. }
                        | Use::DataInstOutput(_)
                        | Use::AlignmentAnchorForControlRegion(_)
                        | Use::AlignmentAnchorForControlNode(_)
                        | Use::AlignmentAnchorForDataInst(_) => {
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

        let all_funcs = plan
            .use_counts
            .keys()
            .filter_map(|&use_kind| match use_kind {
                Use::Node(Node::Func(func)) => Some(func),
                _ => None,
            });
        for func in all_funcs {
            assert!(matches!(
                use_styles.get(&Use::Node(Node::Func(func))),
                Some(UseStyle::Anon { .. })
            ));

            let mut control_region_label_counter = 0;
            let mut value_counter = 0;
            let mut alignment_anchor_counter = 0;

            // Assign a new label/value/alignment-anchor index, but only if:
            // * the definition is actually used (except for alignment anchors)
            // * it doesn't already have an index (e.g. from a previous version)
            let mut define = |use_kind: Use| {
                let (counter, use_style_slot) = match use_kind {
                    Use::ControlRegionLabel(_) => (
                        &mut control_region_label_counter,
                        use_styles.get_mut(&use_kind),
                    ),

                    Use::ControlRegionInput { .. }
                    | Use::ControlNodeOutput { .. }
                    | Use::DataInstOutput(_) => (&mut value_counter, use_styles.get_mut(&use_kind)),

                    Use::AlignmentAnchorForControlRegion(_)
                    | Use::AlignmentAnchorForControlNode(_)
                    | Use::AlignmentAnchorForDataInst(_) => (
                        &mut alignment_anchor_counter,
                        Some(use_styles.entry(use_kind).or_insert(UseStyle::Inline)),
                    ),

                    _ => unreachable!(),
                };
                if let Some(use_style @ UseStyle::Inline) = use_style_slot {
                    let idx = *counter;
                    *counter += 1;
                    *use_style = UseStyle::Anon {
                        parent_func: Some(func),
                        idx,
                    };
                }
            };

            let func_def_bodies_across_versions = plan
                .per_version_name_and_node_defs
                .iter()
                .filter_map(|(_, node_defs)| {
                    match node_defs.get(&Node::Func(func))?.downcast_as_func_decl()? {
                        FuncDecl {
                            def: DeclDef::Present(func_def_body),
                            ..
                        } => Some(func_def_body),

                        _ => None,
                    }
                });

            for func_def_body in func_def_bodies_across_versions {
                let visit_region = |func_at_region: FuncAt<'_, ControlRegion>| {
                    let region = func_at_region.position;

                    define(Use::AlignmentAnchorForControlRegion(region));
                    define(Use::ControlRegionLabel(region));

                    let ControlRegionDef {
                        inputs,
                        children,
                        outputs: _,
                    } = func_def_body.at(region).def();

                    for (i, _) in inputs.iter().enumerate() {
                        define(Use::ControlRegionInput {
                            region,
                            input_idx: i.try_into().unwrap(),
                        });
                    }

                    for func_at_control_node in func_def_body.at(*children) {
                        let control_node = func_at_control_node.position;

                        define(Use::AlignmentAnchorForControlNode(control_node));

                        let ControlNodeDef { kind, outputs } = func_at_control_node.def();

                        if let ControlNodeKind::Block { insts } = *kind {
                            for func_at_inst in func_def_body.at(insts) {
                                define(Use::AlignmentAnchorForDataInst(func_at_inst.position));
                                if cx[func_at_inst.def().form].output_type.is_some() {
                                    define(Use::DataInstOutput(func_at_inst.position));
                                }
                            }
                        }

                        for (i, _) in outputs.iter().enumerate() {
                            define(Use::ControlNodeOutput {
                                control_node,
                                output_idx: i.try_into().unwrap(),
                            });
                        }
                    }
                };

                // FIXME(eddyb) maybe this should be provided by `visit`.
                struct VisitAllRegions<F>(F);
                impl<'a, F: FnMut(FuncAt<'a, ControlRegion>)> Visitor<'a> for VisitAllRegions<F> {
                    // FIXME(eddyb) this is excessive, maybe different kinds of
                    // visitors should exist for module-level and func-level?
                    fn visit_attr_set_use(&mut self, _: AttrSet) {}
                    fn visit_type_use(&mut self, _: Type) {}
                    fn visit_const_use(&mut self, _: Const) {}
                    fn visit_data_inst_form_use(&mut self, _: DataInstForm) {}
                    fn visit_global_var_use(&mut self, _: GlobalVar) {}
                    fn visit_func_use(&mut self, _: Func) {}

                    fn visit_control_region_def(
                        &mut self,
                        func_at_control_region: FuncAt<'a, ControlRegion>,
                    ) {
                        self.0(func_at_control_region);
                        func_at_control_region.inner_visit_with(self);
                    }
                }
                func_def_body.inner_visit_with(&mut VisitAllRegions(visit_region));
            }
        }

        Self { cx, use_styles }
    }

    pub fn cx(&self) -> &'a Context {
        self.cx
    }
}

// Styles for a variety of syntactic categories.
// FIXME(eddyb) this is a somewhat inefficient way of declaring these.
//
// NOTE(eddyb) these methods take `self` so they can become configurable in the future.
#[allow(clippy::unused_self)]
impl Printer<'_> {
    fn error_style(&self) -> pretty::Styles {
        pretty::Styles::color(pretty::palettes::simple::MAGENTA)
    }
    fn comment_style(&self) -> pretty::Styles {
        pretty::Styles {
            color_opacity: Some(0.3),
            size: Some(-4),
            // FIXME(eddyb) this looks wrong for some reason?
            // subscript: true,
            ..pretty::Styles::color(pretty::palettes::simple::DARK_GRAY)
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
        pretty::Styles {
            thickness: Some(2),
            ..pretty::Styles::color(pretty::palettes::simple::MAGENTA)
        }
    }
    fn spv_base_style(&self) -> pretty::Styles {
        pretty::Styles::color(pretty::palettes::simple::ORANGE)
    }
    fn spv_op_style(&self) -> pretty::Styles {
        pretty::Styles {
            thickness: Some(3),
            ..self.spv_base_style()
        }
    }
    fn spv_enumerand_name_style(&self) -> pretty::Styles {
        pretty::Styles::color(pretty::palettes::simple::CYAN)
    }
    fn attr_style(&self) -> pretty::Styles {
        pretty::Styles {
            color: Some(pretty::palettes::simple::GREEN),
            color_opacity: Some(0.6),
            thickness: Some(-2),
            ..Default::default()
        }
    }

    /// Compute a suitable style for an unintrusive `foo.` "namespace prefix",
    /// from a more typical style (by shrinking and/or reducing visibility).
    fn demote_style_for_namespace_prefix(&self, mut style: pretty::Styles) -> pretty::Styles {
        // NOTE(eddyb) this was `opacity: Some(0.4)` + `thickness: Some(-3)`,
        // but thinner text ended up being more annoying to read while still
        // using up too much real-estate (compared to decreasing the size).
        style.color_opacity = Some(style.color_opacity.unwrap_or(1.0) * 0.6);
        // FIXME(eddyb) maybe this could be more uniform with a different unit.
        style.size = Some(style.size.map_or(-4, |size| size - 1));
        style
    }
}

impl<'a> Printer<'a> {
    /// Pretty-print a `: T` style "type ascription" suffix.
    ///
    /// This should be used everywhere some type ascription notation is needed,
    /// to ensure consistency across all such situations.
    fn pretty_type_ascription_suffix(&self, ty: Type) -> pretty::Fragment {
        pretty::join_space(":", [ty.print(self)])
    }

    /// Pretty-print a SPIR-V `opcode`'s name, prefixed by `"spv."`.
    fn pretty_spv_opcode(
        &self,
        opcode_name_style: pretty::Styles,
        opcode: spv::spec::Opcode,
    ) -> pretty::Fragment {
        pretty::Fragment::new([
            self.demote_style_for_namespace_prefix(self.spv_base_style())
                .apply("spv."),
            opcode_name_style.apply(opcode.name()),
        ])
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
                    spv::print::Token::Error(s) => self.error_style().apply(s).into(),
                    spv::print::Token::Punctuation(s) => s.into(),
                    spv::print::Token::OperandKindNamespacePrefix(s) => {
                        pretty::Fragment::new([
                            // HACK(eddyb) double-demote to end up with `spv.A.B`,
                            // with increasing size from `spv.` to `A.` to `B`.
                            self.demote_style_for_namespace_prefix(
                                self.demote_style_for_namespace_prefix(self.spv_base_style()),
                            )
                            .apply("spv."),
                            // FIXME(eddyb) avoid the cost of allocating here.
                            self.demote_style_for_namespace_prefix(
                                self.declarative_keyword_style(),
                            )
                            .apply(format!("{s}.")),
                        ])
                    }
                    spv::print::Token::EnumerandName(s) => {
                        self.spv_enumerand_name_style().apply(s).into()
                    }
                    spv::print::Token::NumericLiteral(s) => {
                        self.numeric_literal_style().apply(s).into()
                    }
                    spv::print::Token::StringLiteral(s) => {
                        self.string_literal_style().apply(s).into()
                    }
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
    /// [`Print::print`] method, instead of a closure, as `print_id`).
    ///
    /// Immediate operands are wrapped in angle brackets, while `ID` operands are
    /// wrapped in parentheses, e.g.: `spv.OpFoo<Bar, 123, "baz">(v1, v2)`.
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
        // e.g: `spv.OpFoo<Bar(/* #0 */)>(/* #0 */ v123)`.
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
                                spv::print::Token::Error(s) => self.error_style().apply(s).into(),
                                spv::print::Token::Punctuation(s) => s.into(),
                                spv::print::Token::OperandKindNamespacePrefix(s) => {
                                    pretty::Fragment::new([
                                        // HACK(eddyb) double-demote to end up with `spv.A.B`,
                                        // with increasing size from `spv.` to `A.` to `B`.
                                        self.demote_style_for_namespace_prefix(
                                            self.demote_style_for_namespace_prefix(
                                                self.spv_base_style(),
                                            ),
                                        )
                                        .apply("spv."),
                                        // FIXME(eddyb) avoid the cost of allocating here.
                                        self.demote_style_for_namespace_prefix(
                                            self.declarative_keyword_style(),
                                        )
                                        .apply(format!("{s}.")),
                                    ])
                                }
                                spv::print::Token::EnumerandName(s) => {
                                    self.spv_enumerand_name_style().apply(s).into()
                                }
                                spv::print::Token::NumericLiteral(s) => {
                                    self.numeric_literal_style().apply(s).into()
                                }
                                spv::print::Token::StringLiteral(s) => {
                                    self.string_literal_style().apply(s).into()
                                }
                                spv::print::Token::Id(id) => {
                                    let comment = self
                                        .comment_style()
                                        .apply(format!("/* #{next_extra_idx} */"));
                                    next_extra_idx += 1;

                                    let id = print_id(id, self).into().unwrap_or_else(|| {
                                        self.comment_style().apply("/* implicit ID */").into()
                                    });
                                    paren_operands.push(pretty::join_space(comment.clone(), [id]));

                                    comment.into()
                                }
                            },
                        )))
                    }
                })
                .peekable();

        // Put together all the pieces, angle-bracketed operands then parenthesized
        // ones, e.g.: `spv.OpFoo<Bar, 123, "baz">(v1, v2)` (with either group optional).
        let mut out = self.pretty_spv_opcode(spv_inst_name_style, opcode);

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

impl AttrsAndDef {
    /// Concat `attrs`, `name` and `def_without_name` into a [`pretty::Fragment`],
    /// effectively "filling in" the `name` missing from `def_without_name`.
    ///
    /// If `name` starts with an anchor definition, the definition of that anchor
    /// gets hoised to before (some non-empty) `attrs`, so that navigating to that
    /// anchor doesn't "hide" those attributes (requiring scrolling to see them).
    fn insert_name_before_def(self, name: impl Into<pretty::Fragment>) -> pretty::Fragment {
        let Self {
            attrs,
            def_without_name,
        } = self;

        let mut maybe_hoisted_anchor = pretty::Fragment::default();
        let mut maybe_def_start_anchor = pretty::Fragment::default();
        let mut maybe_def_end_anchor = pretty::Fragment::default();
        let mut name = name.into();
        if let [pretty::Node::StyledText(name_start_styles_and_text), ..] = &mut name.nodes[..] {
            let name_start_styles = &mut name_start_styles_and_text.0;
            if name_start_styles.anchor_is_def {
                let anchor = name_start_styles.anchor.as_ref().unwrap();
                if !attrs.nodes.is_empty() {
                    name_start_styles.anchor_is_def = false;
                    maybe_hoisted_anchor = pretty::Styles {
                        anchor: Some(anchor.clone()),
                        anchor_is_def: true,
                        ..Default::default()
                    }
                    .apply("")
                    .into();
                }

                // HACK(eddyb) add a pair of anchors "bracketing" the definition
                // (though see below for why only the "start" side is currently
                // in use), to help with `multiversion` alignment, as long as
                // there's no alignment anchor already starting the definition.
                let has_alignment_anchor = match &def_without_name.nodes[..] {
                    [pretty::Node::StyledText(def_start_styles_and_text), ..] => {
                        let (def_start_styles, def_start_text) = &**def_start_styles_and_text;
                        def_start_text == ""
                            && def_start_styles.anchor_is_def
                            && def_start_styles
                                .anchor
                                .as_ref()
                                .unwrap()
                                .contains(Use::ANCHOR_ALIGNMENT_CATEGORY)
                    }
                    _ => false,
                };
                let mk_anchor_def = |suffix| {
                    pretty::Styles {
                        anchor: Some(format!("{anchor}.{suffix}")),
                        anchor_is_def: true,
                        ..Default::default()
                    }
                    .apply("")
                    .into()
                };
                if !has_alignment_anchor {
                    maybe_def_start_anchor = mk_anchor_def("start");
                    // FIXME(eddyb) having end alignment may be useful, but the
                    // current logic in `multiversion` would prefer aligning
                    // the ends, to the detriment of the rest (causing huge gaps).
                    if false {
                        maybe_def_end_anchor = mk_anchor_def("end");
                    }
                }
            }
        }
        pretty::Fragment::new([
            maybe_hoisted_anchor,
            attrs,
            name,
            maybe_def_start_anchor,
            def_without_name,
            maybe_def_end_anchor,
        ])
    }
}

pub trait Print {
    type Output;
    fn print(&self, printer: &Printer<'_>) -> Self::Output;

    // HACK(eddyb) this is only ever implemented by `FuncDecl`, to allow for
    // `Printer::new` to compute its per-function indices. A better replacement
    // could eventually be `fn setup_printer(&self, printer: &mut Printer)`.
    fn downcast_as_func_decl(&self) -> Option<&FuncDecl> {
        None
    }
}

impl<E: Print<Output = pretty::Fragment>, F: Print<Output = pretty::Fragment>> Print
    for ExpectedVsFound<E, F>
{
    type Output = AttrsAndDef;
    fn print(&self, printer: &Printer<'_>) -> AttrsAndDef {
        let Self { expected, found } = self;

        AttrsAndDef {
            attrs: pretty::Fragment::default(),
            def_without_name: pretty::Fragment::new([
                "expected: ".into(),
                expected.print(printer),
                pretty::Node::ForceLineSeparation.into(),
                "found: ".into(),
                found.print(printer),
            ]),
        }
    }
}

impl Use {
    /// Common implementation for [`Use::print`] and [`Use::print_as_def`].
    fn print_as_ref_or_def(&self, printer: &Printer<'_>, is_def: bool) -> pretty::Fragment {
        let style = printer
            .use_styles
            .get(self)
            .copied()
            .unwrap_or(UseStyle::Inline);
        match style {
            UseStyle::Anon { parent_func, idx } => {
                // HACK(eddyb) these are "global" to the whole print `Plan`.
                let name = if let Use::Node(Node::ModuleDialect | Node::ModuleDebugInfo) = self {
                    assert_eq!(idx, 0);
                    self.category().into()
                } else {
                    format!("{}{}", self.category(), idx)
                };

                let anchor = if let Some(func) = parent_func {
                    // Disambiguate intra-function anchors (labels/values) by
                    // prepending a prefix of the form `func123_`.
                    let func = Use::Node(Node::Func(func));
                    let func_category = func.category();
                    let func_idx = match printer.use_styles[&func] {
                        UseStyle::Anon { idx, .. } => idx,
                        UseStyle::Inline => unreachable!(),
                    };
                    format!("{func_category}{func_idx}.{name}")
                } else {
                    // FIXME(eddyb) avoid having to clone `String`s here.
                    name.clone()
                };
                let (name, name_style) = match self {
                    Self::CxInterned(CxInterned::AttrSet(_)) => {
                        (format!("#{name}"), printer.attr_style())
                    }

                    Self::AlignmentAnchorForControlRegion(_)
                    | Self::AlignmentAnchorForControlNode(_)
                    | Self::AlignmentAnchorForDataInst(_) => ("".to_string(), Default::default()),

                    _ => (name, Default::default()),
                };
                let name = pretty::Styles {
                    anchor: Some(anchor),
                    anchor_is_def: is_def,
                    ..name_style
                }
                .apply(name);
                match self {
                    Self::CxInterned(CxInterned::AttrSet(_)) => {
                        // HACK(eddyb) separate `AttrSet` uses from their target.
                        pretty::Fragment::new([name, pretty::Node::ForceLineSeparation])
                    }
                    _ => name.into(),
                }
            }
            UseStyle::Inline => match *self {
                Self::CxInterned(interned) => interned
                    .print(printer)
                    .insert_name_before_def(pretty::Fragment::default()),
                Self::Node(node) => printer
                    .error_style()
                    .apply(format!(
                        "/* undefined {} */_",
                        node.category().unwrap_or_else(|s| s)
                    ))
                    .into(),
                Self::ControlRegionLabel(_)
                | Self::ControlRegionInput { .. }
                | Self::ControlNodeOutput { .. }
                | Self::DataInstOutput(_) => "_".into(),

                Self::AlignmentAnchorForControlRegion(_)
                | Self::AlignmentAnchorForControlNode(_)
                | Self::AlignmentAnchorForDataInst(_) => unreachable!(),
            },
        }
    }

    fn print_as_def(&self, printer: &Printer<'_>) -> pretty::Fragment {
        self.print_as_ref_or_def(printer, true)
    }
}

impl Print for Use {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_>) -> pretty::Fragment {
        self.print_as_ref_or_def(printer, false)
    }
}

// Interned/module-stored nodes dispatch through the `Use` impl above.
impl Print for AttrSet {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_>) -> pretty::Fragment {
        Use::CxInterned(CxInterned::AttrSet(*self)).print(printer)
    }
}
impl Print for Type {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_>) -> pretty::Fragment {
        Use::CxInterned(CxInterned::Type(*self)).print(printer)
    }
}
impl Print for Const {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_>) -> pretty::Fragment {
        Use::CxInterned(CxInterned::Const(*self)).print(printer)
    }
}
impl Print for GlobalVar {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_>) -> pretty::Fragment {
        Use::Node(Node::GlobalVar(*self)).print(printer)
    }
}
impl Print for Func {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_>) -> pretty::Fragment {
        Use::Node(Node::Func(*self)).print(printer)
    }
}

// NOTE(eddyb) the `Print` impl for `Node` is for the top-level definition,
// *not* any uses (which go through the `Print` impls above).

impl Print for Plan<'_> {
    type Output = Versions<pretty::Fragment>;
    fn print(&self, printer: &Printer<'_>) -> Versions<pretty::Fragment> {
        self.print_with_node_filter(printer, |_| true)
    }
}

impl Plan<'_> {
    fn print_with_node_filter(
        &self,
        printer: &Printer<'_>,
        filter: impl Fn(&Node) -> bool,
    ) -> Versions<pretty::Fragment> {
        let num_versions = self.per_version_name_and_node_defs.len();
        let per_node_versions_with_repeat_count = printer
            .use_styles
            .keys()
            .filter_map(|&use_kind| match use_kind {
                Use::Node(node) => Some(node),
                _ => None,
            })
            .filter(filter)
            .map(|node| -> SmallVec<[_; 1]> {
                if num_versions == 0 {
                    return [].into_iter().collect();
                }

                let name = if node.category().is_err() {
                    pretty::Fragment::default()
                } else {
                    Use::Node(node).print_as_def(printer)
                };

                // Avoid printing `AllCxInterned` more than once, it doesn't
                // really have per-version node definitions in the first place.
                if let Node::AllCxInterned = node {
                    // FIXME(eddyb) maybe make `DynNodeDef` `Any`-like, to be
                    // able to assert that all per-version defs are identical.
                    return [(
                        AllCxInterned.print(printer).insert_name_before_def(name),
                        num_versions,
                    )]
                    .into_iter()
                    .collect();
                }

                self.per_version_name_and_node_defs
                    .iter()
                    .map(move |(_, node_defs)| {
                        node_defs
                            .get(&node)
                            .map(|def| def.print(printer).insert_name_before_def(name.clone()))
                            .unwrap_or_default()
                    })
                    .dedup_with_count()
                    .map(|(repeat_count, fragment)| {
                        // FIXME(eddyb) consider rewriting intra-func anchors
                        // here, post-deduplication, to be unique per-version.
                        // Additionally, a diff algorithm could be employed, to
                        // annotate the changes between versions.

                        (fragment, repeat_count)
                    })
                    .collect()
            });

        // Unversioned, flatten the nodes.
        if num_versions == 1 && self.per_version_name_and_node_defs[0].0.is_empty() {
            Versions::Single(pretty::Fragment::new(
                per_node_versions_with_repeat_count
                    .map(|mut versions_with_repeat_count| {
                        versions_with_repeat_count.pop().unwrap().0
                    })
                    .filter(|fragment| !fragment.nodes.is_empty())
                    .intersperse({
                        // Separate top-level definitions with empty lines.
                        // FIXME(eddyb) have an explicit `pretty::Node`
                        // for "vertical gap" instead.
                        "\n\n".into()
                    }),
            ))
        } else {
            Versions::Multiple {
                version_names: self
                    .per_version_name_and_node_defs
                    .iter()
                    .map(|(name, _)| name.clone())
                    .collect(),
                per_row_versions_with_repeat_count: per_node_versions_with_repeat_count.collect(),
            }
        }
    }
}

impl Print for Module {
    type Output = AttrsAndDef;
    fn print(&self, printer: &Printer<'_>) -> AttrsAndDef {
        if self.exports.is_empty() {
            return AttrsAndDef::default();
        }

        let exports = pretty::Fragment::new([
            printer.declarative_keyword_style().apply("export").into(),
            " ".into(),
            pretty::join_comma_sep(
                "{",
                self.exports
                    .iter()
                    .map(|(export_key, exportee)| {
                        pretty::Fragment::new([
                            export_key.print(printer),
                            ": ".into(),
                            exportee.print(printer),
                        ])
                    })
                    .map(|entry| {
                        pretty::Fragment::new([pretty::Node::ForceLineSeparation.into(), entry])
                    }),
                "}",
            ),
        ]);

        AttrsAndDef {
            attrs: pretty::Fragment::default(),
            def_without_name: exports,
        }
    }
}

impl Print for ModuleDialect {
    type Output = AttrsAndDef;
    fn print(&self, printer: &Printer<'_>) -> AttrsAndDef {
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
                                .apply(format!("{version_major}.{version_minor}")),
                        ]),
                        pretty::join_comma_sep(
                            "extensions: {",
                            extensions.iter().map(|ext| {
                                printer.string_literal_style().apply(format!("{ext:?}"))
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

        AttrsAndDef {
            attrs: pretty::Fragment::default(),
            def_without_name: pretty::Fragment::new([" = ".into(), dialect]),
        }
    }
}

impl Print for ModuleDebugInfo {
    type Output = AttrsAndDef;
    fn print(&self, printer: &Printer<'_>) -> AttrsAndDef {
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
                                        printer.numeric_literal_style().apply(format!("{tool_id}")),
                                        ", version: ".into(),
                                        printer
                                            .numeric_literal_style()
                                            .apply(format!("{tool_version}")),
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
                                                    pretty::Fragment::new([
                                                        printer.string_literal_style().apply(
                                                            format!("{:?}", &printer.cx[file]),
                                                        ),
                                                        ": ".into(),
                                                        printer
                                                            .string_literal_style()
                                                            .apply(format!("{contents:?}")),
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
                        pretty::join_comma_sep(
                            "source_extensions: [",
                            source_extensions.iter().map(|ext| {
                                printer.string_literal_style().apply(format!("{ext:?}"))
                            }),
                            "]",
                        ),
                        pretty::join_comma_sep(
                            "module_processes: [",
                            module_processes.iter().map(|proc| {
                                printer.string_literal_style().apply(format!("{proc:?}"))
                            }),
                            "]",
                        ),
                    ]
                    .into_iter()
                    .map(|entry| {
                        pretty::Fragment::new([pretty::Node::ForceLineSeparation.into(), entry])
                    }),
                    "}",
                )
            }
        };

        AttrsAndDef {
            attrs: pretty::Fragment::default(),
            def_without_name: pretty::Fragment::new([" = ".into(), debug_info]),
        }
    }
}

impl Print for ExportKey {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_>) -> pretty::Fragment {
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
                    printer.spv_op_style(),
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
    fn print(&self, printer: &Printer<'_>) -> pretty::Fragment {
        match *self {
            Self::GlobalVar(gv) => gv.print(printer),
            Self::Func(func) => func.print(printer),
        }
    }
}

impl Print for AllCxInterned {
    type Output = AttrsAndDef;
    fn print(&self, printer: &Printer<'_>) -> AttrsAndDef {
        let fragments = printer
            .use_styles
            .iter()
            .filter_map(|(&use_kind, &use_style)| match (use_kind, use_style) {
                (
                    Use::CxInterned(interned),
                    UseStyle::Anon {
                        parent_func: _,
                        idx,
                    },
                ) => Some((interned, idx)),
                _ => None,
            })
            .map(|(interned, anon_idx)| {
                let name = format!("{}{}", interned.category(), anon_idx);
                let name = pretty::Styles {
                    // FIXME(eddyb) avoid having to clone `String`s here.
                    anchor: Some(name.clone()),
                    anchor_is_def: true,
                    ..Default::default()
                }
                .apply(name);

                interned
                    .print(printer)
                    .insert_name_before_def(pretty::Fragment::new([name, " = ".into()]))
            })
            .intersperse({
                // Separate top-level definitions with empty lines.
                // FIXME(eddyb) have an explicit `pretty::Node`
                // for "vertical gap" instead.
                "\n\n".into()
            });

        AttrsAndDef {
            attrs: pretty::Fragment::default(),
            def_without_name: pretty::Fragment::new(fragments),
        }
    }
}

impl Print for CxInterned {
    type Output = AttrsAndDef;
    fn print(&self, printer: &Printer<'_>) -> AttrsAndDef {
        match *self {
            Self::AttrSet(attrs) => AttrsAndDef {
                attrs: pretty::Fragment::default(),
                def_without_name: printer.cx[attrs].print(printer),
            },
            Self::Type(ty) => printer.cx[ty].print(printer),
            Self::Const(ct) => printer.cx[ct].print(printer),
        }
    }
}

impl Print for AttrSetDef {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_>) -> pretty::Fragment {
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
    fn print(&self, printer: &Printer<'_>) -> (AttrStyle, pretty::Fragment) {
        match self {
            Attr::Diagnostics(diags) => (
                AttrStyle::Comment,
                pretty::Fragment::new(
                    diags
                        .0
                        .iter()
                        .map(|diag| {
                            let Diag { level, message } = diag;

                            // FIXME(eddyb) the plan was to use 💥/⮿/⚠
                            // for bug/error/warning, but it doesn't really
                            // render correctly, so allcaps it is for now.
                            let (icon, icon_color) = match level {
                                DiagLevel::Bug(_) => ("BUG", pretty::palettes::simple::MAGENTA),
                                DiagLevel::Error => ("ERR", pretty::palettes::simple::RED),
                                DiagLevel::Warning => ("WARN", pretty::palettes::simple::YELLOW),
                            };

                            let grayish =
                                |[r, g, b]: [u8; 3]| [(r / 2) + 64, (g / 2) + 64, (b / 2) + 64];
                            let comment_style = pretty::Styles::color(grayish(icon_color));

                            // FIXME(eddyb) maybe make this a link to the source code?
                            let bug_location_prefix = match level {
                                DiagLevel::Bug(location) => {
                                    let location = location.to_string();
                                    let location = match location.rsplit_once("/src/") {
                                        Some((_path_prefix, intra_src)) => intra_src,
                                        None => &location,
                                    };
                                    comment_style.clone().apply(format!("[{location}] ")).into()
                                }
                                DiagLevel::Error | DiagLevel::Warning => {
                                    pretty::Fragment::default()
                                }
                            };

                            let mut printed_message = message
                                .print(printer)
                                .insert_name_before_def(pretty::Fragment::default());

                            // HACK(eddyb) apply the right style to all the plain
                            // text parts of the already-printed message.
                            for node in &mut printed_message.nodes {
                                if let pretty::Node::Text(text) = node {
                                    *node = comment_style.clone().apply(mem::take(text));
                                }
                            }

                            // HACK(eddyb) this would ideally use line comments,
                            // but adding the line prefix properly to everything
                            // is a bit of a pain without special `pretty` support.
                            pretty::Fragment::new([
                                comment_style.clone().apply("/*"),
                                pretty::Node::BreakingOnlySpace,
                                pretty::Node::InlineOrIndentedBlock(vec![pretty::Fragment::new([
                                    pretty::Styles {
                                        thickness: Some(3),

                                        // HACK(eddyb) this allows larger "icons"
                                        // without adding gaps via `line-height`.
                                        subscript: true,
                                        size: Some(2),

                                        ..pretty::Styles::color(icon_color)
                                    }
                                    .apply(icon)
                                    .into(),
                                    " ".into(),
                                    bug_location_prefix,
                                    printed_message,
                                ])]),
                                pretty::Node::BreakingOnlySpace,
                                comment_style.apply("*/"),
                            ])
                        })
                        .intersperse(pretty::Node::ForceLineSeparation.into()),
                ),
            ),

            Attr::QPtr(attr) => {
                let (name, params_inputs) = match attr {
                    QPtrAttr::ToSpvPtrInput { input_idx, pointee } => (
                        "to_spv_ptr_input",
                        pretty::Fragment::new([
                            // FIXME(eddyb) is using angle brackets like this consistent styling?
                            pretty::join_comma_sep(
                                "<",
                                [printer
                                    .numeric_literal_style()
                                    .apply(format!("{input_idx}"))],
                                ">",
                            ),
                            pretty::join_comma_sep("(", [pointee.0.print(printer)], ")"),
                        ]),
                    ),

                    QPtrAttr::FromSpvPtrOutput {
                        addr_space,
                        pointee,
                    } => (
                        "from_spv_ptr_output",
                        pretty::Fragment::new([
                            // FIXME(eddyb) is using angle brackets like this consistent styling?
                            pretty::join_comma_sep("<", [addr_space.0.print(printer)], ">"),
                            pretty::join_comma_sep("(", [pointee.0.print(printer)], ")"),
                        ]),
                    ),

                    QPtrAttr::Usage(usage) => (
                        "usage",
                        pretty::join_comma_sep("(", [usage.0.print(printer)], ")"),
                    ),
                };
                (
                    AttrStyle::NonComment,
                    pretty::Fragment::new([
                        printer
                            .demote_style_for_namespace_prefix(printer.attr_style())
                            .apply("qptr.")
                            .into(),
                        printer.attr_style().apply(name).into(),
                        params_inputs,
                    ]),
                )
            }

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
                    format!("// at {file_path}:{line}:{col}")
                } else {
                    format!("// at {file_path:?}:{line}:{col}")
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

impl Print for Vec<DiagMsgPart> {
    // HACK(eddyb) this is only `AttrsAndDef` so it can be pretty-printed as a
    // root - but ideally `DynNodeDef` should allow `pretty::Fragment` too.
    type Output = AttrsAndDef;

    fn print(&self, printer: &Printer<'_>) -> AttrsAndDef {
        let msg = pretty::Fragment::new(self.iter().map(|part| match part {
            DiagMsgPart::Plain(text) => pretty::Node::Text(text.clone()).into(),
            DiagMsgPart::Attrs(attrs) => attrs.print(printer),
            DiagMsgPart::Type(ty) => ty.print(printer),
            DiagMsgPart::Const(ct) => ct.print(printer),
            DiagMsgPart::QPtrUsage(usage) => usage.print(printer),
        }));
        AttrsAndDef {
            attrs: pretty::Fragment::default(),
            def_without_name: msg,
        }
    }
}

impl Print for QPtrUsage {
    type Output = pretty::Fragment;

    fn print(&self, printer: &Printer<'_>) -> pretty::Fragment {
        match self {
            QPtrUsage::Handles(qptr::shapes::Handle::Opaque(ty)) => ty.print(printer),
            QPtrUsage::Handles(qptr::shapes::Handle::Buffer(_, data_usage)) => {
                pretty::Fragment::new([
                    printer
                        .declarative_keyword_style()
                        .apply("buffer_data")
                        .into(),
                    pretty::join_comma_sep("(", [data_usage.print(printer)], ")"),
                ])
            }
            QPtrUsage::Memory(usage) => usage.print(printer),
        }
    }
}

impl Print for QPtrMemUsage {
    type Output = pretty::Fragment;

    fn print(&self, printer: &Printer<'_>) -> pretty::Fragment {
        // FIXME(eddyb) should this be a helper on `Printer`?
        let num_lit = |x: u32| printer.numeric_literal_style().apply(format!("{x}")).into();

        match &self.kind {
            QPtrMemUsageKind::Unused => "_".into(),
            // FIXME(eddyb) should the distinction be noted?
            &QPtrMemUsageKind::StrictlyTyped(ty) | &QPtrMemUsageKind::DirectAccess(ty) => {
                ty.print(printer)
            }
            QPtrMemUsageKind::OffsetBase(entries) => pretty::join_comma_sep(
                "{",
                entries
                    .iter()
                    .map(|(&offset, sub_usage)| {
                        pretty::Fragment::new([
                            num_lit(offset),
                            "..".into(),
                            sub_usage
                                .max_size
                                .and_then(|max_size| offset.checked_add(max_size))
                                .map(num_lit)
                                .unwrap_or_default(),
                            " => ".into(),
                            sub_usage.print(printer),
                        ])
                    })
                    .map(|entry| {
                        pretty::Fragment::new([pretty::Node::ForceLineSeparation.into(), entry])
                    }),
                "}",
            ),
            QPtrMemUsageKind::DynOffsetBase { element, stride } => pretty::Fragment::new([
                "(".into(),
                num_lit(0),
                "..".into(),
                self.max_size
                    .map(|max_size| max_size / stride.get())
                    .map(num_lit)
                    .unwrap_or_default(),
                ") × ".into(),
                num_lit(stride.get()),
                " => ".into(),
                element.print(printer),
            ]),
        }
    }
}

impl Print for TypeDef {
    type Output = AttrsAndDef;
    fn print(&self, printer: &Printer<'_>) -> AttrsAndDef {
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
                    kw(format!("s{width}"))
                } else {
                    kw(format!("u{width}"))
                })
            } else if opcode == wk.OpTypeFloat {
                let width = match imms[..] {
                    [spv::Imm::Short(_, width)] => width,
                    _ => unreachable!(),
                };

                Some(kw(format!("f{width}")))
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
                        .apply(format!("{elem_count}"))
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
            def_without_name: if let Some(def) = compact_def {
                def
            } else {
                match *ctor {
                    // FIXME(eddyb) should this be shortened to `qtr`?
                    TypeCtor::QPtr => printer.declarative_keyword_style().apply("qptr").into(),

                    TypeCtor::SpvInst(spv::Inst { opcode, ref imms }) => printer.pretty_spv_inst(
                        printer.spv_op_style(),
                        opcode,
                        imms,
                        ctor_args,
                        |&arg, printer| match arg {
                            TypeCtorArg::Type(ty) => ty.print(printer),
                            TypeCtorArg::Const(ct) => ct.print(printer),
                        },
                        None,
                    ),
                    TypeCtor::SpvStringLiteralForExtInst => pretty::Fragment::new([
                        printer.error_style().apply("type_of").into(),
                        "(".into(),
                        printer.pretty_spv_opcode(printer.spv_op_style(), wk.OpString),
                        ")".into(),
                    ]),
                }
            },
        }
    }
}

impl Print for ConstDef {
    type Output = AttrsAndDef;
    fn print(&self, printer: &Printer<'_>) -> AttrsAndDef {
        let Self {
            attrs,
            ty,
            ctor,
            ctor_args,
        } = self;

        let wk = &spv::spec::Spec::get().well_known;

        let kw = |kw| printer.declarative_keyword_style().apply(kw).into();
        let literal_ty_suffix = |ty| {
            pretty::Styles {
                // HACK(eddyb) the exact type detracts from the value.
                color_opacity: Some(0.4),
                subscript: true,
                ..printer.declarative_keyword_style()
            }
            .apply(ty)
        };
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
                            let (printed_value, ty) = if signed {
                                let sext_raw_bits =
                                    (raw_bits as u128 as i128) << (128 - width) >> (128 - width);
                                (format!("{sext_raw_bits}"), format!("s{width}"))
                            } else {
                                (format!("{raw_bits}"), format!("u{width}"))
                            };
                            Some(pretty::Fragment::new([
                                printer.numeric_literal_style().apply(printed_value),
                                literal_ty_suffix(ty),
                            ]))
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
                            Some(format!("{float:?}")).filter(|s| {
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
                            pretty::Fragment::new([
                                printer.numeric_literal_style().apply(s),
                                literal_ty_suffix(format!("f{width}")),
                            ])
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
            def_without_name: compact_def.unwrap_or_else(|| match *ctor {
                ConstCtor::PtrToGlobalVar(gv) => {
                    pretty::Fragment::new(["&".into(), gv.print(printer)])
                }
                ConstCtor::SpvInst(spv::Inst { opcode, ref imms }) => printer.pretty_spv_inst(
                    printer.spv_op_style(),
                    opcode,
                    imms,
                    ctor_args,
                    Print::print,
                    Some(*ty),
                ),
                ConstCtor::SpvStringLiteralForExtInst(s) => pretty::Fragment::new([
                    printer.pretty_spv_opcode(printer.spv_op_style(), wk.OpString),
                    "<".into(),
                    printer
                        .string_literal_style()
                        .apply(format!("{:?}", &printer.cx[s]))
                        .into(),
                    ">".into(),
                ]),
            }),
        }
    }
}

impl Print for Import {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_>) -> pretty::Fragment {
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
    fn print(&self, printer: &Printer<'_>) -> AttrsAndDef {
        let Self {
            attrs,
            type_of_ptr_to,
            shape,
            addr_space,
            def,
        } = self;

        let wk = &spv::spec::Spec::get().well_known;

        let type_ascription_suffix = {
            // HACK(eddyb) get the pointee type from SPIR-V `OpTypePointer`, but
            // ideally the `GlobalVarDecl` would hold that type itself.
            let type_of_ptr_to_def = &printer.cx[*type_of_ptr_to];

            match &type_of_ptr_to_def.ctor {
                TypeCtor::QPtr if shape.is_some() => match shape.unwrap() {
                    qptr::shapes::GlobalVarShape::Handles {
                        handle,
                        fixed_count,
                    } => {
                        let handle = match handle {
                            qptr::shapes::Handle::Opaque(ty) => ty.print(printer),
                            qptr::shapes::Handle::Buffer(addr_space, buf) => {
                                pretty::Fragment::new([
                                    printer.declarative_keyword_style().apply("buffer").into(),
                                    // FIXME(eddyb) is using angle brackets like this consistent styling?
                                    pretty::join_comma_sep("<", [addr_space.print(printer)], ">"),
                                    pretty::join_comma_sep(
                                        "(",
                                        [
                                            pretty::Fragment::new([
                                                "size: ".into(),
                                                pretty::Fragment::new(
                                                    Some(buf.fixed_base.size)
                                                        .filter(|&base_size| {
                                                            base_size > 0
                                                                || buf.dyn_unit_stride.is_none()
                                                        })
                                                        .map(|base_size| {
                                                            printer
                                                                .numeric_literal_style()
                                                                .apply(base_size.to_string())
                                                                .into()
                                                        })
                                                        .into_iter()
                                                        .chain(buf.dyn_unit_stride.map(|stride| {
                                                            pretty::Fragment::new([
                                                                "N × ".into(),
                                                                printer
                                                                    .numeric_literal_style()
                                                                    .apply(stride.to_string()),
                                                            ])
                                                        }))
                                                        .intersperse_with(|| " + ".into()),
                                                ),
                                            ]),
                                            pretty::Fragment::new([
                                                "align: ".into(),
                                                printer
                                                    .numeric_literal_style()
                                                    .apply(buf.fixed_base.align.to_string()),
                                            ]),
                                        ],
                                        ")",
                                    ),
                                ])
                            }
                        };

                        let handles = if fixed_count.map_or(0, |c| c.get()) == 1 {
                            handle
                        } else {
                            pretty::Fragment::new([
                                "[".into(),
                                fixed_count
                                    .map(|count| {
                                        pretty::Fragment::new([
                                            printer
                                                .numeric_literal_style()
                                                .apply(count.to_string()),
                                            " × ".into(),
                                        ])
                                    })
                                    .unwrap_or_default(),
                                handle,
                                "]".into(),
                            ])
                        };
                        pretty::join_space(":", [handles])
                    }
                    qptr::shapes::GlobalVarShape::UntypedData(mem_layout) => {
                        pretty::Fragment::new([
                            " ".into(),
                            printer.declarative_keyword_style().apply("layout").into(),
                            pretty::join_comma_sep(
                                "(",
                                [
                                    pretty::Fragment::new([
                                        "size: ".into(),
                                        printer
                                            .numeric_literal_style()
                                            .apply(mem_layout.size.to_string()),
                                    ]),
                                    pretty::Fragment::new([
                                        "align: ".into(),
                                        printer
                                            .numeric_literal_style()
                                            .apply(mem_layout.align.to_string()),
                                    ]),
                                ],
                                ")",
                            ),
                        ])
                    }
                    qptr::shapes::GlobalVarShape::TypedInterface(ty) => {
                        printer.pretty_type_ascription_suffix(ty)
                    }
                },
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
        let addr_space_suffix = match addr_space {
            AddrSpace::Handles => pretty::Fragment::default(),
            AddrSpace::SpvStorageClass(_) => {
                pretty::Fragment::new([" in ".into(), addr_space.print(printer)])
            }
        };
        let header = pretty::Fragment::new([addr_space_suffix, type_ascription_suffix]);

        let maybe_rhs = match def {
            DeclDef::Imported(import) => Some(import.print(printer)),
            DeclDef::Present(GlobalVarDefBody { initializer }) => {
                // FIXME(eddyb) `global_varX in AS: T = Y` feels a bit wonky for
                // the initializer, but it's cleaner than obvious alternatives.
                initializer.map(|initializer| initializer.print(printer))
            }
        };
        let body = maybe_rhs.map(|rhs| pretty::Fragment::new(["= ".into(), rhs]));

        let def_without_name = pretty::Fragment::new([header, pretty::join_space("", body)]);

        AttrsAndDef {
            attrs: attrs.print(printer),
            def_without_name,
        }
    }
}

impl Print for AddrSpace {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_>) -> pretty::Fragment {
        match *self {
            AddrSpace::Handles => printer.declarative_keyword_style().apply("handles").into(),
            AddrSpace::SpvStorageClass(sc) => {
                let wk = &spv::spec::Spec::get().well_known;
                printer.pretty_spv_imm(wk.StorageClass, sc)
            }
        }
    }
}

impl Print for FuncDecl {
    type Output = AttrsAndDef;
    fn print(&self, printer: &Printer<'_>) -> AttrsAndDef {
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
                    let param_name = match def {
                        DeclDef::Imported(_) => "_".into(),
                        DeclDef::Present(def) => Value::ControlRegionInput {
                            region: def.body,
                            input_idx: i.try_into().unwrap(),
                        }
                        .print_as_def(printer),
                    };
                    param.print(printer).insert_name_before_def(param_name)
                }),
                ")",
            ),
            " -> ".into(),
            ret_type.print(printer),
        ]);

        let def_without_name = match def {
            DeclDef::Imported(import) => {
                pretty::Fragment::new([sig, " = ".into(), import.print(printer)])
            }

            // FIXME(eddyb) this can probably go into `impl Print for FuncDefBody`.
            DeclDef::Present(def) => pretty::Fragment::new([
                sig,
                " {".into(),
                pretty::Node::IndentedBlock(match &def.unstructured_cfg {
                    None => vec![def.at_body().print(printer)],
                    Some(cfg) => cfg
                        .rev_post_order(def)
                        .map(|region| {
                            let label = Use::ControlRegionLabel(region);
                            let label_header = if printer.use_styles.contains_key(&label) {
                                let inputs = &def.at(region).def().inputs;
                                let label_inputs = if !inputs.is_empty() {
                                    pretty::join_comma_sep(
                                        "(",
                                        inputs.iter().enumerate().map(|(input_idx, input)| {
                                            input.print(printer).insert_name_before_def(
                                                Value::ControlRegionInput {
                                                    region,
                                                    input_idx: input_idx.try_into().unwrap(),
                                                }
                                                .print_as_def(printer),
                                            )
                                        }),
                                        ")",
                                    )
                                } else {
                                    pretty::Fragment::default()
                                };

                                // FIXME(eddyb) `:` as used here for C-like "label syntax"
                                // interferes (in theory) with `e: T` "type ascription syntax".
                                pretty::Fragment::new([
                                    pretty::Node::ForceLineSeparation.into(),
                                    label.print_as_def(printer),
                                    label_inputs,
                                    ":".into(),
                                    pretty::Node::ForceLineSeparation.into(),
                                ])
                            } else {
                                pretty::Fragment::default()
                            };

                            pretty::Fragment::new([
                                label_header,
                                pretty::Node::IndentedBlock(vec![def.at(region).print(printer)])
                                    .into(),
                                cfg.control_inst_on_exit_from[region].print(printer),
                            ])
                        })
                        .intersperse({
                            // Separate (top-level) control nodes with empty lines.
                            // FIXME(eddyb) have an explicit `pretty::Node`
                            // for "vertical gap" instead.
                            "\n\n".into()
                        })
                        .collect(),
                })
                .into(),
                "}".into(),
            ]),
        };

        AttrsAndDef {
            attrs: attrs.print(printer),
            def_without_name,
        }
    }

    fn downcast_as_func_decl(&self) -> Option<&FuncDecl> {
        Some(self)
    }
}

impl Print for FuncParam {
    type Output = AttrsAndDef;
    fn print(&self, printer: &Printer<'_>) -> AttrsAndDef {
        let Self { attrs, ty } = *self;

        AttrsAndDef {
            attrs: attrs.print(printer),
            def_without_name: printer.pretty_type_ascription_suffix(ty),
        }
    }
}

impl Print for FuncAt<'_, ControlRegion> {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_>) -> pretty::Fragment {
        let ControlRegionDef {
            inputs: _,
            children,
            outputs,
        } = self.def();

        // NOTE(eddyb) `inputs` are always printed by the parent.

        let outputs_footer = if !outputs.is_empty() {
            let mut outputs = outputs.iter().map(|v| v.print(printer));
            let outputs = if outputs.len() == 1 {
                outputs.next().unwrap()
            } else {
                pretty::join_comma_sep("(", outputs, ")")
            };
            pretty::Fragment::new([pretty::Node::ForceLineSeparation.into(), outputs])
        } else {
            pretty::Fragment::default()
        };

        pretty::Fragment::new([
            Use::AlignmentAnchorForControlRegion(self.position).print_as_def(printer),
            self.at(*children).into_iter().print(printer),
            outputs_footer,
        ])
    }
}

impl Print for FuncAt<'_, EntityListIter<ControlNode>> {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_>) -> pretty::Fragment {
        pretty::Fragment::new(
            self.map(|func_at_control_node| func_at_control_node.print(printer))
                .intersperse(pretty::Node::ForceLineSeparation.into()),
        )
    }
}

impl Print for FuncAt<'_, ControlNode> {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_>) -> pretty::Fragment {
        let control_node = self.position;
        let ControlNodeDef { kind, outputs } = self.def();

        let outputs_header = if !outputs.is_empty() {
            let mut outputs = outputs.iter().enumerate().map(|(output_idx, output)| {
                output.print(printer).insert_name_before_def(
                    Value::ControlNodeOutput {
                        control_node,
                        output_idx: output_idx.try_into().unwrap(),
                    }
                    .print_as_def(printer),
                )
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

        // FIXME(eddyb) using `declarative_keyword_style` seems more
        // appropriate here, but it's harder to spot at a glance.
        let kw_style = printer.imperative_keyword_style();
        let kw = |kw| kw_style.clone().apply(kw).into();
        let control_node_body = match kind {
            ControlNodeKind::Block { insts } => {
                assert!(outputs.is_empty());

                pretty::Fragment::new(
                    self.at(*insts)
                        .into_iter()
                        .map(|func_at_inst| {
                            let data_inst_def = func_at_inst.def();
                            let mut data_inst_attrs_and_def = data_inst_def.print(printer);
                            // FIXME(eddyb) this is quite verbose for prepending.
                            data_inst_attrs_and_def.def_without_name = pretty::Fragment::new([
                                Use::AlignmentAnchorForDataInst(func_at_inst.position)
                                    .print_as_def(printer),
                                data_inst_attrs_and_def.def_without_name,
                            ]);
                            data_inst_attrs_and_def.insert_name_before_def(
                                if printer.cx[data_inst_def.form].output_type.is_none() {
                                    pretty::Fragment::default()
                                } else {
                                    pretty::Fragment::new([
                                        Use::DataInstOutput(func_at_inst.position)
                                            .print_as_def(printer),
                                        " = ".into(),
                                    ])
                                },
                            )
                        })
                        .flat_map(|entry| [pretty::Node::ForceLineSeparation.into(), entry]),
                )
            }
            ControlNodeKind::Select {
                kind,
                scrutinee,
                cases,
            } => kind.print_with_scrutinee_and_cases(
                printer,
                kw_style,
                *scrutinee,
                cases.iter().map(|&case| self.at(case).print(printer)),
            ),
            ControlNodeKind::Loop {
                initial_inputs,
                body,
                repeat_condition,
            } => {
                assert!(outputs.is_empty());

                let inputs = &self.at(*body).def().inputs;
                assert_eq!(initial_inputs.len(), inputs.len());

                // FIXME(eddyb) this avoids customizing how `body` is printed,
                // by adding a `-> ...` suffix to it instead, e.g. this `body`:
                // ```
                // v3 = ...
                // v4 = ...
                // (v3, v4)
                // ```
                // may be printed like this, as part of a loop:
                // ```
                // loop(v1 <- 0, v2 <- false) {
                //   v3 = ...
                //   v4 = ...
                //   (v3, v4) -> (v1, v2)
                // }
                // ```
                // In the above example, `v1` and `v2` are the `inputs` of the
                // `body`, which start at `0`/`false`, and are replaced with
                // `v3`/`v4` after each iteration.
                let (inputs_header, body_suffix) = if !inputs.is_empty() {
                    let input_decls_and_uses =
                        inputs.iter().enumerate().map(|(input_idx, input)| {
                            (
                                input,
                                Value::ControlRegionInput {
                                    region: *body,
                                    input_idx: input_idx.try_into().unwrap(),
                                },
                            )
                        });
                    (
                        pretty::join_comma_sep(
                            "(",
                            input_decls_and_uses.clone().zip(initial_inputs).map(
                                |((input_decl, input_use), initial)| {
                                    pretty::Fragment::new([
                                        input_decl.print(printer).insert_name_before_def(
                                            input_use.print_as_def(printer),
                                        ),
                                        " <- ".into(),
                                        initial.print(printer),
                                    ])
                                },
                            ),
                            ")",
                        ),
                        pretty::Fragment::new([" -> ".into(), {
                            let mut input_dests =
                                input_decls_and_uses.map(|(_, input_use)| input_use.print(printer));
                            if input_dests.len() == 1 {
                                input_dests.next().unwrap()
                            } else {
                                pretty::join_comma_sep("(", input_dests, ")")
                            }
                        }]),
                    )
                } else {
                    (pretty::Fragment::default(), pretty::Fragment::default())
                };

                // FIXME(eddyb) this is a weird mishmash of Rust and C syntax.
                pretty::Fragment::new([
                    kw("loop"),
                    inputs_header,
                    " {".into(),
                    pretty::Node::IndentedBlock(vec![pretty::Fragment::new([
                        self.at(*body).print(printer),
                        body_suffix,
                    ])])
                    .into(),
                    "} ".into(),
                    kw("while"),
                    " ".into(),
                    repeat_condition.print(printer),
                ])
            }
        };
        pretty::Fragment::new([
            Use::AlignmentAnchorForControlNode(self.position).print_as_def(printer),
            outputs_header,
            control_node_body,
        ])
    }
}

impl Print for ControlRegionInputDecl {
    type Output = AttrsAndDef;
    fn print(&self, printer: &Printer<'_>) -> AttrsAndDef {
        let Self { attrs, ty } = *self;

        AttrsAndDef {
            attrs: attrs.print(printer),
            def_without_name: printer.pretty_type_ascription_suffix(ty),
        }
    }
}

impl Print for ControlNodeOutputDecl {
    type Output = AttrsAndDef;
    fn print(&self, printer: &Printer<'_>) -> AttrsAndDef {
        let Self { attrs, ty } = *self;

        AttrsAndDef {
            attrs: attrs.print(printer),
            def_without_name: printer.pretty_type_ascription_suffix(ty),
        }
    }
}

impl Print for DataInstDef {
    type Output = AttrsAndDef;
    fn print(&self, printer: &Printer<'_>) -> AttrsAndDef {
        let Self {
            attrs,
            form,
            inputs,
        } = self;

        let attrs = attrs.print(printer);

        let DataInstFormDef { kind, output_type } = &printer.cx[*form];

        let header = match kind {
            &DataInstKind::FuncCall(func) => pretty::Fragment::new([
                printer.declarative_keyword_style().apply("call").into(),
                " ".into(),
                func.print(printer),
            ]),

            DataInstKind::QPtr(op) => {
                let (qptr_input, extra_inputs) = match op {
                    // HACK(eddyb) `FuncLocalVar` should probably not even be in `QPtrOp`.
                    QPtrOp::FuncLocalVar(_) => (None, &inputs[..]),
                    _ => (Some(inputs[0]), &inputs[1..]),
                };
                let (name, extra_inputs): (_, SmallVec<[_; 1]>) = match op {
                    QPtrOp::FuncLocalVar(mem_layout) => {
                        assert!(extra_inputs.len() <= 1);
                        (
                            "func_local_var",
                            [
                                pretty::Fragment::new([
                                    "size: ".into(),
                                    printer
                                        .numeric_literal_style()
                                        .apply(mem_layout.size.to_string()),
                                ]),
                                pretty::Fragment::new([
                                    "align: ".into(),
                                    printer
                                        .numeric_literal_style()
                                        .apply(mem_layout.align.to_string()),
                                ]),
                            ]
                            .into_iter()
                            .chain(extra_inputs.get(0).map(|&init| {
                                pretty::Fragment::new(["init: ".into(), init.print(printer)])
                            }))
                            .collect(),
                        )
                    }

                    QPtrOp::HandleArrayIndex => {
                        assert_eq!(extra_inputs.len(), 1);
                        (
                            "handle_array_index",
                            [extra_inputs[0].print(printer)].into_iter().collect(),
                        )
                    }
                    QPtrOp::BufferData => {
                        assert_eq!(extra_inputs.len(), 0);
                        ("buffer_data", [].into_iter().collect())
                    }
                    &QPtrOp::BufferDynLen {
                        fixed_base_size,
                        dyn_unit_stride,
                    } => {
                        assert_eq!(extra_inputs.len(), 0);

                        // FIXME(eddyb) this isn't very nice, but without mapping
                        // to actual integer ops, there's not a lot of options.
                        (
                            "buffer_dyn_len",
                            [
                                pretty::Fragment::new([
                                    "fixed_base_size: ".into(),
                                    printer
                                        .numeric_literal_style()
                                        .apply(fixed_base_size.to_string()),
                                ]),
                                pretty::Fragment::new([
                                    "dyn_unit_stride: ".into(),
                                    printer
                                        .numeric_literal_style()
                                        .apply(dyn_unit_stride.to_string()),
                                ]),
                            ]
                            .into_iter()
                            .collect(),
                        )
                    }

                    QPtrOp::Offset(offset) => {
                        assert_eq!(extra_inputs.len(), 0);
                        (
                            "offset",
                            [printer
                                .numeric_literal_style()
                                .apply(format!("{offset}"))
                                .into()]
                            .into_iter()
                            .collect(),
                        )
                    }
                    &QPtrOp::DynOffset {
                        stride,
                        index_bounds: _,
                    } => {
                        assert_eq!(extra_inputs.len(), 1);
                        (
                            "dyn_offset",
                            [pretty::Fragment::new([
                                extra_inputs[0].print(printer),
                                " × ".into(),
                                printer
                                    .numeric_literal_style()
                                    .apply(format!("{stride}"))
                                    .into(),
                            ])]
                            .into_iter()
                            .collect(),
                        )
                    }

                    QPtrOp::Load => {
                        assert_eq!(extra_inputs.len(), 0);
                        ("load", [].into_iter().collect())
                    }
                    QPtrOp::Store => {
                        assert_eq!(extra_inputs.len(), 1);
                        (
                            "store",
                            [extra_inputs[0].print(printer)].into_iter().collect(),
                        )
                    }
                };

                // HACK(eddyb) this duplicates and intentionally breaks away from
                // the style of SPIR-V instructions and how they handle immediates.
                // FIXME(eddyb) pick a consistent style, this is getting annoying.
                return AttrsAndDef {
                    attrs,
                    def_without_name: pretty::Fragment::new([
                        printer
                            .demote_style_for_namespace_prefix(printer.declarative_keyword_style())
                            .apply("qptr.")
                            .into(),
                        printer.declarative_keyword_style().apply(name).into(),
                        pretty::join_comma_sep(
                            "(",
                            qptr_input
                                .map(|v| v.print(printer))
                                .into_iter()
                                .chain(extra_inputs),
                            ")",
                        ),
                        output_type
                            .map(|ty| printer.pretty_type_ascription_suffix(ty))
                            .unwrap_or_default(),
                    ]),
                };
            }

            DataInstKind::SpvInst(inst) => {
                return AttrsAndDef {
                    attrs,
                    def_without_name: printer.pretty_spv_inst(
                        printer.spv_op_style(),
                        inst.opcode,
                        &inst.imms,
                        inputs,
                        Print::print,
                        *output_type,
                    ),
                };
            }
            &DataInstKind::SpvExtInst { ext_set, inst } => {
                let wk = &spv::spec::Spec::get().well_known;

                // FIXME(eddyb) should this be rendered more compactly?
                pretty::Fragment::new([
                    "(".into(),
                    printer.pretty_spv_opcode(printer.spv_op_style(), wk.OpExtInstImport),
                    "<".into(),
                    printer
                        .string_literal_style()
                        .apply(format!("{:?}", &printer.cx[ext_set]))
                        .into(),
                    ">).".into(),
                    printer.pretty_spv_opcode(printer.spv_op_style(), wk.OpExtInst),
                    "<".into(),
                    printer
                        .numeric_literal_style()
                        .apply(format!("{inst}"))
                        .into(),
                    ">".into(),
                ])
            }
        };

        // FIXME(eddyb) deduplicate the "parens + optional type ascription"
        // logic with `pretty_spv_inst`.
        let def_without_name = pretty::Fragment::new([
            header,
            pretty::join_comma_sep("(", inputs.iter().map(|v| v.print(printer)), ")"),
            output_type
                .map(|ty| printer.pretty_type_ascription_suffix(ty))
                .unwrap_or_default(),
        ]);

        AttrsAndDef {
            attrs,
            def_without_name,
        }
    }
}

impl Print for cfg::ControlInst {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_>) -> pretty::Fragment {
        let Self {
            attrs,
            kind,
            inputs,
            targets,
            target_inputs,
        } = self;

        let attrs = attrs.print(printer);

        let kw_style = printer.imperative_keyword_style();
        let kw = |kw| kw_style.clone().apply(kw).into();

        let mut targets = targets.iter().map(|&target_region| {
            let mut target = pretty::Fragment::new([
                kw("branch"),
                " ".into(),
                Use::ControlRegionLabel(target_region).print(printer),
            ]);
            if let Some(inputs) = target_inputs.get(&target_region) {
                target = pretty::Fragment::new([
                    target,
                    pretty::join_comma_sep("(", inputs.iter().map(|v| v.print(printer)), ")"),
                ]);
            }
            target
        });

        let def = match kind {
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
                imms,
            })) => {
                // FIXME(eddyb) use `targets.is_empty()` when that is stabilized.
                assert!(targets.len() == 0);
                printer.pretty_spv_inst(kw_style, *opcode, imms, inputs, Print::print, None)
            }

            cfg::ControlInstKind::Branch => {
                assert_eq!((targets.len(), inputs.len()), (1, 0));
                targets.next().unwrap()
            }

            cfg::ControlInstKind::SelectBranch(kind) => {
                assert_eq!(inputs.len(), 1);
                kind.print_with_scrutinee_and_cases(printer, kw_style.clone(), inputs[0], targets)
            }
        };

        pretty::Fragment::new([attrs, def])
    }
}

impl SelectionKind {
    fn print_with_scrutinee_and_cases(
        &self,
        printer: &Printer<'_>,
        kw_style: pretty::Styles,
        scrutinee: Value,
        mut cases: impl ExactSizeIterator<Item = pretty::Fragment>,
    ) -> pretty::Fragment {
        let kw = |kw| kw_style.clone().apply(kw).into();
        match *self {
            SelectionKind::BoolCond => {
                assert_eq!(cases.len(), 2);
                let [then_case, else_case] = [cases.next().unwrap(), cases.next().unwrap()];
                pretty::Fragment::new([
                    kw("if"),
                    " ".into(),
                    scrutinee.print(printer),
                    " {".into(),
                    pretty::Node::IndentedBlock(vec![then_case]).into(),
                    "} ".into(),
                    kw("else"),
                    " {".into(),
                    pretty::Node::IndentedBlock(vec![else_case]).into(),
                    "}".into(),
                ])
            }
            SelectionKind::SpvInst(spv::Inst { opcode, ref imms }) => {
                #[derive(Copy, Clone)]
                struct TargetLabelId;

                let header = printer.pretty_spv_inst(
                    kw_style.clone(),
                    opcode,
                    imms,
                    [scrutinee]
                        .into_iter()
                        .map(Ok)
                        .chain((0..cases.len()).map(|_| Err(TargetLabelId))),
                    |id, printer| match id {
                        Ok(v) => Some(v.print(printer)),
                        Err(TargetLabelId) => None,
                    },
                    None,
                );

                pretty::Fragment::new([
                    header,
                    " {".into(),
                    pretty::Node::IndentedBlock(
                        cases
                            .map(|case| {
                                pretty::Fragment::new([
                                    pretty::Node::ForceLineSeparation.into(),
                                    // FIXME(eddyb) this should pull information out
                                    // of the instruction to be more precise.
                                    kw("case"),
                                    " => {".into(),
                                    pretty::Node::IndentedBlock(vec![case]).into(),
                                    "}".into(),
                                    pretty::Node::ForceLineSeparation.into(),
                                ])
                            })
                            .collect(),
                    )
                    .into(),
                    "}".into(),
                ])
            }
        }
    }
}

impl Value {
    fn print_as_def(&self, printer: &Printer<'_>) -> pretty::Fragment {
        Use::from(*self).print_as_def(printer)
    }
}

impl Print for Value {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_>) -> pretty::Fragment {
        Use::from(*self).print(printer)
    }
}
