// FIXME(eddyb) stop using `itertools` for methods like `intersperse` when they
// get stabilized on `Iterator` instead.
#![allow(unstable_name_collisions)]
use itertools::Itertools as _;

use crate::func_at::FuncAt;
use crate::visit::{DynVisit, InnerVisit, Visit, Visitor};
use crate::{
    cfg, spv, AddrSpace, Attr, AttrSet, AttrSetDef, Const, ConstCtor, ConstDef, Context,
    ControlNode, ControlNodeDef, ControlNodeKind, ControlNodeOutputDecl, ControlRegion,
    ControlRegionDef, DataInst, DataInstDef, DataInstKind, DeclDef, EntityListIter, ExportKey,
    Exportee, Func, FuncDecl, FuncParam, FxIndexMap, GlobalVar, GlobalVarDecl, GlobalVarDefBody,
    Import, Module, ModuleDebugInfo, ModuleDialect, SelectionKind, Type, TypeCtor, TypeCtorArg,
    TypeDef, Value,
};
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use std::collections::hash_map::Entry;
use std::fmt::Write;
use std::{fmt, mem};

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

    /// When visiting module-stored nodes, the `Module` is needed to map the
    /// `Node` to the (per-version) definition, which is then stored in the
    /// (per-version) `FxHashMap` within `per_version_name_and_node_defs`.
    current_module: Option<&'a Module>,

    /// Versions allow comparing multiple copies of the same e.g. `Module`,
    /// with definitions sharing a `Node` key being shown together.
    ///
    /// Each `per_version_name_and_node_defs` entry contains a "version" with:
    /// * a descriptive name (e.g. the name of a pass that produced that version)
    ///   * the name is left empty in the default single-version mode
    /// * its `Node` definitions (dynamic via the `DynNodeDef` helper trait)
    ///
    /// Specific `Node`s may be present in only a subset of versions, and such
    /// a distinction will be reflected in the output.
    ///
    /// For `Node` collection, the last entry consistutes the "active" version.
    per_version_name_and_node_defs: Vec<(String, FxHashMap<Node, &'a dyn DynNodeDef<'a>>)>,

    /// Merged per-`Use` counts across all versions.
    ///
    /// That is, each `Use` maps to the largest count of that `Use` in any version,
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

/// Print `Plan` top-level entry, an effective reification of SPIR-T's implicit DAG.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
enum Node {
    /// Either a whole `Module`, or some other printable type passed to
    /// `Plan::for_root` (e.g. `ExpectedVsFound`).
    Root,

    /// Definitions for all `CxInterned` that need them, grouped together.
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

/// Helper for `Node::AllCxInterned`'s definition, to  be used in `node_defs`.
struct AllCxInterned;

/// Everything interned in `Context`, that might need to be printed once
/// (as part of `Node::AllCxInterned`) and referenced multiple times.
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

/// A `Print` `Output` type that splits the attributes from the main body of the
/// definition, allowing additional processing before they get concatenated.
#[derive(Default)]
pub struct AttrsAndDef {
    pub attrs: pretty::Fragment,

    /// Definition that typically looks like one of these cases:
    /// * ` = ...` for `name = ...`
    /// * `(...) {...}` for `name(...) {...}` (i.e. functions)
    ///
    /// Where `name` is added later
    pub def_without_name: pretty::Fragment,
}

trait DynNodeDef<'a>: DynVisit<'a, Plan<'a>> + Print<Output = AttrsAndDef> {}
impl<'a, T: DynVisit<'a, Plan<'a>> + Print<Output = AttrsAndDef>> DynNodeDef<'a> for T {}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
enum Use {
    Node(Node),

    CxInterned(CxInterned),

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
            Self::Node(node) => node.category().unwrap(),
            Self::CxInterned(interned) => interned.category(),
            Self::ControlPointLabel(_) => "label",
            Self::ControlNodeOutput { .. } | Self::DataInstOutput(_) => "v",
        }
    }
}

impl<'a> Plan<'a> {
    /// Create a `Plan` with all of `root`'s dependencies, followed by `root` itself.
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

    /// Create a `Plan` with all of `module`'s contents.
    ///
    /// Shorthand for `Plan::for_root(module.cx_ref(), module)`.
    pub fn for_module(module: &'a Module) -> Self {
        Self::for_root(module.cx_ref(), module)
    }

    /// Create a `Plan` that combines `Plan::for_root` from each version.
    ///
    /// Each version has a string, which should contain a descriptive name
    /// (e.g. the name of a pass that produced that version).
    ///
    /// While the roots (and their dependencies) can be entirely unrelated, the
    /// output won't be very useful in that case. For ideal results, most of the
    /// same entities (e.g. `GlobalVar` or `Func`) should be in most versions,
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
                assert!(
                    std::ptr::eq(*entry.get(), node_def),
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

    fn visit_global_var_use(&mut self, gv: GlobalVar) {
        match self.current_module {
            Some(module) => {
                self.use_node(Node::GlobalVar(gv), &module.global_vars[gv]);
            }

            // FIXME(eddyb) should this be a hard error?
            None => {}
        }
    }

    fn visit_func_use(&mut self, func: Func) {
        match self.current_module {
            Some(module) => {
                self.use_node(Node::Func(func), &module.funcs[func]);
            }

            // FIXME(eddyb) should this be a hard error?
            None => {}
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

    fn visit_func_decl(&mut self, func_decl: &'a FuncDecl) {
        if let DeclDef::Present(func_def_body) = &func_decl.def {
            if let Some(cfg) = &func_def_body.unstructured_cfg {
                for point_range in cfg.rev_post_order(func_def_body) {
                    if let Some(control_inst) = cfg.control_insts.get(point_range.last()) {
                        for &target in &control_inst.targets {
                            *self
                                .use_counts
                                .entry(Use::ControlPointLabel(target))
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

/// Wrapper for handling the difference between single-version and multi-version
/// output, which aren't expressible in `pretty::Fragment`.
//
// FIXME(eddyb) introduce a `pretty::Node` variant capable of handling this,
// but that's complicated wrt non-HTML output, if they're to also be 2D tables.
pub enum Versions<PF> {
    Single(PF),
    Multiple {
        // FIXME(eddyb) avoid allocating this if possible.
        version_names: Vec<String>,

        /// Each node has definitions "tagged" with an `usize` indicating the
        /// number of versions that share that definition, aka "repeat count"
        /// (i.e. "repeat counts" larger than `1` indicate deduplication).
        per_node_versions_with_repeat_count: Vec<SmallVec<[(PF, usize); 1]>>,
    },
}

impl fmt::Display for Versions<pretty::FragmentPostLayout> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Single(fragment) => fragment.fmt(f),
            Self::Multiple {
                version_names,
                per_node_versions_with_repeat_count,
            } => {
                let mut first = true;

                // HACK(eddyb) this is not the nicest output, but multi-version
                // is intended for HTML input primarily anyway.
                for versions_with_repeat_count in per_node_versions_with_repeat_count {
                    if !first {
                        writeln!(f)?;
                    }
                    first = false;

                    let mut next_version_idx = 0;
                    let mut any_headings = false;
                    for (fragment, repeat_count) in versions_with_repeat_count {
                        // No headings for anything uniform across versions.
                        if (next_version_idx, *repeat_count) != (0, version_names.len()) {
                            any_headings = true;

                            if next_version_idx == 0 {
                                write!(f, "//#IF ")?;
                            } else {
                                write!(f, "//#ELSEIF ")?;
                            }
                            let mut first_name = true;
                            for name in &version_names[next_version_idx..][..*repeat_count] {
                                if !first_name {
                                    write!(f, " | ")?;
                                }
                                first_name = false;

                                write!(f, "`{name}`")?;
                            }
                            writeln!(f)?;
                        }

                        writeln!(f, "{fragment}")?;

                        next_version_idx += repeat_count;
                    }
                    if any_headings {
                        writeln!(f, "//#ENDIF")?;
                    }
                }

                Ok(())
            }
        }
    }
}

impl Versions<pretty::FragmentPostLayout> {
    // FIXME(eddyb) provide a non-allocating version.
    pub fn render_to_html(&self) -> pretty::HtmlSnippet {
        match self {
            Self::Single(fragment) => fragment.render_to_html(),
            Self::Multiple {
                version_names,
                per_node_versions_with_repeat_count,
            } => {
                // HACK(eddyb) using an UUID as a class name in lieu of "scoped <style>".
                const TABLE_CLASS_NAME: &str = "spirt-table-90c2056d-5b38-4644-824a-b4be1c82f14d";

                let mut html = pretty::HtmlSnippet::default();
                html.head_deduplicatable_elements.insert(
                    "
<style>
    SCOPE {
        min-width: 100%;

        border-collapse: collapse;
    }
    SCOPE>tbody>tr>*:not(:only-child) {
        border: solid 1px;
    }
    SCOPE>tbody>tr>th {
        /* HACK(eddyb) these are relative to `pretty`'s own HTML styles. */
        font-size: 17px;
        font-weight: 700;

        font-style: italic;
    }
    SCOPE>tbody>tr>td {
        vertical-align: top;

        /* HACK(eddyb) force local scroll when table isn't wide enough. */
        max-width: 40ch;
    }
    SCOPE>tbody>tr>td>pre {
        overflow-x: auto;
    }
</style>
        "
                    .replace("SCOPE", &format!("table.{TABLE_CLASS_NAME}")),
                );

                let headings = {
                    let mut h = "<tr>".to_string();
                    for name in version_names {
                        write!(h, "<th><code>{name}</code></th>").unwrap();
                    }
                    h + "</tr>\n"
                };

                html.body = format!("<table class=\"{TABLE_CLASS_NAME}\">\n");
                let mut last_was_uniform = true;
                for versions_with_repeat_count in per_node_versions_with_repeat_count {
                    let is_uniform = match versions_with_repeat_count[..] {
                        [(_, repeat_count)] => repeat_count == version_names.len(),
                        _ => false,
                    };

                    if last_was_uniform && is_uniform {
                        // Headings unnecessary, they would be between uniform
                        // rows (or at the very start, before an uniform row).
                    } else {
                        // Repeat the headings often, where necessary.
                        html.body += &headings;
                    }
                    last_was_uniform = is_uniform;

                    html.body += "<tr>\n";
                    for (fragment, repeat_count) in versions_with_repeat_count {
                        writeln!(html.body, "<td colspan=\"{repeat_count}\">").unwrap();

                        let pretty::HtmlSnippet {
                            head_deduplicatable_elements: fragment_head,
                            body: fragment_body,
                        } = fragment.render_to_html();
                        html.head_deduplicatable_elements.extend(fragment_head);
                        html.body += &fragment_body;

                        html.body += "</td>\n";
                    }
                    html.body += "</tr>\n";
                }
                html.body += "</table>";

                html
            }
        }
    }
}

impl<PF> Versions<PF> {
    fn map_pretty_fragments<PF2>(self, f: impl Fn(PF) -> PF2) -> Versions<PF2> {
        match self {
            Versions::Single(fragment) => Versions::Single(f(fragment)),
            Versions::Multiple {
                version_names,
                per_node_versions_with_repeat_count,
            } => Versions::Multiple {
                version_names,
                per_node_versions_with_repeat_count: per_node_versions_with_repeat_count
                    .into_iter()
                    .map(|versions_with_repeat_count| {
                        versions_with_repeat_count
                            .into_iter()
                            .map(|(fragment, repeat_count)| (f(fragment), repeat_count))
                            .collect()
                    })
                    .collect(),
            },
        }
    }
}

impl Plan<'_> {
    /// Print the whole `Plan` to a `Versions<pretty::Fragment>` and perform
    /// layout on its `pretty::Fragment`s.
    ///
    /// The resulting `Versions<pretty::FragmentPostLayout>` value supports
    /// `fmt::Display` for convenience, but also more specific methods
    /// (e.g. HTML output).
    pub fn pretty_print(&self) -> Versions<pretty::FragmentPostLayout> {
        // FIXME(eddyb) make max line width configurable.
        let max_line_width = 120;

        self.print(&Printer::new(self))
            .map_pretty_fragments(|fragment| fragment.layout_with_max_line_width(max_line_width))
    }
}

pub struct Printer<'a> {
    cx: &'a Context,
    use_styles: FxIndexMap<Use, UseStyle>,
}

/// How an `Use` of a definition should be printed.
#[derive(Copy, Clone)]
enum UseStyle {
    /// Refer to the definition by its category and an `idx` (e.g. `"type123"`).
    Anon {
        /// For intra-function `Use`s (i.e. `Use::ControlPointLabel` and values),
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
                if let Use::ControlPointLabel(_)
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
                                            matches!(attr, Attr::SpvDebugLine { .. })
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
                        | Use::ControlPointLabel(_)
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

            let mut control_pointer_label_counter = 0;
            let mut value_counter = 0;

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
                let mut visit_point_range = |point_range: cfg::ControlPointRange| {
                    // The label is only for CFG edge destinations.
                    let label_point = point_range.first();

                    // Only assign a new index if this `ControlPointLabel` is
                    // new in this version (and absent from previous ones).
                    if let Some(use_style @ UseStyle::Inline) =
                        use_styles.get_mut(&Use::ControlPointLabel(label_point))
                    {
                        let idx = control_pointer_label_counter;
                        control_pointer_label_counter += 1;
                        *use_style = UseStyle::Anon {
                            parent_func: Some(func),
                            idx,
                        };
                    }

                    // FIXME(eddyb) stop using `rev_post_order_try_for_each`.
                    func_def_body
                        .at(point_range)
                        .rev_post_order_try_for_each(|func_at_point_cursor| -> Result<(), ()> {
                            let point_cursor = func_at_point_cursor.position;
                            let point = point_cursor.position;

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
                                return Ok(());
                            }

                            let control_node = point.control_node();
                            let ControlNodeDef { kind, outputs } =
                                &*func_def_body.control_nodes[control_node];

                            let block_insts = match *kind {
                                ControlNodeKind::Block { insts } => insts,
                                _ => None,
                            };

                            let defined_values = func_def_body
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
                                // Only assign a new index if this `Value` definition is
                                // new in this version (and absent from previous ones)
                                if let Some(use_style @ UseStyle::Inline) =
                                    use_styles.get_mut(&use_kind)
                                {
                                    let idx = value_counter;
                                    value_counter += 1;
                                    *use_style = UseStyle::Anon {
                                        parent_func: Some(func),
                                        idx,
                                    };
                                }
                            }

                            Ok(())
                        })
                        .unwrap()
                };

                match &func_def_body.unstructured_cfg {
                    None => visit_point_range(cfg::ControlPointRange::LinearChain(
                        func_def_body.at_body().def().children.iter(),
                    )),
                    Some(cfg) => {
                        for point_range in cfg.rev_post_order(func_def_body) {
                            visit_point_range(point_range);
                        }
                    }
                }
            }
        }

        Self { cx, use_styles }
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
            color_opacity: Some(0.3),
            thickness: Some(-3),
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
    fn spv_operand_kind_name_style(&self) -> pretty::Styles {
        // HACK(eddyb) effectively this is almost always redundant.
        pretty::Styles {
            color_opacity: Some(0.4),
            thickness: Some(-3),
            ..self.declarative_keyword_style()
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

impl AttrsAndDef {
    /// Concat `attrs`, `name` and `def_without_name` into a `pretty::Fragment`,
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
        let mut name = name.into();
        if let [pretty::Node::StyledText(ref mut styles_and_text), ..] = name.nodes[..] {
            let styles = &mut styles_and_text.0;
            if !attrs.nodes.is_empty() && mem::take(&mut styles.anchor_is_def) {
                maybe_hoisted_anchor = pretty::Styles {
                    anchor: styles.anchor.clone(),
                    anchor_is_def: true,
                    ..Default::default()
                }
                .apply("")
                .into();
            }
        }
        pretty::Fragment::new([maybe_hoisted_anchor, attrs, name, def_without_name])
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
    /// Common implementation for `Use::print` and `Use::print_as_def`.
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
                        _ => unreachable!(),
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
                Self::ControlPointLabel(_)
                | Self::ControlNodeOutput { .. }
                | Self::DataInstOutput(_) => "_".into(),
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
        let num_versions = self.per_version_name_and_node_defs.len();
        let per_node_versions_with_repeat_count = printer
            .use_styles
            .keys()
            .filter_map(|&use_kind| match use_kind {
                Use::Node(node) => Some(node),
                _ => None,
            })
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
        if num_versions == 1 && self.per_version_name_and_node_defs[0].0 == "" {
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
                per_node_versions_with_repeat_count: per_node_versions_with_repeat_count.collect(),
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
            def_without_name: if let Some(def) = compact_def {
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
            def_without_name: if let Some(def) = compact_def {
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

        let def_without_name = pretty::Fragment::new([header, pretty::join_space("", body)]);

        AttrsAndDef {
            attrs: attrs.print(printer),
            def_without_name,
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
                    param.print(printer).insert_name_before_def(
                        Value::FuncParam {
                            idx: i.try_into().unwrap(),
                        }
                        .print(printer),
                    )
                }),
                ")",
            ),
            " -> ".into(),
            ret_type.print(printer),
        ]);

        let def_without_name = match def {
            DeclDef::Imported(import) => {
                pretty::Fragment::new([sig, " = ".into(), import.print(printer).into()])
            }

            // FIXME(eddyb) this can probably go into `impl Print for FuncDefBody`.
            DeclDef::Present(def) => pretty::Fragment::new([
                sig,
                " {".into(),
                pretty::Node::IndentedBlock(match &def.unstructured_cfg {
                    None => vec![def.at_body().print(printer)],
                    Some(cfg) => cfg
                        .rev_post_order(def)
                        .map(|point_range| {
                            pretty::Fragment::new([
                                def.at(point_range).print(printer),
                                if let Some(control_inst) =
                                    cfg.control_insts.get(point_range.last())
                                {
                                    control_inst.print(printer)
                                } else {
                                    pretty::Fragment::default()
                                },
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
        let ControlRegionDef { children, outputs } = self.def();

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
            self.at(*children).into_iter().print(printer),
            outputs_footer,
        ])
    }
}

impl Print for FuncAt<'_, Option<EntityListIter<ControlNode>>> {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_>) -> pretty::Fragment {
        pretty::Fragment::new(
            self.map(|func_at_control_node| func_at_control_node.print(printer))
                .intersperse(pretty::Node::ForceLineSeparation.into()),
        )
    }
}

impl Print for FuncAt<'_, cfg::ControlPointRange> {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_>) -> pretty::Fragment {
        let point_range = self.position;

        let control_nodes = pretty::Node::IndentedBlock(vec![
            self.at(Some(point_range.control_nodes())).print(printer),
        ])
        .into();

        // The label is only for CFG edge destinations.
        let label_point = point_range.first();
        let label = Use::ControlPointLabel(label_point);
        if printer.use_styles.contains_key(&label) {
            // FIXME(eddyb) `:` as used here for C-like "label syntax"
            // interferes (in theory) with `e: T` "type ascription syntax".
            let label_header = pretty::Fragment::new([
                pretty::Node::ForceLineSeparation.into(),
                label.print_as_def(printer),
                ":".into(),
                pretty::Node::ForceLineSeparation.into(),
            ]);

            pretty::Fragment::new(match label_point {
                cfg::ControlPoint::Entry(_) => [label_header, control_nodes],
                cfg::ControlPoint::Exit(_) => [control_nodes, label_header],
            })
        } else {
            control_nodes
        }
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
            ControlNodeKind::UnstructuredMerge => printer
                .comment_style()
                .apply("/* unstructured merge */")
                .into(),
            ControlNodeKind::Block { insts } => {
                assert!(outputs.is_empty());

                pretty::Fragment::new(
                    self.at(*insts)
                        .into_iter()
                        .map(|func_at_inst| {
                            let data_inst_def = func_at_inst.def();
                            data_inst_def.print(printer).insert_name_before_def(
                                if data_inst_def.output_type.is_none() {
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
                body,
                repeat_condition,
            } => {
                // FIXME(eddyb) this is a weird mishmash of Rust and C syntax.
                pretty::Fragment::new([
                    kw("loop"),
                    " {".into(),
                    pretty::Node::IndentedBlock(vec![self.at(*body).print(printer)]).into(),
                    "} ".into(),
                    kw("while"),
                    " ".into(),
                    repeat_condition.print(printer),
                ])
            }
        };
        pretty::Fragment::new([outputs_header, control_node_body])
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
                    def_without_name: printer.pretty_spv_inst(
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
                pretty::Fragment::new([kw("branch"), " ".into(), targets.nth(0).unwrap()])
            }

            cfg::ControlInstKind::SelectBranch(kind) => {
                assert_eq!(inputs.len(), 1);
                kind.print_with_scrutinee_and_cases(printer, kw_style, inputs[0], targets)
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
                    kw_style,
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

                // FIXME(eddyb) this doesn't work well for structured selects.
                pretty::Fragment::new([
                    header,
                    match cases.len() {
                        0 => pretty::Fragment::default(),
                        1 => pretty::Fragment::new([" ".into(), cases.nth(0).unwrap()]),
                        _ => pretty::join_comma_sep(
                            " {",
                            cases.map(|case| {
                                pretty::Fragment::new([
                                    pretty::Node::ForceLineSeparation.into(),
                                    case,
                                ])
                            }),
                            "}",
                        ),
                    },
                ])
            }
        }
    }
}

impl Value {
    /// Common implementation for `Value::print` and `Value::print_as_def`.
    fn print_as_ref_or_def(&self, printer: &Printer<'_>, is_def: bool) -> pretty::Fragment {
        let value_use = match *self {
            Self::Const(ct) => Use::CxInterned(CxInterned::Const(ct)),
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

    fn print_as_def(&self, printer: &Printer<'_>) -> pretty::Fragment {
        self.print_as_ref_or_def(printer, true)
    }
}

impl Print for Value {
    type Output = pretty::Fragment;
    fn print(&self, printer: &Printer<'_>) -> pretty::Fragment {
        self.print_as_ref_or_def(printer, false)
    }
}
