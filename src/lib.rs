//! # `SPIR-🇹`
//!
//! **⋯🢒 🇹arget 🠆 🇹ransform 🠆 🇹ranslate ⋯🢒**
//!
//! Shader-focused IR to facilitate working with SPIR-V in a compiler setting.
//!
//! 🚧 *This project is in active design and development, check out
//! [the GitHub repository](https://github.com/EmbarkStudios/spirt).* 🚧

// FIXME(eddyb) should crate docs use `#[doc = include!("../README.md")]`?

// BEGIN - Embark standard lints v6 for Rust 1.55+
// do not change or add/remove here, but one can add exceptions after this section
// for more info see: <https://github.com/EmbarkStudios/rust-ecosystem/issues/59>
#![deny(unsafe_code)]
#![warn(
    clippy::all,
    clippy::await_holding_lock,
    clippy::char_lit_as_u8,
    clippy::checked_conversions,
    clippy::dbg_macro,
    clippy::debug_assert_with_mut_call,
    clippy::doc_markdown,
    clippy::empty_enum,
    clippy::enum_glob_use,
    clippy::exit,
    clippy::expl_impl_clone_on_copy,
    clippy::explicit_deref_methods,
    clippy::explicit_into_iter_loop,
    clippy::fallible_impl_from,
    clippy::filter_map_next,
    clippy::flat_map_option,
    clippy::float_cmp_const,
    clippy::fn_params_excessive_bools,
    clippy::from_iter_instead_of_collect,
    clippy::if_let_mutex,
    clippy::implicit_clone,
    clippy::imprecise_flops,
    clippy::inefficient_to_string,
    clippy::invalid_upcast_comparisons,
    clippy::large_digit_groups,
    clippy::large_stack_arrays,
    clippy::large_types_passed_by_value,
    clippy::let_unit_value,
    clippy::linkedlist,
    clippy::lossy_float_literal,
    clippy::macro_use_imports,
    clippy::manual_ok_or,
    clippy::map_err_ignore,
    clippy::map_flatten,
    clippy::map_unwrap_or,
    clippy::match_on_vec_items,
    clippy::match_same_arms,
    clippy::match_wild_err_arm,
    clippy::match_wildcard_for_single_variants,
    clippy::mem_forget,
    clippy::mismatched_target_os,
    clippy::missing_enforced_import_renames,
    clippy::mut_mut,
    clippy::mutex_integer,
    clippy::needless_borrow,
    clippy::needless_continue,
    clippy::needless_for_each,
    clippy::option_option,
    clippy::path_buf_push_overwrite,
    clippy::ptr_as_ptr,
    clippy::rc_mutex,
    clippy::ref_option_ref,
    clippy::rest_pat_in_fully_bound_structs,
    clippy::same_functions_in_if_condition,
    clippy::semicolon_if_nothing_returned,
    clippy::single_match_else,
    clippy::string_add_assign,
    clippy::string_add,
    clippy::string_lit_as_bytes,
    clippy::string_to_string,
    clippy::todo,
    clippy::trait_duplication_in_bounds,
    clippy::unimplemented,
    clippy::unnested_or_patterns,
    clippy::unused_self,
    clippy::useless_transmute,
    clippy::verbose_file_reads,
    clippy::zero_sized_map_values,
    future_incompatible,
    nonstandard_style,
    rust_2018_idioms
)]
// END - Embark standard lints v6 for Rust 1.55+
// crate-specific exceptions:
#![allow(
    // FIXME(eddyb) review all of these (some of them are intentional, sadly).
    clippy::semicolon_if_nothing_returned,
    clippy::should_implement_trait,
    clippy::single_match,
    clippy::single_match_else,
    clippy::string_add,
    clippy::unimplemented,
    clippy::unnested_or_patterns,
    clippy::unused_self,
    clippy::useless_conversion,
    clippy::vtable_address_comparisons,
    elided_lifetimes_in_paths,
)]
// NOTE(eddyb) this is stronger than the "Embark standard lints" above, because
// we almost never need `unsafe` code and this is a further "speed bump" to it.
#![forbid(unsafe_code)]

use smallvec::SmallVec;
use std::collections::BTreeSet;

// HACK(eddyb) work around the lack of `FxIndex{Map,Set}` type aliases elsewhere.
type FxIndexMap<K, V> =
    indexmap::IndexMap<K, V, std::hash::BuildHasherDefault<rustc_hash::FxHasher>>;
type FxIndexSet<V> = indexmap::IndexSet<V, std::hash::BuildHasherDefault<rustc_hash::FxHasher>>;

mod context;
pub use context::{
    AttrSet, Const, Context, ControlNode, ControlRegion, DataInst, EntityDefs, EntityList,
    EntityListIter, EntityOrientedDenseMap, EntityOrientedMapKey, Func, GlobalVar, InternedStr,
    Type,
};

pub mod cfg;
pub mod func_at;
pub mod print;
pub mod transform;
pub mod visit;
pub mod passes {
    // NOTE(eddyb) inline `mod` to avoid adding APIs here, it's just namespacing.

    pub mod legalize;
    pub mod link;
}

pub mod spv;

// HACK(eddyb) this only serves to disallow modifying the `cx` field of `Module`.
mod sealed {
    use super::*;
    use std::rc::Rc;

    #[derive(Clone)]
    pub struct Module {
        /// Context used for everything interned, in this module.
        ///
        /// Notable choices made for this field:
        /// * private to disallow switching the context of a module
        /// * `Rc` sharing to allow multiple modules to use the same context
        ///   (`Context: !Sync` because of the interners so it can't be `Arc`)
        cx: Rc<Context>,

        pub dialect: ModuleDialect,
        pub debug_info: ModuleDebugInfo,

        pub global_vars: EntityDefs<GlobalVar>,
        pub funcs: EntityDefs<Func>,

        pub exports: FxIndexMap<ExportKey, Exportee>,
    }

    impl Module {
        pub fn new(cx: Rc<Context>, dialect: ModuleDialect, debug_info: ModuleDebugInfo) -> Self {
            Self {
                cx,

                dialect,
                debug_info,

                global_vars: Default::default(),
                funcs: Default::default(),

                exports: Default::default(),
            }
        }

        // FIXME(eddyb) `cx_ref` might be the better default in situations where
        // the module doesn't need to be modified, figure out if that's common.
        pub fn cx(&self) -> Rc<Context> {
            self.cx.clone()
        }

        pub fn cx_ref(&self) -> &Rc<Context> {
            &self.cx
        }
    }
}
pub use sealed::Module;

#[derive(Clone)]
pub enum ModuleDialect {
    Spv(spv::Dialect),
}

#[derive(Clone)]
pub enum ModuleDebugInfo {
    Spv(spv::ModuleDebugInfo),
}

/// An unique identifier (e.g. a link name, or "symbol") for a module export.
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum ExportKey {
    LinkName(InternedStr),

    SpvEntryPoint {
        imms: SmallVec<[spv::Imm; 2]>,
        // FIXME(eddyb) remove this by recomputing the interface vars.
        interface_global_vars: SmallVec<[GlobalVar; 4]>,
    },
}

/// A definition exported out of a module (see also `ExportKey`).
#[derive(Copy, Clone)]
pub enum Exportee {
    GlobalVar(GlobalVar),
    Func(Func),
}

#[derive(Default, PartialEq, Eq, Hash)]
pub struct AttrSetDef {
    // FIXME(eddyb) use `BTreeMap<Attr, AttrValue>` and split some of the params
    // between the `Attr` and `AttrValue` based on specified uniquness.
    // FIXME(eddyb) don't put debuginfo in here, but rather at use sites
    // (for e.g. types, with component types also having the debuginfo
    // bundled at the use site of the composite type) in order to allow
    // deduplicating definitions that only differ in debuginfo, in SPIR-T,
    // and still lift SPIR-V with duplicate definitions, out of that.
    pub attrs: BTreeSet<Attr>,
}

// FIXME(eddyb) consider interning individual attrs, not just `AttrSet`s.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Attr {
    SpvAnnotation(spv::Inst),

    SpvDebugLine {
        file_path: OrdAssertEq<InternedStr>,
        line: u32,
        col: u32,
    },

    /// Some SPIR-V instructions, like `OpFunction`, take a bitflags operand
    /// that is effectively an optimization over using `OpDecorate`.
    // FIXME(eddyb) handle flags having further operands as parameters.
    SpvBitflagsOperand(spv::Imm),
}

// HACK(eddyb) wrapper to limit `Ord` for interned index types (e.g. `InternedStr`)
// to only situations where the interned index reflects contents (i.e. equality).
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct OrdAssertEq<T>(pub T);

impl<T: Eq> PartialOrd for OrdAssertEq<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: Eq> Ord for OrdAssertEq<T> {
    #[track_caller]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        assert!(
            self == other,
            "OrdAssertEq<{}>::cmp called with unequal values",
            std::any::type_name::<T>(),
        );
        std::cmp::Ordering::Equal
    }
}

// FIXME(eddyb) maybe special-case some basic types like integers.
#[derive(PartialEq, Eq, Hash)]
pub struct TypeDef {
    pub attrs: AttrSet,
    pub ctor: TypeCtor,
    pub ctor_args: SmallVec<[TypeCtorArg; 2]>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum TypeCtor {
    SpvInst(spv::Inst),

    /// The type of a `ConstCtor::SpvStringLiteralForExtInst` constant, i.e.
    /// a SPIR-V `OpString` with no actual type in SPIR-V.
    SpvStringLiteralForExtInst,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum TypeCtorArg {
    Type(Type),
    Const(Const),
}

// FIXME(eddyb) maybe special-case some basic consts like integer literals.
#[derive(PartialEq, Eq, Hash)]
pub struct ConstDef {
    pub attrs: AttrSet,
    pub ty: Type,
    pub ctor: ConstCtor,
    pub ctor_args: SmallVec<[Const; 2]>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum ConstCtor {
    PtrToGlobalVar(GlobalVar),

    SpvInst(spv::Inst),

    /// SPIR-V `OpString`, but only when used as an operand for an `OpExtInst`,
    /// which can't have literals itself - for non-string literals `OpConstant*`
    /// are readily usable, but only `OpString` is supported for string literals.
    SpvStringLiteralForExtInst(InternedStr),
}

/// Declarations (`GlobalVarDecl`, `FuncDecl`) can contain a full definition,
/// or only be an import of a definition (e.g. from another module).
#[derive(Clone)]
pub enum DeclDef<D> {
    Imported(Import),
    Present(D),
}

/// An identifier (e.g. a link name, or "symbol") for an import declaration.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum Import {
    LinkName(InternedStr),
}

// FIXME(eddyb) mark any `GlobalVar` not *controlled* by the SPIR-V module
// (roughly: storage classes that don't allow initializers, i.e. most of them),
// as an "import" from "the shader interface", and therefore "externally visible",
// to implicitly distinguish it from `GlobalVar`s internal to the module
// (such as any constants that may need to be reshaped for legalization).
#[derive(Clone)]
pub struct GlobalVarDecl {
    pub attrs: AttrSet,

    /// The type of a pointer to the global variable (as opposed to the value type).
    // FIXME(eddyb) try to replace with value type (or at least have that too).
    pub type_of_ptr_to: Type,

    /// The address space the global variable will be allocated into.
    pub addr_space: AddrSpace,

    pub def: DeclDef<GlobalVarDefBody>,
}

#[derive(Copy, Clone)]
pub enum AddrSpace {
    SpvStorageClass(u32),
}

#[derive(Clone)]
pub struct GlobalVarDefBody {
    /// If `Some`, the global variable will start out with the specified value.
    pub initializer: Option<Const>,
}

#[derive(Clone)]
pub struct FuncDecl {
    pub attrs: AttrSet,

    pub ret_type: Type,

    pub params: SmallVec<[FuncParam; 2]>,

    pub def: DeclDef<FuncDefBody>,
}

#[derive(Copy, Clone)]
pub struct FuncParam {
    pub attrs: AttrSet,

    pub ty: Type,
}

// FIXME(eddyb) `FuncDefBody`/`func_def_body` are too long, find shorter names.
#[derive(Clone)]
pub struct FuncDefBody {
    pub control_regions: EntityDefs<ControlRegion>,
    pub control_nodes: EntityDefs<ControlNode>,
    pub data_insts: EntityDefs<DataInst>,

    /// The `ControlRegion` representing the whole body of the function.
    ///
    /// Function parameters are provided via `body.inputs`, i.e. they can be
    /// only accessed with `Value::ControlRegionInputs { region: body, idx }`.
    ///
    /// When `unstructured_cfg` is `None`, this includes the structured return
    /// of the function, with `body.outputs` as the returned values.
    pub body: ControlRegion,

    /// The unstructured (part of the) control-flow graph of the function.
    ///
    /// Only present if structurization wasn't attempted, or if was only partial
    /// (leaving behind a mix of structured and unstructured control-flow).
    ///
    /// When present, it starts at `body` (more specifically, its exit),
    /// effectively replacing the structured return `body` otherwise implies,
    /// with `body` (or rather, its `children`) always being fully structured.
    pub unstructured_cfg: Option<cfg::ControlFlowGraph>,
}

/// Linear chain of `ControlNode`s, describing a single-entry single-exit (SESE)
/// control-flow "region" (subgraph) in a function's control-flow graph (CFG).
///
/// # Control-flow
///
/// In SPIR-T, two forms of control-flow are used:
/// * "structured": `ControlRegion`s and `ControlNode`s in a "mutual tree"
///   * i.e. each such `ControlRegion` can only appear in exactly one `ControlNode`,
///     and each `ControlNode` can only appear in exactly one `ControlRegion`
///   * a region is either the function's body, or used as part of `ControlNode`
///     (e.g. the "then" case of an `if`-`else`), itself part of a larger region
///   * when inside a region, reaching any other part of the function (or any
///     other function on call stack) requires leaving through the region's
///     single exit (also called "merge") point, i.e. its execution is either:
///     * "convergent": the region completes and continues into its parent
///       `ControlNode`, or function (the latter being a "structured return")
///     * "divergent": execution gets stuck in the region (an infinite loop),
///       or is aborted (e.g. `OpTerminateInvocation` from SPIR-V)
/// * "unstructured": `ControlRegion`s which connect to other `ControlRegion`s
///   using `cfg::ControlInst`s (as described by a `cfg::ControlFlowGraph`)
///
/// When a function's entire body can be described by a single `ControlRegion`,
/// that function is said to have (entirely) "structured control-flow".
///
/// Mixing "structured" and "unstructured" control-flow is supported because:
/// * during structurization, it allows structured subgraphs to remain connected
///   by the same CFG edges that were connecting smaller `ControlRegion`s before
/// * structurization doesn't have to fail in the cases it doesn't fully support
///   yet, but can instead result in a "maximally structured" function
///
/// Other IRs may use different "structured control-flow" definitions, notably:
/// * SPIR-V uses a laxer definition, that corresponds more to the constraints
///   of the GLSL language, and is single-entry multiple-exit (SEME) with
///   "alternate exits" consisting of `break`s out of `switch`es and loops,
///   and `return`s (making it non-trivial to inline one function into another)
/// * RVSDG inspired SPIR-T's design, but its regions are (acyclic) graphs, it
///   makes no distinction between control-flow and "computational" nodes, and
///   its execution order is determined by value/state dependencies alone
///   (SPIR-T may get closer to it in the future, but the initial compromise
///   was chosen to limit the effort of lowering/lifting from/to SPIR-V)
///
/// # Data-flow interactions
///
/// SPIR-T `Value`s follow "single static assignment" (SSA), just like SPIR-V:
/// * inside a function, any new value is produced (or "defined") as an output
///   of `DataInst`/`ControlNode`, and "uses" of that value are `Value`s
///   variants which refer to the defining `DataInst`/`ControlNode` directly
///   (guaranteeing the "single" and "static" of "SSA", by construction)
/// * the definition of a value must "dominate" all of its uses
///   (i.e. in all possible execution paths, the definition precedes all uses)
///
/// But unlike SPIR-V, SPIR-T's structured control-flow has implications for SSA:
/// * dominance is simpler, so values defined in a `ControlRegion` can be used:
///   * later in that region, including in the region's `outputs`
///     (which allows "exporting" values out to the rest of the function)
///   * outside that region, but *only* if the parent `ControlNode` only has
///     exactly one child region (i.e. a single-case `Select`, or a `Loop`)
///     * this is an "emergent" property, stemming from the region having to
///       execute (at least once) before the parent `ControlNode` can complete,
///       but is not is not ideal (especially for reasoning about loops) and
///       should eventually be replaced with passing all such values through
///       the region `outputs` (or by inlining the region, in the `Select` case)
/// * instead of φ ("phi") nodes, SPIR-T uses region `outputs` to merge values
///   coming from separate control-flow paths (i.e. the cases of a `Select`),
///   and region `inputs` for passing values back along loop backedges
///   (additionally, the body's `inputs` are used for function parameters)
///   * like the "block arguments" alternative to SSA phi nodes (which some
///     other SSA IRs use), this has the advantage of keeping the uses of the
///     "source" values in their respective paths (where they're dominated),
///     instead of in the merge (where phi nodes require special-casing, as
///     their "uses" of all the "source" values would normally be illegal)
///   * in unstructured control-flow, region `inputs` are additionally used for
///     phi nodes, as `cfg:ControlInst`s passing values to their target regions
#[derive(Clone)]
pub struct ControlRegionDef {
    /// Inputs to this `ControlRegion`:
    /// * accessed using `Value::ControlRegionInput`
    /// * values provided by the parent:
    ///   * when this is the function body: the function's parameters
    pub inputs: SmallVec<[ControlRegionInputDecl; 2]>,

    pub children: EntityList<ControlNode>,

    /// Output values from this `ControlRegion`, provided to the parent:
    /// * when this is the function body: these are the structured return values
    /// * when this is a `Select` case: these are the values for the parent
    ///   `ControlNode`'s outputs (accessed using `Value::ControlNodeOutput`)
    /// * when this is a `Loop` body: these are the values to be used for the
    ///   next loop iteration's body `inputs`
    ///   * **not** accessible through `Value::ControlNodeOutput` on the `Loop`,
    ///     as it's both confusing regarding `Value::ControlRegionInput`, and
    ///     also there's nothing stopping body-defined values from directly being
    ///     used outside the loop (once that changes, this aspect can be flipped)
    pub outputs: SmallVec<[Value; 2]>,
}

#[derive(Copy, Clone)]
pub struct ControlRegionInputDecl {
    pub attrs: AttrSet,

    pub ty: Type,
}

#[derive(Clone)]
pub struct ControlNodeDef {
    pub kind: ControlNodeKind,

    /// Outputs from this `ControlNode`:
    /// * accessed using `Value::ControlNodeOutput`
    /// * values provided by `region.outputs`, where `region` is the executed
    ///   child `ControlRegion`:
    ///   * when this is a `Select`: the case that was chosen
    pub outputs: SmallVec<[ControlNodeOutputDecl; 2]>,
}

#[derive(Copy, Clone)]
pub struct ControlNodeOutputDecl {
    pub attrs: AttrSet,

    pub ty: Type,
}

#[derive(Clone)]
pub enum ControlNodeKind {
    /// Linear chain of `DataInst`s, executing in sequence.
    ///
    /// This is only an optimization over keeping `DataInst`s in `ControlRegion`
    /// linear chains directly, or even merging `DataInst` with `ControlNode`.
    Block {
        // FIXME(eddyb) should empty blocks be allowed? should `DataInst`s be
        // linked directly into the `ControlRegion` `children` list?
        insts: EntityList<DataInst>,
    },

    /// Choose one `ControlRegion` out of `cases` to execute, based on a single
    /// value input (`scrutinee`) interpreted according to `SelectionKind`.
    ///
    /// This corresponds to "gamma" (`γ`) nodes in (R)VSDG, though those are
    /// sometimes limited only to a two-way selection on a boolean condition.
    Select {
        kind: SelectionKind,
        scrutinee: Value,

        cases: SmallVec<[ControlRegion; 2]>,
    },

    /// Execute `body` repeatedly, until `repeat_condition` evaluates to `false`.
    ///
    /// To represent "loop state", `body` can take `inputs`, getting values from:
    /// * on the first iteration: `initial_inputs`
    /// * on later iterations: `body`'s own `outputs` (from the last iteration)
    ///
    /// As the condition is checked only *after* the body, this type of loop is
    /// sometimes described as "tail-controlled", and is also equivalent to the
    /// C-like `do { body; } while(repeat_condition)` construct.
    ///
    /// This corresponds to "theta" (`θ`) nodes in (R)VSDG.
    Loop {
        initial_inputs: SmallVec<[Value; 2]>,

        body: ControlRegion,

        // FIXME(eddyb) should this be kept in `body.outputs`? (that would not
        // have any ambiguity as to whether it can see `body`-computed values)
        repeat_condition: Value,
    },
}

#[derive(Clone)]
pub enum SelectionKind {
    /// Two-case selection based on boolean condition, i.e. `if`-`else`, with
    /// the two cases being "then" and "else" (in that order).
    BoolCond,

    SpvInst(spv::Inst),
}

#[derive(Clone)]
pub struct DataInstDef {
    pub attrs: AttrSet,

    pub kind: DataInstKind,

    pub output_type: Option<Type>,

    // FIXME(eddyb) change the inline size of this to fit most instructions.
    pub inputs: SmallVec<[Value; 2]>,
}

#[derive(Clone, PartialEq, Eq)]
pub enum DataInstKind {
    // FIXME(eddyb) try to split this into recursive and non-recursive calls,
    // to avoid needing special handling for recursion where it's impossible.
    FuncCall(Func),

    SpvInst(spv::Inst),
    SpvExtInst { ext_set: InternedStr, inst: u32 },
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum Value {
    Const(Const),

    /// One of the inputs to a `ControlRegion`:
    /// * declared by `region.inputs[input_idx]`
    /// * value provided by the parent of the `region`:
    ///   * when `region` is the function body: `input_idx`th function parameter
    ControlRegionInput {
        region: ControlRegion,
        input_idx: u32,
    },

    /// One of the outputs produced by a `ControlNode`:
    /// * declared by `control_node.outputs[output_idx]`
    /// * value provided by `region.outputs[output_idx]`, where `region` is the
    ///   executed child `ControlRegion` (of `control_node`):
    ///   * when `control_node` is a `Select`: the case that was chosen
    ControlNodeOutput {
        control_node: ControlNode,
        output_idx: u32,
    },

    /// The output value of a `DataInst`.
    DataInstOutput(DataInst),
}
