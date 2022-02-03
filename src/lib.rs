use smallvec::SmallVec;
use std::collections::BTreeSet;

// HACK(eddyb) work around the lack of `FxIndex{Map,Set}` type aliases elsewhere.
type FxIndexMap<K, V> =
    indexmap::IndexMap<K, V, std::hash::BuildHasherDefault<rustc_hash::FxHasher>>;
type FxIndexSet<V> = indexmap::IndexSet<V, std::hash::BuildHasherDefault<rustc_hash::FxHasher>>;

mod context;
pub use context::{
    AttrSet, Const, Context, ControlNode, DataInst, EntityDefs, EntityOrientedDenseMap,
    EntityOrientedMapKey, Func, GlobalVar, InternedStr, Type,
};

pub mod cfg;
pub mod print;
pub mod transform;
pub mod visit;
pub mod passes {
    // NOTE(eddyb) inline `mod` to avoid adding APIs here, it's just namespacing.

    pub mod link;
}

pub mod spv;

// HACK(eddyb) this only serves to disallow modifying the `cx` field of `Module`.
mod sealed {
    use super::*;
    use std::rc::Rc;

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

pub enum ModuleDialect {
    Spv(spv::Dialect),
}

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
}

impl TypeCtor {
    pub fn name(&self) -> &'static str {
        match self {
            Self::SpvInst(inst) => inst.opcode.name(),
        }
    }
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
}

/// Declarations (`GlobalVarDecl`, `FuncDecl`) can contain a full definition,
/// or only be an import of a definition (e.g. from another module).
pub enum DeclDef<D> {
    Imported(Import),
    Present(D),
}

/// An identifier (e.g. a link name, or "symbol") for an import declaration.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum Import {
    LinkName(InternedStr),
}

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

pub struct GlobalVarDefBody {
    /// If `Some`, the global variable will start out with the specified value.
    pub initializer: Option<Const>,
}

pub struct FuncDecl {
    pub attrs: AttrSet,

    pub ret_type: Type,

    pub params: SmallVec<[FuncParam; 2]>,

    pub def: DeclDef<FuncDefBody>,
}

pub struct FuncParam {
    pub attrs: AttrSet,

    pub ty: Type,
}

pub struct FuncDefBody {
    pub data_insts: EntityDefs<DataInst>,
    pub control_nodes: EntityDefs<ControlNode>,

    /// The `ControlRegion` representing the whole body of the function.
    // FIXME(eddyb) this is not that useful without `cfg` right now, which is
    // needed to reach other `ControlNode`s (through CFG edges).
    pub body: ControlRegion,

    /// The (unstructured) control-flow graph of the function.
    // FIXME(eddyb) replace this CFG setup with stricter structured regions.
    pub cfg: cfg::ControlFlowGraph,
}

/// A graph of `ControlNode`s, asymmetrically isolated from surrounding `ControlNode`s:
/// * inputs inside the region are free to use values defined outside
/// * values defined inside the region are hidden from outside users
///   (propagating values to the outside can, and should, be done through
///   the `outputs` field, which can reference values defined inside)
///
/// For more general information on structured control-flow, and specifically
/// how SPIR-T represents it, also see `ControlNodeDef`'s documentation.
//
// FIXME(eddyb) consider perhaps moving more documentation, from there, up here.
///
/// The choice of a separate `ControlRegion` type, instead of "simply" a variant
/// of `ControlNodeKind`, may seem like an unnecessary distinction, but it:
/// * prevents (unwanted) arbitrary nesting of `ControlNode`s
///   * i.e. it prevents `ControlNodeKind` from having child `ControlNode`s,
///     without grouping them into `ControlRegion`s first
/// * provides direct access to `outputs` and ensures their presence
///
/// Currently the `ControlNode` "graph" of a `ControlRegion` is a linear chain
/// (using `first` and `last`, alongside the `{prev,next}_in_control_region`
/// fields in each `ControlNodeDef`, to encode a doubly-linked list made of
/// `ControlNode`s), but this may change in the future.
///
/// Also, regions could include `DataInst`s more directly (as simpler nodes),
/// than merely having a `ControlNode` container for them (`ControlNodeKind::Block`).
pub struct ControlRegion {
    pub first: ControlNode,
    pub last: ControlNode,

    pub outputs: SmallVec<[Value; 2]>,
}

/// A control-flow "node" is a self-contained single-entry single-exit (SESE)
/// subgraph of the control-flow graph (CFG) of a function, with child nodes
/// being grouped into `ControlRegion`s and only appearing exactly once, and
/// no mechanism for leaving a `ControlNode`/`ControlRegion` and continuing to
/// execute the parent function (or any other on the call stack), without going
/// through its single exit (also called "merge") point.
///
/// When the entire body of a function has its control-flow represented as a
/// tree of `ControlRegion`s and their `ControlNode`s, that function is said
/// to have (entirely) "structured control-flow".
///
/// Note that this may differ from other "structured control-flow" definitions,
/// in particular SPIR-V uses a laxer definition, that corresponds more to the
/// constraints of the GLSL language, and is single-entry multiple-exit (SEME)
/// with "alternate exits" consisting of `break`s out of `switch`es and loops,
/// and `return`s (making it non-trivial to inline one function into another).
///
/// In SPIR-T, unstructured control-flow is represented with a separate CFG
/// (i.e. a `cfg::ControlFlowGraph`) connecting `ControlNode`s together, and
/// mainly exists as an intermediary state during lowering to structured regions.
//
// FIXME(eddyb) fully implement CFG structurization.
pub struct ControlNodeDef {
    /// Backwards link in a `ControlRegion`'s doubly-link list of `ControlNode`s.
    pub prev_in_control_region: Option<ControlNode>,
    /// Forwards link in a `ControlRegion`'s doubly-link list of `ControlNode`s.
    pub next_in_control_region: Option<ControlNode>,

    pub kind: ControlNodeKind,
    pub outputs: SmallVec<[ControlNodeOutputDecl; 2]>,
}

#[derive(Copy, Clone)]
pub struct ControlNodeOutputDecl {
    pub attrs: AttrSet,

    pub ty: Type,
}

pub enum ControlNodeKind {
    /// Helper `ControlNode` used for conversions between a CFG and structured regions,
    /// potentially having `ControlNodeOutputDecl`s with values provided externally.
    // FIXME(eddyb) is there a better way to do this?
    UnstructuredMerge,

    Block {
        insts: Vec<DataInst>,
    },
}

pub struct DataInstDef {
    pub attrs: AttrSet,

    pub kind: DataInstKind,

    pub output_type: Option<Type>,

    // FIXME(eddyb) change the inline size of this to fit most instructions.
    pub inputs: SmallVec<[Value; 2]>,
}

#[derive(PartialEq, Eq)]
pub enum DataInstKind {
    // FIXME(eddyb) try to split this into recursive and non-recursive calls,
    // to avoid needing special handling for recursion where it's impossible.
    FuncCall(Func),

    SpvInst(spv::Inst),
    SpvExtInst { ext_set: InternedStr, inst: u32 },
}

#[derive(Copy, Clone)]
pub enum Value {
    Const(Const),
    FuncParam {
        idx: u32,
    },
    // FIXME(eddyb) this variant alone increases the size of the `enum`.
    ControlNodeOutput {
        control_node: ControlNode,
        output_idx: u32,
    },
    DataInstOutput(DataInst),
}
