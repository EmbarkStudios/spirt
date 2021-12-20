use indexmap::IndexMap;
use smallvec::SmallVec;
use std::collections::BTreeSet;

mod context;
pub use context::{AttrSet, Const, Context, DataInst, Func, GlobalVar, InternedStr, Region, Type};

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

        pub global_vars: context::UniqIdxMap<GlobalVar, GlobalVarDecl>,
        pub funcs: context::UniqIdxMap<Func, FuncDecl>,

        pub exports: IndexMap<ExportKey, Exportee>,
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
    SpvAnnotation {
        // FIXME(eddyb) determine this based on the annotation.
        opcode: spv::spec::Opcode,
        // FIXME(eddyb) this cannot represent IDs - is that desirable?
        // (for now we don't support `Op{ExecutionMode,Decorate}Id`)
        imms: SmallVec<[spv::Imm; 2]>,
    },

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
    SpvInst {
        opcode: spv::spec::Opcode,

        // FIXME(eddyb) reconsider whether flattening "long immediates" is a good idea.
        // FIXME(eddyb) it might be worth investigating the performance implications
        // of interning "long immediates", compared to the flattened representation.
        imms: SmallVec<[spv::Imm; 2]>,
    },
}

impl TypeCtor {
    pub fn name(&self) -> &'static str {
        match self {
            Self::SpvInst { opcode, .. } => opcode.name(),
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

    SpvInst {
        opcode: spv::spec::Opcode,

        // FIXME(eddyb) reconsider whether flattening "long immediates" is a good idea.
        // FIXME(eddyb) it might be worth investigating the performance implications
        // of interning "long immediates", compared to the flattened representation.
        imms: SmallVec<[spv::Imm; 2]>,
    },
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
    // FIXME(eddyb) this might not be the most efficient storage,
    // but it prevents misuse.
    pub data_insts: context::UniqIdxMap<DataInst, DataInstDef>,
    pub regions: context::UniqIdxMap<Region, RegionDef>,

    // FIXME(eddyb) replace this with a hierarchical "structural region" system.
    pub all_regions: Vec<Region>,
}

pub struct RegionDef {
    pub inputs: SmallVec<[RegionInputDecl; 2]>,
    pub insts: Vec<DataInst>,
    pub terminator: ControlInst,
}

pub struct RegionInputDecl {
    pub attrs: AttrSet,

    pub ty: Type,
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

    SpvInst {
        opcode: spv::spec::Opcode,

        // FIXME(eddyb) reconsider whether flattening "long immediates" is a good idea.
        // FIXME(eddyb) it might be worth investigating the performance implications
        // of interning "long immediates", compared to the flattened representation.
        imms: SmallVec<[spv::Imm; 2]>,
    },
    SpvExtInst {
        ext_set: InternedStr,
        inst: u32,
    },
}

pub struct ControlInst {
    pub attrs: AttrSet,

    pub kind: ControlInstKind,

    pub inputs: SmallVec<[Value; 2]>,

    // FIXME(eddyb) change the inline size of this to fit most instructions.
    pub targets: SmallVec<[Region; 4]>,

    // FIXME(eddyb) this is clunky because it models φ nodes (`OpPhi` in SPIR-V),
    // replace the CFG setup with stricter structural regions.
    pub target_inputs: IndexMap<Region, SmallVec<[Value; 2]>>,
}

#[derive(PartialEq, Eq)]
pub enum ControlInstKind {
    SpvInst {
        opcode: spv::spec::Opcode,

        // FIXME(eddyb) reconsider whether flattening "long immediates" is a good idea.
        // FIXME(eddyb) it might be worth investigating the performance implications
        // of interning "long immediates", compared to the flattened representation.
        imms: SmallVec<[spv::Imm; 2]>,
    },
}

#[derive(Copy, Clone)]
pub enum Value {
    Const(Const),
    // FIXME(eddyb) consider replacing this with inputs of the entry region.
    FuncParam { idx: u32 },
    // FIXME(eddyb) this variant alone increases the size of the `enum`.
    RegionInput { region: Region, input_idx: u32 },
    DataInstOutput(DataInst),
}
