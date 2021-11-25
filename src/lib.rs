use smallvec::SmallVec;
use std::collections::BTreeSet;

mod context;
pub use context::{AttrSet, Const, Context, GlobalVar, InternedStr, Type};

pub mod print;
pub mod visit;

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

        pub global_vars: context::UniqIdxMap<GlobalVar, GlobalVarDef>,
        pub funcs: Vec<Func>,
    }

    impl Module {
        pub fn new(cx: Rc<Context>, dialect: ModuleDialect, debug_info: ModuleDebugInfo) -> Self {
            Self {
                cx,

                dialect,
                debug_info,

                global_vars: Default::default(),
                funcs: vec![],
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
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Attr {
    // FIXME(eddyb) de-special-case this by recomputing the interface vars.
    SpvEntryPoint {
        params: SmallVec<[spv::Imm; 2]>,
        interface_global_vars: OrdAssertEq<SmallVec<[GlobalVar; 4]>>,
    },

    SpvAnnotation {
        // FIXME(eddyb) determine this based on the annotation.
        opcode: spv::spec::Opcode,
        // FIXME(eddyb) this cannot represent IDs - is that desirable?
        // (for now we don't support `Op{ExecutionMode,Decorate}Id`)
        params: SmallVec<[spv::Imm; 2]>,
    },

    SpvDebugLine {
        file_path: OrdAssertEq<InternedStr>,
        line: u32,
        col: u32,
    },
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

#[derive(PartialEq, Eq, Hash)]
pub enum TypeCtor {
    SpvInst(spv::spec::Opcode),
}

impl TypeCtor {
    pub fn name(&self) -> &'static str {
        match self {
            Self::SpvInst(opcode) => opcode.name(),
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum TypeCtorArg {
    Type(Type),
    Const(Const),

    // FIXME(eddyb) reconsider whether flattening "long immediates" is a good idea.
    // FIXME(eddyb) it might be worth investingating the performance implications
    // of interning "long immediates", compared to the flattened representation.
    SpvImm(spv::Imm),
}

// FIXME(eddyb) maybe special-case some basic consts like integer literals.
#[derive(PartialEq, Eq, Hash)]
pub struct ConstDef {
    pub attrs: AttrSet,
    pub ty: Type,
    pub ctor: ConstCtor,
    pub ctor_args: SmallVec<[ConstCtorArg; 2]>,
}

#[derive(PartialEq, Eq, Hash)]
pub enum ConstCtor {
    PtrToGlobalVar(GlobalVar),

    SpvInst(spv::spec::Opcode),
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum ConstCtorArg {
    Const(Const),

    // FIXME(eddyb) reconsider whether flattening "long immediates" is a good idea.
    // FIXME(eddyb) it might be worth investingating the performance implications
    // of interning "long immediates", compared to the flattened representation.
    SpvImm(spv::Imm),
}

pub struct GlobalVarDef {
    pub attrs: AttrSet,

    /// The type of a pointer to the global variable (as opposed to the value type).
    // FIXME(eddyb) try to replace with value type (or at least have that too).
    pub type_of_ptr_to: Type,

    /// The address space the global variable will be allocated into.
    pub addr_space: AddrSpace,

    /// If `Some`, the global variable will start out with the specified value.
    pub initializer: Option<Const>,
}

#[derive(Copy, Clone)]
pub enum AddrSpace {
    SpvStorageClass(u32),
}
pub struct Func {
    pub insts: Vec<Misc>,
}

pub struct Misc {
    pub attrs: AttrSet,

    pub kind: MiscKind,

    // FIXME(eddyb) track this entirely as a def-use graph.
    pub output: Option<MiscOutput>,

    // FIXME(eddyb) maybe split inputs into "params" and "value inputs"?
    // (would "params" only contain immediates, or also e.g. types?)
    pub inputs: SmallVec<[MiscInput; 2]>,
}

pub enum MiscKind {
    SpvInst(spv::spec::Opcode),
}

impl MiscKind {
    pub fn name(&self) -> &'static str {
        match self {
            Self::SpvInst(opcode) => opcode.name(),
        }
    }
}

#[derive(Copy, Clone)]
pub enum MiscOutput {
    SpvResult {
        result_type: Option<Type>,
        result_id: spv::Id,
    },
}

#[derive(Copy, Clone)]
pub enum MiscInput {
    Type(Type),
    Const(Const),

    // FIXME(eddyb) reconsider whether flattening "long immediates" is a good idea.
    // FIXME(eddyb) it might be worth investingating the performance implications
    // of interning "long immediates", compared to the flattened representation.
    SpvImm(spv::Imm),

    // FIXME(eddyb) get rid of this by tracking all entities SPIR-V uses ID for.
    SpvUntrackedId(spv::Id),

    SpvExtInstImport(InternedStr),
}
