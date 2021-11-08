use smallvec::SmallVec;
use std::collections::BTreeSet;

mod context;
pub use context::{AttrSet, Context, InternedStr};

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

        pub globals: Vec<Global>,
        pub funcs: Vec<Func>,
    }

    impl Module {
        pub fn new(cx: Rc<Context>, dialect: ModuleDialect, debug_info: ModuleDebugInfo) -> Self {
            Self {
                cx,

                dialect,
                debug_info,

                globals: vec![],
                funcs: vec![],
            }
        }

        // FIXME(eddyb) `-> &Rc<Context>` might be better in situations where
        // the module doesn't need to be modified, figure out if that's common.
        pub fn cx(&self) -> Rc<Context> {
            self.cx.clone()
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

pub enum Global {
    Misc(Misc),
}

pub struct Func {
    pub insts: Vec<Misc>,
}

pub struct Misc {
    pub kind: MiscKind,

    // FIXME(eddyb) track this entirely as a def-use graph.
    pub output: Option<MiscOutput>,

    // FIXME(eddyb) maybe split inputs into "params" and "value inputs"?
    // (would "params" only contain immediates, or also e.g. types?)
    pub inputs: SmallVec<[MiscInput; 2]>,

    pub attrs: AttrSet,
}

pub enum MiscKind {
    SpvInst { opcode: u16 },
}

pub enum MiscOutput {
    SpvResult {
        result_type_id: Option<spv::Id>,
        result_id: spv::Id,
    },
}

#[derive(Copy, Clone)]
pub enum MiscInput {
    // FIXME(eddyb) reconsider whether flattening "long immediates" is a good idea.
    // FIXME(eddyb) it might be worth investingating the performance implications
    // of interning "long immediates", compared to the flattened representation.
    SpvImm(spv::Imm),

    // FIXME(eddyb) get rid of this by tracking all entities SPIR-V uses ID for.
    SpvUntrackedId(spv::Id),

    SpvExtInstImport(InternedStr),
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
    // FIXME(eddyb) de-special-case this by recomputing the interface IDs.
    SpvEntryPoint {
        params: SmallVec<[spv::Imm; 2]>,
        interface_ids: SmallVec<[spv::Id; 4]>,
    },

    SpvAnnotation {
        // FIXME(eddyb) determine this based on the annotation.
        opcode: u16,
        // FIXME(eddyb) this cannot represent IDs - is that desirable?
        // (for now we don't support `Op{ExecutionMode,Decorate}Id`)
        params: SmallVec<[spv::Imm; 2]>,
    },

    SpvDebugLine {
        file_path: InternedStr,
        line: u32,
        col: u32,
    },
}
