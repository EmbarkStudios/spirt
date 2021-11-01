use smallvec::SmallVec;
use std::rc::Rc;

pub mod spv;

// TODO(eddyb) split out everything into:
// * a "context" containing type/const definitions
//   (or just intern them globally/thread-locally?)
// * globals (variables/fns) that can be grouped into "modules"
//   (which also have e.g. individual dialects)
pub struct Module {
    pub dialect: ModuleDialect,

    pub top_level: Vec<TopLevel>,
}

pub enum ModuleDialect {
    Spv(spv::Dialect),
}

pub enum TopLevel {
    Misc(Misc),
}

pub struct Misc {
    pub kind: MiscKind,

    // FIXME(eddyb) track this entirely as a def-use graph.
    pub output: Option<MiscOutput>,

    // FIXME(eddyb) maybe split inputs into "params" and "value inputs"?
    // (would "params" only contain immediates, or also e.g. types?)
    pub inputs: SmallVec<[MiscInput; 2]>,
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

pub enum MiscInput {
    // FIXME(eddyb) reconsider whether flattening "long immediates" is a good idea.
    SpvImm(spv::Imm),

    // FIXME(eddyb) get rid of this by tracking all entities SPIR-V uses ID for.
    SpvUntrackedId(spv::Id),

    // FIXME(eddyb) consider using string interning instead of `Rc<String>`.
    SpvExtInstImport(Rc<String>),
}
