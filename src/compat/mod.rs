use smallvec::SmallVec;
use std::num::NonZeroU32;

pub mod spv;

// TODO(eddyb) split out everything into:
// * a "context" containing type/const definitions
//   (or just intern them globally/thread-locally?)
// * globals (variables/fns) that can be grouped into "modules"
//   (which also have format-specifically layouts and whatnot)
pub struct Module {
    /// Non-semantic information, mostly used for perfect round-tripping.
    pub layout: ModuleLayout,

    pub top_level: Vec<TopLevel>,
}

pub enum ModuleLayout {
    Spv(spv::SpvModuleLayout),
}

pub enum TopLevel {
    SpvInst {
        opcode: u16,
        operands: SmallVec<[SpvOperand; 4]>,
    },
    SpvUnknownInst {
        opcode: u16,
        operands: SmallVec<[u32; 8]>,
    },
}

// FIXME(eddyb) consider moving some/all of these defitions into `spv`.

pub enum SpvOperand {
    ShortImm(spv::spec::OperandKind, u32),
    LongImmStart(spv::spec::OperandKind, u32),
    LongImmCont(spv::spec::OperandKind, u32),

    Id(spv::spec::OperandKind, SpvId),
}

pub type SpvId = NonZeroU32;
