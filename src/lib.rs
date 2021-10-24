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
    SpvInst(SpvInst),
}

// FIXME(eddyb) consider moving some/all of these defitions into `spv`.
pub struct SpvInst {
    pub opcode: u16,

    // FIXME(eddyb) consider nesting "Result Type ID" in "Result ID".
    pub result_type_id: Option<SpvId>,
    pub result_id: Option<SpvId>,

    pub operands: SmallVec<[SpvOperand; 2]>,
}

pub enum SpvOperand {
    ShortImm(spv::spec::OperandKind, u32),
    LongImmStart(spv::spec::OperandKind, u32),
    LongImmCont(spv::spec::OperandKind, u32),

    Id(spv::spec::OperandKind, SpvId),

    // FIXME(eddyb) reduce uses of this by addressing the situations it can
    // appear in, with dedicated IR constructs instead.
    ForwardIdRef(spv::spec::OperandKind, SpvId),
}

pub type SpvId = NonZeroU32;
