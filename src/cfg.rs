//! Control-flow graph (CFG) abstractions and utilities.

use crate::{spv, AttrSet, Region, Value};
use indexmap::IndexMap;
use smallvec::SmallVec;

/// The control-flow graph of a function, represented as per-region
/// control-flow instructions that execute "after" the region itself.
pub type ControlFlowGraph = IndexMap<Region, ControlInst>;

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
    SpvInst(spv::Inst),
}
