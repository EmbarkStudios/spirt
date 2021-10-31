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
    Spv(spv::ModuleLayout),
}

pub enum TopLevel {
    SpvInst(spv::Inst),
}
