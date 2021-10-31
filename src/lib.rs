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
    SpvInst(spv::Inst),
}
