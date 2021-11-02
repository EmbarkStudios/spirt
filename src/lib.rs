use smallvec::SmallVec;
use std::collections::BTreeSet;
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

    // FIXME(eddyb) intern attr sets instead of just using `Rc`.
    // FIXME(eddyb) use `BTreeMap<Attr, AttrValue>` and split some of the params
    // between the `Attr` and `AttrValue` based on specified uniquness.
    // FIXME(eddyb) don't put debuginfo in here, but rather at use sites
    // (for e.g. types, with component types also having the debuginfo
    // bundled at the use site of the composite type) in order to allow
    // deduplicating definitions that only differ in debuginfo, in SPIR-T,
    // and still lift SPIR-V with duplicate definitions, out of that.
    pub attrs: Option<Rc<BTreeSet<Attr>>>,
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

#[derive(PartialEq, Eq, PartialOrd, Ord)]
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
}
