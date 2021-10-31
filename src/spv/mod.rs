pub mod print;
pub mod read;
pub mod spec;
pub mod write;

// TODO(eddyb) have a way to generate "parsed instructions" out of the module,
// basically whatever would be the the basis for outputting words back out.
pub struct SpvModuleLayout {
    // FIXME(eddyb) parse the version in the header.
    pub header_version: u32,

    pub original_generator_magic: u32,
    pub original_id_bound: u32,

    // FIXME(eddyb) this could be an `IndexSet` if not for duplicates.
    pub capabilities: Vec<u32>,
}
