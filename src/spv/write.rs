//! Low-level emission of SPIR-V binary form.

use crate::spv::{self, spec};
use std::path::Path;
use std::{fs, io, iter};

pub struct ModuleEmitter {
    /// Output SPIR-V words.
    // FIXME(eddyb) try to write bytes to an `impl io::Write` directly.
    pub words: Vec<u32>,
}

impl ModuleEmitter {
    pub fn with_header(header: [u32; spec::HEADER_LEN]) -> Self {
        // FIXME(eddyb) sanity-check the provided header words.
        Self {
            words: header.into(),
        }
    }

    pub fn push_inst(&mut self, inst: &spv::Inst) -> io::Result<()> {
        let total_word_count = 1
            + (inst.result_type_id.is_some() as usize)
            + (inst.result_id.is_some() as usize)
            + inst.operands.len();
        let opcode = u32::from(inst.opcode)
            | u32::from(u16::try_from(total_word_count).map_err(|_| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    "word count of SPIR-V instruction doesn't fit in 16 bits",
                )
            })?) << 16;
        self.words.extend(
            iter::once(opcode)
                .chain(inst.result_type_id.map(|id| id.get()))
                .chain(inst.result_id.map(|id| id.get()))
                .chain(inst.operands.iter().map(|operand| match *operand {
                    spv::Operand::Imm(spv::Imm::Short(_, word))
                    | spv::Operand::Imm(spv::Imm::LongStart(_, word))
                    | spv::Operand::Imm(spv::Imm::LongCont(_, word)) => word,
                    spv::Operand::Id(_, id) => id.get(),
                })),
        );
        Ok(())
    }

    pub fn write_to_spv_file(&self, path: impl AsRef<Path>) -> io::Result<()> {
        let spv_bytes = {
            // FIXME(eddyb) find a safe wrapper crate for this.
            fn u32_slice_to_u8_slice(xs: &[u32]) -> &[u8] {
                unsafe {
                    let (prefix, out, suffix) = xs.align_to();
                    assert_eq!((prefix, suffix), (&[][..], &[][..]));
                    out
                }
            }
            u32_slice_to_u8_slice(&self.words)
        };
        fs::write(path, spv_bytes)
    }
}
