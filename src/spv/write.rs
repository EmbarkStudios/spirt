use crate::spv::spec;
use std::path::Path;
use std::{fs, io, iter};

impl super::SpvModuleLayout {
    pub fn capability_insts(&self) -> impl Iterator<Item = crate::SpvInst> + '_ {
        let spec::WellKnown {
            op_capability,
            capability,
            ..
        } = spec::Spec::get().well_known;
        self.capabilities.iter().map(move |&cap| crate::SpvInst {
            opcode: op_capability,
            result_type_id: None,
            result_id: None,
            operands: iter::once(crate::SpvOperand::ShortImm(capability, cap)).collect(),
        })
    }
}

impl crate::Module {
    pub fn write_to_spv_file(&self, path: impl AsRef<Path>) -> io::Result<()> {
        let spv_spec = spec::Spec::get();
        let layout = match &self.layout {
            crate::ModuleLayout::Spv(layout) => layout,

            #[allow(unreachable_patterns)]
            _ => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "not a SPIR-V module",
                ));
            }
        };
        let reserved_inst_schema = 0;

        // Start with the SPIR-V module header.
        let mut spv_words = vec![
            spv_spec.magic,
            layout.header_version,
            layout.original_generator_magic,
            // FIXME(eddyb) update this if the module has been modified.
            layout.original_id_bound,
            reserved_inst_schema,
        ];
        let mut push_inst = |inst: &crate::SpvInst| -> io::Result<()> {
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
            spv_words.extend(
                iter::once(opcode)
                    .chain(inst.result_type_id.map(|id| id.get()))
                    .chain(inst.result_id.map(|id| id.get()))
                    .chain(inst.operands.iter().map(|operand| match *operand {
                        crate::SpvOperand::ShortImm(_, word)
                        | crate::SpvOperand::LongImmStart(_, word)
                        | crate::SpvOperand::LongImmCont(_, word) => word,
                        crate::SpvOperand::Id(_, id) | crate::SpvOperand::ForwardIdRef(_, id) => {
                            id.get()
                        }
                    })),
            );
            Ok(())
        };

        for cap_inst in layout.capability_insts() {
            push_inst(&cap_inst)?;
        }
        for top_level in &self.top_level {
            match top_level {
                crate::TopLevel::SpvInst(inst) => push_inst(inst)?,
            }
        }

        let spv_bytes = {
            // FIXME(eddyb) find a safe wrapper crate for this.
            fn u32_slice_to_u8_slice(xs: &[u32]) -> &[u8] {
                unsafe {
                    let (prefix, out, suffix) = xs.align_to();
                    assert_eq!((prefix, suffix), (&[][..], &[][..]));
                    out
                }
            }
            u32_slice_to_u8_slice(&spv_words)
        };
        fs::write(path, spv_bytes)
    }
}
