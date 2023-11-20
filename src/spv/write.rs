//! Low-level emission of SPIR-V binary form.

use crate::spv::{self, spec};
use std::borrow::Cow;
use std::path::Path;
use std::{fs, io, iter, slice};

// FIXME(eddyb) keep a `&'static spec::Spec` if that can even speed up anything.
struct OperandEmitter<'a> {
    // FIXME(eddyb) use a field like this to interpret `Opcode`/`OperandKind`, too.
    wk: &'static spv::spec::WellKnown,

    /// Input immediate operands of an instruction.
    imms: iter::Copied<slice::Iter<'a, spv::Imm>>,

    /// Input ID operands of an instruction.
    ids: iter::Copied<slice::Iter<'a, spv::Id>>,

    /// Output SPIR-V words.
    out: &'a mut Vec<u32>,
}

enum OperandEmitError {
    /// Ran out of immediates while emitting an instruction's operands.
    NotEnoughImms,

    /// Ran out of IDs while emitting an instruction's operands.
    NotEnoughIds,

    /// Extra immediates were left over, after emitting an instruction's operands.
    TooManyImms,

    /// Extra IDs were left over, after emitting an instruction's operands.
    TooManyIds,

    /// Unsupported enumerand value.
    UnsupportedEnumerand(spec::OperandKind, u32),

    /// Unsupported `OpSpecConstantOp` (`LiteralSpecConstantOpInteger`) opcode.
    UnsupportedSpecConstantOpOpcode(u32),
}

impl OperandEmitError {
    // FIXME(eddyb) improve messages and add more contextual information.
    fn message(&self) -> Cow<'static, str> {
        match *self {
            Self::NotEnoughImms => "truncated instruction (immediates)".into(),
            Self::NotEnoughIds => "truncated instruction (IDs)".into(),
            Self::TooManyImms => "overlong instruction (immediates)".into(),
            Self::TooManyIds => "overlong instruction (IDs)".into(),
            // FIXME(eddyb) deduplicate this with `spv::read`.
            Self::UnsupportedEnumerand(kind, word) => {
                let (name, def) = kind.name_and_def();
                match def {
                    spec::OperandKindDef::BitEnum { bits, .. } => {
                        let unsupported = spec::BitIdx::of_all_set_bits(word)
                            .filter(|&bit_idx| bits.get(bit_idx).is_none())
                            .fold(0u32, |x, i| x | (1 << i.0));
                        format!("unsupported {name} bit-pattern 0x{unsupported:08x}").into()
                    }

                    spec::OperandKindDef::ValueEnum { .. } => {
                        format!("unsupported {name} value {word}").into()
                    }

                    _ => unreachable!(),
                }
            }
            Self::UnsupportedSpecConstantOpOpcode(opcode) => {
                format!("{opcode} is not a supported opcode (for `OpSpecConstantOp`)").into()
            }
        }
    }
}

impl OperandEmitter<'_> {
    fn is_exhausted(&mut self) -> bool {
        // FIXME(eddyb) use `self.imms.is_empty() && self.ids.is_empty()` when
        // that is stabilized.
        self.imms.len() == 0 && self.ids.len() == 0
    }

    fn enumerant_params(&mut self, enumerant: &spec::Enumerant) -> Result<(), OperandEmitError> {
        for (mode, kind) in enumerant.all_params() {
            if mode == spec::OperandMode::Optional && self.is_exhausted() {
                break;
            }
            self.operand(kind)?;
        }

        Ok(())
    }

    fn operand(&mut self, kind: spec::OperandKind) -> Result<(), OperandEmitError> {
        use OperandEmitError as Error;

        let mut get_enum_word = || match self.imms.next() {
            Some(spv::Imm::Short(found_kind, word)) => {
                assert_eq!(kind, found_kind);
                Ok(word)
            }
            Some(spv::Imm::LongStart(..) | spv::Imm::LongCont(..)) => unreachable!(),
            None => Err(Error::NotEnoughImms),
        };

        match kind.def() {
            spec::OperandKindDef::BitEnum { bits, .. } => {
                let word = get_enum_word()?;
                self.out.push(word);

                for bit_idx in spec::BitIdx::of_all_set_bits(word) {
                    let bit_def =
                        bits.get(bit_idx).ok_or(Error::UnsupportedEnumerand(kind, word))?;
                    self.enumerant_params(bit_def)?;
                }
            }
            spec::OperandKindDef::ValueEnum { variants } => {
                let word = get_enum_word()?;
                self.out.push(word);

                let variant_def = u16::try_from(word)
                    .ok()
                    .and_then(|v| variants.get(v))
                    .ok_or(Error::UnsupportedEnumerand(kind, word))?;
                self.enumerant_params(variant_def)?;
            }
            spec::OperandKindDef::Id => {
                self.out.push(self.ids.next().ok_or(Error::NotEnoughIds)?.get());
            }
            spec::OperandKindDef::Literal { .. } => {
                match self.imms.next().ok_or(Error::NotEnoughImms)? {
                    spv::Imm::Short(found_kind, word) => {
                        assert_eq!(kind, found_kind);
                        self.out.push(word);
                    }
                    spv::Imm::LongStart(found_kind, word) => {
                        assert_eq!(kind, found_kind);
                        self.out.push(word);
                        while let Some(spv::Imm::LongCont(cont_kind, word)) =
                            self.imms.clone().next()
                        {
                            self.imms.next();
                            assert_eq!(kind, cont_kind);
                            self.out.push(word);
                        }
                    }
                    spv::Imm::LongCont(..) => unreachable!(),
                }
            }
        }

        // HACK(eddyb) this isn't cleanly uniform because it's an odd special case.
        if kind == self.wk.LiteralSpecConstantOpInteger {
            // FIXME(eddyb) this partially duplicates the main instruction emission.
            let &word = self.out.last().unwrap();
            let (_, _, inner_def) = u16::try_from(word)
                .ok()
                .and_then(spec::Opcode::try_from_u16_with_name_and_def)
                .ok_or(Error::UnsupportedSpecConstantOpOpcode(word))?;

            for (inner_mode, inner_kind) in inner_def.all_operands() {
                if inner_mode == spec::OperandMode::Optional && self.is_exhausted() {
                    break;
                }
                self.operand(inner_kind)?;
            }
        }

        Ok(())
    }

    fn inst_operands(mut self, def: &spec::InstructionDef) -> Result<(), OperandEmitError> {
        use OperandEmitError as Error;

        for (mode, kind) in def.all_operands() {
            if mode == spec::OperandMode::Optional && self.is_exhausted() {
                break;
            }
            self.operand(kind)?;
        }

        // The instruction must consume all of its operands.
        if !self.is_exhausted() {
            return Err(
                // FIXME(eddyb) use `!self.imms.is_empty()` when that is stabilized.
                if self.imms.len() != 0 {
                    Error::TooManyImms
                } else {
                    // FIXME(eddyb) use `!self.ids.is_empty()` when that is stabilized.
                    assert!(self.ids.len() != 0);
                    Error::TooManyIds
                },
            );
        }

        Ok(())
    }
}

pub struct ModuleEmitter {
    /// Output SPIR-V words.
    // FIXME(eddyb) try to write bytes to an `impl io::Write` directly.
    pub words: Vec<u32>,
}

// FIXME(eddyb) stop abusing `io::Error` for error reporting.
fn invalid(reason: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, format!("malformed SPIR-V ({reason})"))
}

impl ModuleEmitter {
    pub fn with_header(header: [u32; spec::HEADER_LEN]) -> Self {
        // FIXME(eddyb) sanity-check the provided header words.
        Self { words: header.into() }
    }

    // FIXME(eddyb) sanity-check the operands against the definition of `inst.opcode`.
    pub fn push_inst(&mut self, inst: &spv::InstWithIds) -> io::Result<()> {
        let (inst_name, def) = inst.opcode.name_and_def();
        let invalid = |msg: &str| invalid(&format!("in {inst_name}: {msg}"));

        // FIXME(eddyb) make these errors clearer (or turn them into asserts?).
        if inst.result_type_id.is_some() != def.has_result_type_id {
            return Err(invalid("result type ID (`IdResultType`) mismatch"));
        }
        if inst.result_id.is_some() != def.has_result_id {
            return Err(invalid("result ID (`IdResult`) mismatch"));
        }

        let total_word_count = 1
            + (inst.result_type_id.is_some() as usize)
            + (inst.result_id.is_some() as usize)
            + inst.imms.len()
            + inst.ids.len();

        self.words.reserve(total_word_count);
        let expected_final_pos = self.words.len() + total_word_count;

        let opcode = u32::from(inst.opcode.as_u16())
            | u32::from(u16::try_from(total_word_count).ok().ok_or_else(|| {
                invalid("word count of SPIR-V instruction doesn't fit in 16 bits")
            })?) << 16;
        self.words.extend(
            iter::once(opcode)
                .chain(inst.result_type_id.map(|id| id.get()))
                .chain(inst.result_id.map(|id| id.get())),
        );

        OperandEmitter {
            wk: &spec::Spec::get().well_known,
            imms: inst.imms.iter().copied(),
            ids: inst.ids.iter().copied(),
            out: &mut self.words,
        }
        .inst_operands(def)
        .map_err(|e| invalid(&e.message()))?;

        // If no error was produced so far, `OperandEmitter` should've pushed
        // the exact number of words.
        assert_eq!(self.words.len(), expected_final_pos);

        Ok(())
    }

    pub fn write_to_spv_file(&self, path: impl AsRef<Path>) -> io::Result<()> {
        fs::write(path, bytemuck::cast_slice::<u32, u8>(&self.words))
    }
}
