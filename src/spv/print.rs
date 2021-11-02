//! Pretty-printing SPIR-V operands.

use crate::spv::{self, spec};
use smallvec::SmallVec;
use std::{io, slice, str};

// HACK(eddyb) using a different type than `spv::Operand` for flexibility.
pub enum PrintOperand {
    Imm(spv::Imm),

    // FIXME(eddyb) this should probably not be made this expensive.
    IdLike(String),
}

// FIXME(eddyb) keep a `&'static spec::Spec` if that can even speed up anything.
pub struct OperandPrinter<'a, W> {
    /// Input operands to print from (may be grouped e.g. into literals).
    pub operands: slice::Iter<'a, PrintOperand>,

    /// Output sink to print into.
    // FIXME(eddyb) printing to a string first might be better?
    pub out: W,
}

impl<W: io::Write> OperandPrinter<'_, W> {
    fn enumerant_params(&mut self, enumerant: &spec::Enumerant) -> io::Result<()> {
        let param_count = match enumerant.rest_params {
            None => enumerant.req_params.len(),
            Some(_) => self.operands.len(),
        };

        if param_count != 0 {
            write!(self.out, "(")?;
            for i in 0..param_count {
                if i > 0 {
                    write!(self.out, ", ")?;
                }
                self.operand()?;
            }
            write!(self.out, ")")?;
        }

        Ok(())
    }

    fn literal(&mut self, kind: spec::OperandKind, first_word: u32) -> io::Result<()> {
        // HACK(eddyb) easier to buffer these than to deal with iterators.
        let mut words = SmallVec::<[u32; 16]>::new();
        words.push(first_word);
        while let Some(&PrintOperand::Imm(spv::Imm::LongCont(cont_kind, word))) =
            self.operands.clone().next()
        {
            self.operands.next();
            assert!(kind == cont_kind);
            words.push(word);
        }

        let (name, def) = kind.name_and_def();
        assert!(matches!(def, spec::OperandKindDef::Literal { .. }));

        write!(self.out, "{}(", name)?;

        if kind == spec::Spec::get().well_known.LiteralString {
            // FIXME(eddyb) deduplicate with `spv::extract_literal_string`.
            let bytes: SmallVec<[u8; 64]> = words
                .into_iter()
                .flat_map(u32::to_le_bytes)
                .take_while(|&byte| byte != 0)
                .collect();
            match str::from_utf8(&bytes) {
                Ok(s) => write!(self.out, "{:?}", s)?,
                Err(e) => write!(self.out, "{} in {:?}", e, bytes)?,
            }
        } else if let [word @ 0..=0xffff] = words[..] {
            write!(self.out, "{}", word)?;
        } else {
            write!(self.out, "0x")?;
            for word in words.into_iter().rev() {
                write!(self.out, "{:08x}", word)?;
            }
        }

        write!(self.out, ")")
    }

    fn operand(&mut self) -> io::Result<()> {
        let operand = self.operands.next().unwrap();
        match *operand {
            PrintOperand::Imm(spv::Imm::Short(kind, word)) => {
                let (name, def) = kind.name_and_def();
                match def {
                    spec::OperandKindDef::BitEnum { empty_name, bits } => {
                        write!(self.out, "{}", name)?;
                        if word == 0 {
                            write!(self.out, ".{}", empty_name)
                        } else {
                            write!(self.out, ".(")?;
                            let mut first = true;
                            for bit_idx in spec::BitIdx::of_all_set_bits(word) {
                                if !first {
                                    write!(self.out, " | ")?;
                                }
                                first = false;

                                let (bit_name, bit_def) = bits.get_named(bit_idx).unwrap();
                                write!(self.out, ".{}", bit_name)?;
                                self.enumerant_params(bit_def)?;
                            }
                            write!(self.out, ")")
                        }
                    }
                    spec::OperandKindDef::ValueEnum { variants } => {
                        let (variant_name, variant_def) =
                            variants.get_named(word.try_into().unwrap()).unwrap();
                        write!(self.out, "{}.{}", name, variant_name)?;
                        self.enumerant_params(variant_def)
                    }
                    spec::OperandKindDef::Id => unreachable!(),
                    spec::OperandKindDef::Literal { .. } => self.literal(kind, word),
                }
            }
            PrintOperand::Imm(spv::Imm::LongStart(kind, word)) => self.literal(kind, word),
            PrintOperand::Imm(spv::Imm::LongCont(..)) => unreachable!(),
            PrintOperand::IdLike(ref s) => write!(self.out, "{}", s),
        }
    }

    pub fn all_operands(mut self) -> io::Result<()> {
        // FIXME(eddyb) use `!self.operands.is_empty()` when that is stabilized.
        while self.operands.len() != 0 {
            // FIXME(eddyb) maybe don't print this at the very start?
            write!(self.out, " ")?;
            self.operand()?;
        }
        Ok(())
    }
}
