//! Pretty-printing SPIR-V operands.

use crate::spv::{self, spec};
use smallvec::SmallVec;
use std::fmt::Write;
use std::{fmt, iter, mem, str};

// HACK(eddyb) using a different type than `spv::Operand` for flexibility.
pub enum PrintOperand {
    Imm(spv::Imm),

    // FIXME(eddyb) this should probably not be made this expensive.
    IdLike(String),
}

// FIXME(eddyb) keep a `&'static spec::Spec` if that can even speed up anything.
struct OperandPrinter<I: Iterator<Item = PrintOperand>> {
    /// Input operands to print from (may be grouped e.g. into literals).
    operands: iter::Peekable<I>,

    /// Output for the current operand (drained by the `all_operands` method).
    out: String,
}

impl<I: Iterator<Item = PrintOperand>> OperandPrinter<I> {
    fn enumerant_params(&mut self, enumerant: &spec::Enumerant) -> fmt::Result {
        struct Unlimited;
        let mut remaining_params = match enumerant.rest_params {
            None => Ok(enumerant.req_params.len()),
            Some(_) => Err(Unlimited),
        };

        let exhausted_params = match remaining_params {
            Ok(count) => count == 0,
            Err(Unlimited) => self.operands.peek().is_none(),
        };
        if !exhausted_params {
            write!(self.out, "(")?;
            loop {
                self.operand()?;
                let exhausted_params = match &mut remaining_params {
                    Ok(count) => {
                        *count -= 1;
                        *count == 0
                    }
                    Err(Unlimited) => self.operands.peek().is_none(),
                };
                if exhausted_params {
                    break;
                }
                write!(self.out, ", ")?;
            }
            write!(self.out, ")")?;
        }

        Ok(())
    }

    fn literal(&mut self, kind: spec::OperandKind, first_word: u32) -> fmt::Result {
        // HACK(eddyb) easier to buffer these than to deal with iterators.
        let mut words = SmallVec::<[u32; 16]>::new();
        words.push(first_word);
        while let Some(&PrintOperand::Imm(spv::Imm::LongCont(cont_kind, word))) =
            self.operands.peek()
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

    fn operand(&mut self) -> fmt::Result {
        let operand = self.operands.next().unwrap();
        match operand {
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
            PrintOperand::IdLike(s) => {
                if self.out.is_empty() {
                    self.out = s;
                } else {
                    self.out.push_str(&s);
                }
                Ok(())
            }
        }
    }

    fn all_operands(mut self) -> impl Iterator<Item = String> {
        iter::from_fn(move || {
            if self.operands.peek().is_none() {
                return None;
            }
            self.operand().unwrap();
            Some(mem::take(&mut self.out))
        })
    }
}

/// Group `operands` into logical operands (i.e. long immediates are unflattened)
/// and produce one output `String` for each of them.
pub fn operands(operands: impl IntoIterator<Item = PrintOperand>) -> impl Iterator<Item = String> {
    OperandPrinter {
        operands: operands.into_iter().peekable(),
        out: String::new(),
    }
    .all_operands()
}
