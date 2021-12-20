//! Pretty-printing SPIR-V operands.

use crate::spv::{self, spec};
use smallvec::SmallVec;
use std::fmt::Write;
use std::{fmt, iter, mem, str};

/// One component in a `PrintOutParts` (see its documentation for details).
pub enum PrintOutPart<ID> {
    /// Fully printed (into a `String`) part.
    Printed(String),

    /// Unprinted part, of its original type (allowing post-processing).
    Id(ID),
}

/// The components outputted by printing a ("logical") SPIR-V operand, which
/// have to be concatenated (after separately processing `ID`s) to obtain the
/// complete printed operand.
///
/// With some rare exceptions (enumerand immediates, with `IdRef` parameters),
/// most `PrintOutParts` will only have one `PrintOutPart`.
pub struct PrintOutParts<ID> {
    pub parts: SmallVec<[PrintOutPart<ID>; 1]>,
}

impl<ID> Default for PrintOutParts<ID> {
    fn default() -> Self {
        Self {
            parts: SmallVec::new(),
        }
    }
}

impl PrintOutParts<String> {
    pub fn concat(self) -> String {
        self.parts
            .into_iter()
            .map(|part| match part {
                PrintOutPart::Printed(s) | PrintOutPart::Id(s) => s,
            })
            .reduce(|out, extra| out + &extra)
            .unwrap_or_default()
    }
}

impl<ID> fmt::Write for PrintOutParts<ID> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        if let Some(PrintOutPart::Printed(part)) = self.parts.last_mut() {
            *part += s;
        } else {
            self.parts.push(PrintOutPart::Printed(s.to_string()));
        }
        Ok(())
    }
}

// FIXME(eddyb) keep a `&'static spec::Spec` if that can even speed up anything.
struct OperandPrinter<IMMS: Iterator<Item = spv::Imm>, ID, IDS: Iterator<Item = ID>> {
    /// Input immediate operands to print from (may be grouped e.g. into literals).
    imms: iter::Peekable<IMMS>,

    /// Input ID operands to print from.
    ids: iter::Peekable<IDS>,

    /// Output for the current operand (drained by the `inst_operands` method).
    out: PrintOutParts<ID>,
}

impl<IMMS: Iterator<Item = spv::Imm>, ID, IDS: Iterator<Item = ID>> OperandPrinter<IMMS, ID, IDS> {
    fn is_exhausted(&mut self) -> bool {
        self.imms.peek().is_none() && self.ids.peek().is_none()
    }

    fn enumerant_params(&mut self, enumerant: &spec::Enumerant) -> fmt::Result {
        let mut first = true;
        for (mode, kind) in enumerant.all_params() {
            if mode == spec::OperandMode::Optional {
                if self.is_exhausted() {
                    break;
                }
            }

            if first {
                write!(self.out, "(")?;
            } else {
                write!(self.out, ", ")?;
            }
            first = false;

            self.operand(kind)?;
        }
        if !first {
            write!(self.out, ")")?;
        }

        Ok(())
    }

    fn literal(&mut self, kind: spec::OperandKind, first_word: u32) -> fmt::Result {
        // HACK(eddyb) easier to buffer these than to deal with iterators.
        let mut words = SmallVec::<[u32; 16]>::new();
        words.push(first_word);
        while let Some(&spv::Imm::LongCont(cont_kind, word)) = self.imms.peek() {
            self.imms.next();
            assert!(kind == cont_kind);
            words.push(word);
        }

        let (name, def) = kind.name_and_def();
        assert!(matches!(def, spec::OperandKindDef::Literal { .. }));

        // FIXME(eddyb) decide when it's useful to show the kind of literal.
        let explicit_kind = false;

        if explicit_kind {
            write!(self.out, "{}(", name)?;
        }

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

        if explicit_kind {
            write!(self.out, ")")?;
        }

        Ok(())
    }

    fn operand(&mut self, kind: spec::OperandKind) -> fmt::Result {
        let (name, def) = kind.name_and_def();

        // FIXME(eddyb) should this be a hard error?
        let write_missing = |this: &mut Self| write!(this.out, "/* missing {} */", name);

        let mut maybe_get_enum_word = || match self.imms.next() {
            Some(spv::Imm::Short(found_kind, word)) => {
                assert!(kind == found_kind);
                Some(word)
            }
            Some(spv::Imm::LongStart(..)) | Some(spv::Imm::LongCont(..)) => unreachable!(),
            None => None,
        };

        match def {
            spec::OperandKindDef::BitEnum { empty_name, bits } => {
                let word = match maybe_get_enum_word() {
                    Some(word) => word,
                    None => return write_missing(self),
                };

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
                let word = match maybe_get_enum_word() {
                    Some(word) => word,
                    None => return write_missing(self),
                };

                let (variant_name, variant_def) =
                    variants.get_named(word.try_into().unwrap()).unwrap();
                write!(self.out, "{}.{}", name, variant_name)?;
                self.enumerant_params(variant_def)
            }
            spec::OperandKindDef::Id => match self.ids.next() {
                Some(id) => {
                    self.out.parts.push(PrintOutPart::Id(id));
                    Ok(())
                }
                None => write_missing(self),
            },
            spec::OperandKindDef::Literal { .. } => {
                // FIXME(eddyb) there's no reason to take the first word now,
                // `self.literal(kind)` could do it itself.
                match self.imms.next() {
                    Some(spv::Imm::Short(found_kind, word))
                    | Some(spv::Imm::LongStart(found_kind, word)) => {
                        assert!(kind == found_kind);
                        self.literal(kind, word)
                    }
                    Some(spv::Imm::LongCont(..)) => unreachable!(),
                    None => write_missing(self),
                }
            }
        }
    }

    fn inst_operands(mut self, opcode: spec::Opcode) -> impl Iterator<Item = PrintOutParts<ID>> {
        opcode.def().all_operands().map_while(move |(mode, kind)| {
            if mode == spec::OperandMode::Optional {
                if self.is_exhausted() {
                    return None;
                }
            }
            self.operand(kind).unwrap();
            Some(mem::take(&mut self.out))
        })
    }
}

/// Print a single SPIR-V operand from only immediates, potentially composed of
/// an enumerand with parameters (which consumes more immediates).
pub fn operand_from_imms(imms: impl IntoIterator<Item = spv::Imm>) -> String {
    let mut printer = OperandPrinter {
        imms: imms.into_iter().peekable(),
        ids: iter::empty().peekable(),
        out: PrintOutParts::default(),
    };
    let &kind = match printer.imms.peek().unwrap() {
        spv::Imm::Short(kind, _) | spv::Imm::LongStart(kind, _) => kind,
        _ => unreachable!(),
    };
    printer.operand(kind).unwrap();
    assert!(printer.imms.next().is_none());
    printer.out.concat()
}

/// Print a single SPIR-V (short) immediate (e.g. an enumerand).
pub fn imm(kind: spec::OperandKind, word: u32) -> String {
    operand_from_imms([spv::Imm::Short(kind, word)])
}

/// Group (ordered according to `opcode`) `imms` and `ids` into logical operands
/// (i.e. long immediates are unflattened) and produce one output `String`
/// by printing each of them.
pub fn inst_operands<ID>(
    opcode: spec::Opcode,
    imms: impl IntoIterator<Item = spv::Imm>,
    ids: impl IntoIterator<Item = ID>,
) -> impl Iterator<Item = PrintOutParts<ID>> {
    OperandPrinter {
        imms: imms.into_iter().peekable(),
        ids: ids.into_iter().peekable(),
        out: PrintOutParts::default(),
    }
    .inst_operands(opcode)
}
