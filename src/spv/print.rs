//! Pretty-printing SPIR-V operands.

use crate::spv::{self, spec};
use smallvec::SmallVec;
use std::fmt::Write;
use std::{fmt, iter, mem, str};

// FIXME(eddyb) keep a `&'static spec::Spec` if that can even speed up anything.
struct OperandPrinter<IMMS: Iterator<Item = spv::Imm>, IDS: Iterator<Item = String>> {
    /// Input immediate operands to print from (may be grouped e.g. into literals).
    imms: iter::Peekable<IMMS>,

    /// Input ID operands to print from.
    ids: iter::Peekable<IDS>,

    /// Output for the current operand (drained by the `inst_operands` method).
    out: String,
}

impl<IMMS: Iterator<Item = spv::Imm>, IDS: Iterator<Item = String>> OperandPrinter<IMMS, IDS> {
    fn is_exhausted(&mut self) -> bool {
        self.imms.peek().is_none() && self.ids.peek().is_none()
    }

    fn enumerant_params(&mut self, enumerant: &spec::Enumerant) -> fmt::Result {
        // FIXME(eddyb) maybe define this on `spec::Enumerant` and use it
        // in `spv::read` as well?
        enum EnumParamOperandKind {
            Req(spec::OperandKind),
            Opt(spec::OperandKind),
        }
        let all_params = enumerant
            .req_params
            .iter()
            .copied()
            .map(EnumParamOperandKind::Req)
            .chain(
                enumerant
                    .rest_params
                    .iter()
                    .flat_map(|&kind| iter::repeat_with(move || EnumParamOperandKind::Opt(kind))),
            );

        let mut first = true;
        for kind in all_params {
            let kind = match kind {
                EnumParamOperandKind::Req(kind) => kind,
                EnumParamOperandKind::Opt(kind) => {
                    if self.is_exhausted() {
                        break;
                    }
                    kind
                }
            };

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
        let missing = || format!("/* missing {} */", name);

        let mut maybe_get_enum_word = || match self.imms.next() {
            Some(spv::Imm::Short(found_kind, word)) => {
                assert!(kind == found_kind);
                Some(word)
            }
            Some(spv::Imm::LongStart(..)) | Some(spv::Imm::LongCont(..)) => unreachable!(),
            None => {
                self.out.push_str(&missing());
                None
            }
        };

        match def {
            spec::OperandKindDef::BitEnum { empty_name, bits } => {
                let word = match maybe_get_enum_word() {
                    Some(word) => word,
                    None => return Ok(()),
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
                    None => return Ok(()),
                };

                let (variant_name, variant_def) =
                    variants.get_named(word.try_into().unwrap()).unwrap();
                write!(self.out, "{}.{}", name, variant_name)?;
                self.enumerant_params(variant_def)
            }
            spec::OperandKindDef::Id => {
                let s = self.ids.next().unwrap_or_else(missing);
                if self.out.is_empty() {
                    self.out = s;
                } else {
                    self.out.push_str(&s);
                }
                Ok(())
            }
            spec::OperandKindDef::Literal { .. } => {
                // FIXME(eddyb) there's no reason to take the first word now,
                // `self.literal(kind)` could do itself.
                let (found_kind, first_word) = match self.imms.next() {
                    Some(spv::Imm::Short(kind, word)) | Some(spv::Imm::LongStart(kind, word)) => {
                        (kind, word)
                    }
                    Some(spv::Imm::LongCont(..)) => unreachable!(),
                    None => {
                        self.out.push_str(&missing());
                        return Ok(());
                    }
                };
                assert!(kind == found_kind);
                self.literal(kind, first_word)
            }
        }
    }

    fn inst_operands(mut self, opcode: spec::Opcode) -> impl Iterator<Item = String> {
        let def = opcode.def();

        // FIXME(eddyb) maybe define this on `spec::InstructionDef` and use it
        // in `spv::read` as well?
        enum InstOperandKind {
            Req(spec::OperandKind),
            Opt(spec::OperandKind),
        }
        let all_operands = def
            .req_operands
            .iter()
            .copied()
            .map(InstOperandKind::Req)
            .chain(def.opt_operands.iter().copied().map(InstOperandKind::Opt))
            .chain(def.rest_operands.iter().flat_map(|rest_unit| {
                let (opt_a, req_b) = match *rest_unit {
                    spec::RestOperandsUnit::One(kind) => (kind, None),
                    spec::RestOperandsUnit::Two([a_kind, b_kind]) => (a_kind, Some(b_kind)),
                };
                iter::repeat_with(move || {
                    iter::once(InstOperandKind::Opt(opt_a)).chain(req_b.map(InstOperandKind::Req))
                })
                .flatten()
            }));

        all_operands.map_while(move |kind| {
            let kind = match kind {
                InstOperandKind::Req(kind) => kind,
                InstOperandKind::Opt(kind) => {
                    if self.is_exhausted() {
                        return None;
                    }
                    kind
                }
            };
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
        out: String::new(),
    };
    let &kind = match printer.imms.peek().unwrap() {
        spv::Imm::Short(kind, _) | spv::Imm::LongStart(kind, _) => kind,
        _ => unreachable!(),
    };
    printer.operand(kind).unwrap();
    assert!(printer.imms.next().is_none());
    printer.out
}

/// Print a single SPIR-V (short) immediate (e.g. an enumerand).
pub fn imm(kind: spec::OperandKind, word: u32) -> String {
    operand_from_imms([spv::Imm::Short(kind, word)])
}

/// Group (ordered according to `opcode`) `imms` and `ids` into logical operands
/// (i.e. long immediates are unflattened) and produce one output `String`
/// by printing each of them.
pub fn inst_operands(
    opcode: spec::Opcode,
    imms: impl IntoIterator<Item = spv::Imm>,
    ids: impl IntoIterator<Item = String>,
) -> impl Iterator<Item = String> {
    OperandPrinter {
        imms: imms.into_iter().peekable(),
        ids: ids.into_iter().peekable(),
        out: String::new(),
    }
    .inst_operands(opcode)
}
