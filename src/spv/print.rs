//! Pretty-printing SPIR-V operands.

use crate::spv::{self, spec};
use smallvec::SmallVec;
use std::borrow::Cow;
use std::fmt::Write;
use std::{iter, mem, str};

/// The smallest unit produced by printing a ("logical") SPIR-V operand.
///
/// All variants other than `Id` contain a fully formatted string, and the
/// distinction between variants can be erased to obtain a plain-text version
/// (also except `OperandKindNamespacePrefix` requiring an extra implicit `.`).
//
// FIXME(eddyb) should there be a `TokenKind` enum and then `Cow<'static, str>`
// paired with a `TokenKind` in place of all of these individual variants?
pub enum Token<ID> {
    /// An inconsistency was detected in the operands to be printed.
    /// For stylistic consistency, the error message is always found wrapped in
    /// a block comment (i.e. the [`String`] is always of the form `"/* ... */"`).
    Error(String),

    // NOTE(eddyb) this implies a suffix `: ` not included in the string, and
    // optionally some processing of the name (e.g. removing spaces).
    OperandName(&'static str),

    // FIXME(eddyb) perhaps encode the hierarchical structure of e.g. enumerand
    // parameters, so that the SPIR-T printer can do layout for them.
    Punctuation(&'static str),

    // NOTE(eddyb) this implies a suffix `.` not included in the string.
    OperandKindNamespacePrefix(&'static str),

    EnumerandName(&'static str),

    NumericLiteral(String),
    StringLiteral(String),

    /// Unprinted ID operand, of its original type (allowing post-processing).
    Id(ID),
}

/// All the [`Token`]s outputted by printing one single ("logical") SPIR-V operand,
/// which may be concatenated (after separately processing `ID`s) to obtain a
/// complete plain-text version of the printed operand.
pub struct TokensForOperand<ID> {
    pub tokens: SmallVec<[Token<ID>; 3]>,
}

impl<ID> Default for TokensForOperand<ID> {
    fn default() -> Self {
        Self { tokens: SmallVec::new() }
    }
}

impl TokensForOperand<String> {
    pub fn concat_to_plain_text(self) -> String {
        self.tokens
            .into_iter()
            .flat_map(|token| {
                let (first, second): (Cow<'_, str>, _) = match token {
                    Token::OperandName(s) => (s.into(), Some(": ".into())),
                    Token::OperandKindNamespacePrefix(s) => (s.into(), Some(".".into())),
                    Token::Punctuation(s) | Token::EnumerandName(s) => (s.into(), None),
                    Token::Error(s)
                    | Token::NumericLiteral(s)
                    | Token::StringLiteral(s)
                    | Token::Id(s) => (s.into(), None),
                };
                [first].into_iter().chain(second)
            })
            .reduce(|out, extra| (out.into_owned() + &extra).into())
            .unwrap_or_default()
            .into_owned()
    }
}

// FIXME(eddyb) keep a `&'static spec::Spec` if that can even speed up anything.
struct OperandPrinter<IMMS: Iterator<Item = spv::Imm>, ID, IDS: Iterator<Item = ID>> {
    // FIXME(eddyb) use a field like this to interpret `Opcode`/`OperandKind`, too.
    wk: &'static spv::spec::WellKnown,

    /// Input immediate operands to print from (may be grouped e.g. into literals).
    imms: iter::Peekable<IMMS>,

    /// Input ID operands to print from.
    ids: iter::Peekable<IDS>,

    /// Output for the current operand (drained by the `inst_operands` method).
    out: TokensForOperand<ID>,
}

impl<IMMS: Iterator<Item = spv::Imm>, ID, IDS: Iterator<Item = ID>> OperandPrinter<IMMS, ID, IDS> {
    fn is_exhausted(&mut self) -> bool {
        self.imms.peek().is_none() && self.ids.peek().is_none()
    }

    fn enumerant_params(&mut self, enumerant: &spec::Enumerant) {
        let mut first = true;
        for (mode, name_and_kind) in enumerant.all_params_with_names() {
            if mode == spec::OperandMode::Optional && self.is_exhausted() {
                break;
            }

            self.out.tokens.push(Token::Punctuation(if first { "(" } else { ", " }));
            first = false;

            let (name, kind) = name_and_kind.name_and_kind();
            self.operand(name, kind);
        }
        if !first {
            self.out.tokens.push(Token::Punctuation(")"));
        }
    }

    fn literal(&mut self, kind: spec::OperandKind, first_word: u32) {
        // HACK(eddyb) easier to buffer these than to deal with iterators.
        let mut words = SmallVec::<[u32; 16]>::new();
        words.push(first_word);
        while let Some(&spv::Imm::LongCont(cont_kind, word)) = self.imms.peek() {
            self.imms.next();
            assert_eq!(kind, cont_kind);
            words.push(word);
        }

        let def = kind.def();
        assert!(matches!(def, spec::OperandKindDef::Literal { .. }));

        let literal_token = if kind == self.wk.LiteralSpecConstantOpInteger {
            assert_eq!(words.len(), 1);
            let (_, inner_name, inner_def) = match u16::try_from(first_word)
                .ok()
                .and_then(spec::Opcode::try_from_u16_with_name_and_def)
            {
                Some(opcode_name_and_def) => opcode_name_and_def,
                None => {
                    self.out.tokens.push(Token::Error(format!(
                        "/* {first_word} not a valid `OpSpecConstantOp` opcode */"
                    )));
                    return;
                }
            };

            // FIXME(eddyb) deduplicate this with `enumerant_params`.
            self.out.tokens.push(Token::EnumerandName(inner_name));

            let mut first = true;
            for (inner_mode, inner_name_and_kind) in inner_def.all_operands_with_names() {
                if inner_mode == spec::OperandMode::Optional && self.is_exhausted() {
                    break;
                }

                self.out.tokens.push(Token::Punctuation(if first { "(" } else { ", " }));
                first = false;

                let (inner_name, inner_kind) = inner_name_and_kind.name_and_kind();
                self.operand(inner_name, inner_kind);
            }
            if !first {
                self.out.tokens.push(Token::Punctuation(")"));
            }
            return;
        } else if kind == self.wk.LiteralString {
            // FIXME(eddyb) deduplicate with `spv::extract_literal_string`.
            let bytes: SmallVec<[u8; 64]> = words
                .into_iter()
                .flat_map(u32::to_le_bytes)
                .take_while(|&byte| byte != 0)
                .collect();
            match str::from_utf8(&bytes) {
                Ok(s) => Token::StringLiteral(format!("{s:?}")),
                Err(e) => Token::Error(format!("/* {e} in {bytes:?} */")),
            }
        } else {
            let mut words_msb_to_lsb =
                words.into_iter().rev().skip_while(|&word| word == 0).peekable();
            let most_significant_word = words_msb_to_lsb.next().unwrap_or(0);

            // FIXME(eddyb) use a more advanced decision procedure for picking
            // how to print integer(?) literals.
            let mut s;
            if words_msb_to_lsb.peek().is_none() && most_significant_word <= 0xffff {
                s = format!("{most_significant_word}");
            } else {
                s = format!("0x{most_significant_word:x}");
                for word in words_msb_to_lsb {
                    write!(s, "_{word:08x}").unwrap();
                }
            }
            Token::NumericLiteral(s)
        };

        self.out.tokens.push(literal_token);
    }

    fn operand(&mut self, operand_name: &'static str, kind: spec::OperandKind) {
        if !operand_name.is_empty() {
            self.out.tokens.push(Token::OperandName(operand_name));
        }

        let (name, def) = kind.name_and_def();

        // FIXME(eddyb) should this be a hard error?
        let emit_missing_error = |this: &mut Self| {
            this.out.tokens.push(Token::Error(format!("/* missing {name} */")));
        };

        let mut maybe_get_enum_word = || match self.imms.next() {
            Some(spv::Imm::Short(found_kind, word)) => {
                assert_eq!(kind, found_kind);
                Some(word)
            }
            Some(spv::Imm::LongStart(..) | spv::Imm::LongCont(..)) => unreachable!(),
            None => None,
        };

        match def {
            spec::OperandKindDef::BitEnum { empty_name, bits } => {
                let word = match maybe_get_enum_word() {
                    Some(word) => word,
                    None => return emit_missing_error(self),
                };

                self.out.tokens.push(Token::OperandKindNamespacePrefix(name));
                if word == 0 {
                    self.out.tokens.push(Token::EnumerandName(empty_name));
                } else if let Some(bit_idx) = spec::BitIdx::of_single_set_bit(word) {
                    let (bit_name, bit_def) = bits.get_named(bit_idx).unwrap();
                    self.out.tokens.push(Token::EnumerandName(bit_name));
                    self.enumerant_params(bit_def);
                } else {
                    self.out.tokens.push(Token::Punctuation("{"));
                    let mut first = true;
                    for bit_idx in spec::BitIdx::of_all_set_bits(word) {
                        if !first {
                            self.out.tokens.push(Token::Punctuation(", "));
                        }
                        first = false;

                        let (bit_name, bit_def) = bits.get_named(bit_idx).unwrap();
                        self.out.tokens.push(Token::EnumerandName(bit_name));
                        self.enumerant_params(bit_def);
                    }
                    self.out.tokens.push(Token::Punctuation("}"));
                }
            }
            spec::OperandKindDef::ValueEnum { variants } => {
                let word = match maybe_get_enum_word() {
                    Some(word) => word,
                    None => return emit_missing_error(self),
                };

                let (variant_name, variant_def) =
                    variants.get_named(word.try_into().unwrap()).unwrap();
                self.out.tokens.extend([
                    Token::OperandKindNamespacePrefix(name),
                    Token::EnumerandName(variant_name),
                ]);
                self.enumerant_params(variant_def);
            }
            spec::OperandKindDef::Id => match self.ids.next() {
                Some(id) => {
                    self.out.tokens.push(Token::Id(id));
                }
                None => emit_missing_error(self),
            },
            spec::OperandKindDef::Literal { .. } => {
                // FIXME(eddyb) there's no reason to take the first word now,
                // `self.literal(kind)` could do it itself.
                match self.imms.next() {
                    Some(
                        spv::Imm::Short(found_kind, word) | spv::Imm::LongStart(found_kind, word),
                    ) => {
                        assert_eq!(kind, found_kind);
                        self.literal(kind, word);
                    }
                    Some(spv::Imm::LongCont(..)) => unreachable!(),
                    None => emit_missing_error(self),
                }
            }
        }
    }

    fn inst_operands(mut self, opcode: spec::Opcode) -> impl Iterator<Item = TokensForOperand<ID>> {
        opcode.def().all_operands_with_names().map_while(move |(mode, name_and_kind)| {
            if mode == spec::OperandMode::Optional && self.is_exhausted() {
                return None;
            }
            let (name, kind) = name_and_kind.name_and_kind();
            self.operand(name, kind);
            Some(mem::take(&mut self.out))
        })
    }
}

/// Print a single SPIR-V operand from only immediates, potentially composed of
/// an enumerand with parameters (which consumes more immediates).
pub fn operand_from_imms<T>(imms: impl IntoIterator<Item = spv::Imm>) -> TokensForOperand<T> {
    let mut printer = OperandPrinter {
        wk: &spec::Spec::get().well_known,
        imms: imms.into_iter().peekable(),
        ids: iter::empty().peekable(),
        out: TokensForOperand::default(),
    };
    let &kind = match printer.imms.peek().unwrap() {
        spv::Imm::Short(kind, _) | spv::Imm::LongStart(kind, _) => kind,
        spv::Imm::LongCont(..) => unreachable!(),
    };
    printer.operand("", kind);
    assert!(printer.imms.next().is_none());
    printer.out
}

/// Group (ordered according to `opcode`) `imms` and `ids` into logical operands
/// (i.e. long immediates are unflattened) and produce one [`TokensForOperand`] by
/// printing each of them.
pub fn inst_operands<ID>(
    opcode: spec::Opcode,
    imms: impl IntoIterator<Item = spv::Imm>,
    ids: impl IntoIterator<Item = ID>,
) -> impl Iterator<Item = TokensForOperand<ID>> {
    OperandPrinter {
        wk: &spec::Spec::get().well_known,
        imms: imms.into_iter().peekable(),
        ids: ids.into_iter().peekable(),
        out: TokensForOperand::default(),
    }
    .inst_operands(opcode)
}
