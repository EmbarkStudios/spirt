//! Pretty-printing SPIR-V operands.

use crate::spv::{self, spec};
use smallvec::SmallVec;
use std::borrow::Cow;
use std::fmt::Write;
use std::{iter, mem, str};

/// The smallest unit produced by printing a ("logical") SPIR-V operand.
///
/// All variants other than `Id` contain a fully formatted string, and the
/// distinction between variants can be erased to obtain a plain-text version.
//
// FIXME(eddyb) should there be a `TokenKind` enum and then `Cow<'static, str>`
// paired with a `TokenKind` in place of all of these individual variants?
pub enum Token<ID> {
    /// An inconsistency was detected in the operands to be printed.
    /// For stylistic consistency, the error message is always found wrapped in
    /// a block comment (i.e. the `String` is always of the form `"/* ... */"`).
    Error(String),

    // FIXME(eddyb) perhaps encode the hierarchical structure of e.g. enumerand
    // parameters, so that the SPIR-T printer can do layout for them.
    Punctuation(&'static str),

    OperandKindName(&'static str),
    EnumerandName(&'static str),

    NumericLiteral(String),
    StringLiteral(String),

    /// Unprinted ID operand, of its original type (allowing post-processing).
    Id(ID),
}

/// All the `Token`s outputted by printing one single ("logical") SPIR-V operand,
/// which may be concatenated (after separately processing `ID`s) to obtain a
/// complete plain-text version of the printed operand.
pub struct TokensForOperand<ID> {
    pub tokens: SmallVec<[Token<ID>; 3]>,
}

impl<ID> Default for TokensForOperand<ID> {
    fn default() -> Self {
        Self {
            tokens: SmallVec::new(),
        }
    }
}

impl TokensForOperand<String> {
    pub fn concat_to_plain_text(self) -> String {
        self.tokens
            .into_iter()
            .map(|token| -> Cow<str> {
                match token {
                    Token::Punctuation(s) | Token::OperandKindName(s) | Token::EnumerandName(s) => {
                        s.into()
                    }
                    Token::Error(s)
                    | Token::NumericLiteral(s)
                    | Token::StringLiteral(s)
                    | Token::Id(s) => s.into(),
                }
            })
            .reduce(|out, extra| (out.into_owned() + &extra).into())
            .unwrap_or_default()
            .into_owned()
    }
}

// FIXME(eddyb) keep a `&'static spec::Spec` if that can even speed up anything.
struct OperandPrinter<IMMS: Iterator<Item = spv::Imm>, ID, IDS: Iterator<Item = ID>> {
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
        for (mode, kind) in enumerant.all_params() {
            if mode == spec::OperandMode::Optional && self.is_exhausted() {
                break;
            }

            self.out
                .tokens
                .push(Token::Punctuation(if first { "(" } else { ", " }));
            first = false;

            self.operand(kind);
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
            assert!(kind == cont_kind);
            words.push(word);
        }

        let (name, def) = kind.name_and_def();
        assert!(matches!(def, spec::OperandKindDef::Literal { .. }));

        let literal_token = if kind == spec::Spec::get().well_known.LiteralString {
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
            let mut words_msb_to_lsb = words
                .into_iter()
                .rev()
                .skip_while(|&word| word == 0)
                .peekable();
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

        // FIXME(eddyb) decide when it's useful to show the kind of literal.
        let explicit_kind = false;

        if explicit_kind {
            self.out
                .tokens
                .extend([Token::OperandKindName(name), Token::Punctuation("(")]);
        }
        self.out.tokens.push(literal_token);
        if explicit_kind {
            self.out.tokens.push(Token::Punctuation(")"));
        }
    }

    fn operand(&mut self, kind: spec::OperandKind) {
        let (name, def) = kind.name_and_def();

        // FIXME(eddyb) should this be a hard error?
        let emit_missing_error = |this: &mut Self| {
            this.out
                .tokens
                .push(Token::Error(format!("/* missing {name} */")));
        };

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
                    None => return emit_missing_error(self),
                };

                self.out.tokens.push(Token::OperandKindName(name));
                if word == 0 {
                    self.out
                        .tokens
                        .extend([Token::Punctuation("."), Token::EnumerandName(empty_name)]);
                } else {
                    self.out.tokens.push(Token::Punctuation(".("));
                    let mut first = true;
                    for bit_idx in spec::BitIdx::of_all_set_bits(word) {
                        if !first {
                            self.out.tokens.push(Token::Punctuation(" | "));
                        }
                        first = false;

                        let (bit_name, bit_def) = bits.get_named(bit_idx).unwrap();
                        self.out
                            .tokens
                            .extend([Token::Punctuation("."), Token::EnumerandName(bit_name)]);
                        self.enumerant_params(bit_def);
                    }
                    self.out.tokens.push(Token::Punctuation(")"));
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
                    Token::OperandKindName(name),
                    Token::Punctuation("."),
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
                    Some(spv::Imm::Short(found_kind, word))
                    | Some(spv::Imm::LongStart(found_kind, word)) => {
                        assert!(kind == found_kind);
                        self.literal(kind, word);
                    }
                    Some(spv::Imm::LongCont(..)) => unreachable!(),
                    None => emit_missing_error(self),
                }
            }
        }
    }

    fn inst_operands(mut self, opcode: spec::Opcode) -> impl Iterator<Item = TokensForOperand<ID>> {
        opcode.def().all_operands().map_while(move |(mode, kind)| {
            if mode == spec::OperandMode::Optional && self.is_exhausted() {
                return None;
            }
            self.operand(kind);
            Some(mem::take(&mut self.out))
        })
    }
}

/// Print a single SPIR-V operand from only immediates, potentially composed of
/// an enumerand with parameters (which consumes more immediates).
// FIXME(eddyb) the return type should likely be `TokensForOperand<!>`.
pub fn operand_from_imms(imms: impl IntoIterator<Item = spv::Imm>) -> TokensForOperand<String> {
    let mut printer = OperandPrinter {
        imms: imms.into_iter().peekable(),
        ids: iter::empty().peekable(),
        out: TokensForOperand::default(),
    };
    let &kind = match printer.imms.peek().unwrap() {
        spv::Imm::Short(kind, _) | spv::Imm::LongStart(kind, _) => kind,
        spv::Imm::LongCont(..) => unreachable!(),
    };
    printer.operand(kind);
    assert!(printer.imms.next().is_none());
    printer.out
}

/// Group (ordered according to `opcode`) `imms` and `ids` into logical operands
/// (i.e. long immediates are unflattened) and produce one `TokensForOperand` by
/// printing each of them.
pub fn inst_operands<ID>(
    opcode: spec::Opcode,
    imms: impl IntoIterator<Item = spv::Imm>,
    ids: impl IntoIterator<Item = ID>,
) -> impl Iterator<Item = TokensForOperand<ID>> {
    OperandPrinter {
        imms: imms.into_iter().peekable(),
        ids: ids.into_iter().peekable(),
        out: TokensForOperand::default(),
    }
    .inst_operands(opcode)
}
