//! SPIR-V support, mainly conversions to/from SPIR-T ([`lower`]/[`lift`]).

// NOTE(eddyb) all the modules are declared here, but they're documented "inside"
// (i.e. using inner doc comments).
pub mod lift;
pub mod lower;
pub mod print;
pub mod read;
pub mod spec;
pub mod write;

use crate::{FxIndexMap, InternedStr};
use smallvec::SmallVec;
use std::collections::{BTreeMap, BTreeSet};
use std::iter;
use std::num::NonZeroU32;
use std::string::FromUtf8Error;

/// Semantic properties of a SPIR-V module (not tied to any IDs).
#[derive(Clone)]
pub struct Dialect {
    pub version_major: u8,
    pub version_minor: u8,

    pub capabilities: BTreeSet<u32>,
    pub extensions: BTreeSet<String>,

    pub addressing_model: u32,
    pub memory_model: u32,
}

/// Non-semantic details (i.e. debuginfo) of a SPIR-V module (not tied to any IDs).
#[derive(Clone)]
pub struct ModuleDebugInfo {
    pub original_generator_magic: Option<NonZeroU32>,

    pub source_languages: BTreeMap<DebugSourceLang, DebugSources>,
    pub source_extensions: Vec<String>,
    pub module_processes: Vec<String>,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct DebugSourceLang {
    pub lang: u32,
    pub version: u32,
}

#[derive(Clone, Default)]
pub struct DebugSources {
    pub file_contents: FxIndexMap<InternedStr, String>,
}

/// A SPIR-V instruction, in its minimal form (opcode and immediate operands).
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Inst {
    pub opcode: spec::Opcode,

    // FIXME(eddyb) change the inline size of this to fit most instructions.
    // FIXME(eddyb) it might be worth investigating the performance implications
    // of interning "long immediates", compared to the flattened representation.
    // NOTE(eddyb) interning these separately is likely unnecessary in many cases,
    // now that `DataInstForm`s are interned, and `Const`s etc. were already.
    pub imms: SmallVec<[Imm; 2]>,
}

impl From<spec::Opcode> for Inst {
    fn from(opcode: spec::Opcode) -> Self {
        Self {
            opcode,
            imms: SmallVec::new(),
        }
    }
}

/// A full SPIR-V instruction (like [`Inst`], but including input/output ID operands).
pub struct InstWithIds {
    pub without_ids: Inst,

    // FIXME(eddyb) consider nesting "Result Type ID" in "Result ID".
    pub result_type_id: Option<Id>,
    pub result_id: Option<Id>,

    // FIXME(eddyb) change the inline size of this to fit most instructions.
    pub ids: SmallVec<[Id; 4]>,
}

// HACK(eddyb) access to `Inst` fields for convenience.
impl std::ops::Deref for InstWithIds {
    type Target = Inst;
    fn deref(&self) -> &Inst {
        &self.without_ids
    }
}
impl std::ops::DerefMut for InstWithIds {
    fn deref_mut(&mut self) -> &mut Inst {
        &mut self.without_ids
    }
}

/// SPIR-V immediate (one word, longer immediates are a sequence of multiple [`Imm`]s).
//
// FIXME(eddyb) consider replacing with a `struct` e.g.:
// `{ first: bool, last: bool, kind: OperandKind, word: u32 }`
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Imm {
    Short(spec::OperandKind, u32),
    LongStart(spec::OperandKind, u32),
    LongCont(spec::OperandKind, u32),
}

/// SPIR-V ID.
pub type Id = NonZeroU32;

// FIXME(eddyb) pick a "small string" crate, and fine-tune its inline size,
// instead of allocating a whole `String`.
//
/// Given a single `LiteralString` (as one [`Imm::Short`] or a [`Imm::LongStart`]
/// followed by some number of [`Imm::LongCont`] - will panic otherwise), returns a
/// Rust [`String`] if the literal is valid UTF-8, or the validation error otherwise.
fn extract_literal_string(imms: &[Imm]) -> Result<String, FromUtf8Error> {
    let wk = &spec::Spec::get().well_known;

    let mut words = match *imms {
        [Imm::Short(kind, first_word)] | [Imm::LongStart(kind, first_word), ..] => {
            assert_eq!(kind, wk.LiteralString);
            iter::once(first_word).chain(imms[1..].iter().map(|&imm| match imm {
                Imm::LongCont(kind, word) => {
                    assert_eq!(kind, wk.LiteralString);
                    word
                }
                _ => unreachable!(),
            }))
        }
        _ => unreachable!(),
    };

    let mut bytes = Vec::with_capacity(imms.len() * 4);
    while let Some(word) = words.next() {
        for byte in word.to_le_bytes() {
            if byte == 0 {
                assert!(words.next().is_none());
                return String::from_utf8(bytes);
            }
            bytes.push(byte);
        }
    }
    unreachable!("missing \\0 terminator in LiteralString");
}

// FIXME(eddyb) this shouldn't just panic when `s.contains('\0')`.
fn encode_literal_string(s: &str) -> impl Iterator<Item = Imm> + '_ {
    let wk = &spec::Spec::get().well_known;

    let bytes = s.as_bytes();

    // FIXME(eddyb) replace with `array_chunks` once that is stabilized.
    let full_words = bytes
        .chunks_exact(4)
        .map(|w| <[u8; 4]>::try_from(w).unwrap());

    let leftover_bytes = &bytes[full_words.len() * 4..];
    let mut last_word = [0; 4];
    last_word[..leftover_bytes.len()].copy_from_slice(leftover_bytes);

    let total_words = full_words.len() + 1;

    full_words
        .chain(iter::once(last_word))
        .map(u32::from_le_bytes)
        .enumerate()
        .map(move |(i, word)| {
            let kind = wk.LiteralString;
            match (i, total_words) {
                (0, 1) => Imm::Short(kind, word),
                (0, _) => Imm::LongStart(kind, word),
                (_, _) => Imm::LongCont(kind, word),
            }
        })
}
