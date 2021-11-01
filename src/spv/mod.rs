use smallvec::SmallVec;
use std::collections::BTreeSet;
use std::iter;
use std::num::NonZeroU32;
use std::string::FromUtf8Error;

pub mod lift;
pub mod lower;
pub mod print;
pub mod read;
pub mod spec;
pub mod write;

pub struct Dialect {
    pub version_major: u8,
    pub version_minor: u8,

    pub original_generator_magic: u32,
    // FIXME(eddyb) always recompute this from the module.
    pub original_id_bound: u32,

    pub capabilities: BTreeSet<u32>,
    pub extensions: BTreeSet<String>,
}

pub struct Inst {
    pub opcode: u16,

    // FIXME(eddyb) consider nesting "Result Type ID" in "Result ID".
    pub result_type_id: Option<Id>,
    pub result_id: Option<Id>,

    pub operands: SmallVec<[Operand; 2]>,
}

pub enum Operand {
    // FIXME(eddyb) this is a bit wasteful because we don't have to fit the
    // `OperandKind` of `Imm` in between the discriminant and the `u32`, but
    // hopefully `Operand` isn't that size-sensitive.
    Imm(Imm),

    Id(spec::OperandKind, Id),

    // FIXME(eddyb) reduce uses of this by addressing the situations it can
    // appear in, with dedicated IR constructs instead.
    // FIXME(eddyb) if SPIR-T won't use this directly, is there a point in even
    // distinguishing between forward and other references? lowering would still
    // need to track that on its own anyway.
    ForwardIdRef(spec::OperandKind, Id),
}

pub enum Imm {
    Short(spec::OperandKind, u32),
    LongStart(spec::OperandKind, u32),
    LongCont(spec::OperandKind, u32),
}

pub type Id = NonZeroU32;

// FIXME(eddyb) pick a "small string" crate, and fine-tune its inline size,
// instead of allocating a whole `String`.
/// Given a single `LiteralString` (as one `Imm::Short` or a `Imm::LongStart`
/// followed by some number of `Imm::LongCont` - will panic otherwise), returns a
/// Rust `String` if the literal is valid UTF-8, or the validation error otherwise.
fn extract_literal_string(operands: &[Operand]) -> Result<String, FromUtf8Error> {
    let spv_spec = spec::Spec::get();

    let mut words = match *operands {
        [Operand::Imm(Imm::Short(kind, first_word))]
        | [Operand::Imm(Imm::LongStart(kind, first_word)), ..] => {
            assert!(kind == spv_spec.well_known.literal_string);
            iter::once(first_word).chain(operands[1..].iter().map(|operand| match *operand {
                Operand::Imm(Imm::LongCont(kind, word)) => {
                    assert!(kind == spv_spec.well_known.literal_string);
                    word
                }
                _ => unreachable!(),
            }))
        }
        _ => unreachable!(),
    };

    let mut bytes = Vec::with_capacity(operands.len() * 4);
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
fn encode_literal_string(s: &str) -> impl Iterator<Item = Operand> + '_ {
    let spv_spec = spec::Spec::get();

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
            let kind = spv_spec.well_known.literal_string;
            match (i, total_words) {
                (0, 1) => Operand::Imm(Imm::Short(kind, word)),
                (0, _) => Operand::Imm(Imm::LongStart(kind, word)),
                (_, _) => Operand::Imm(Imm::LongCont(kind, word)),
            }
        })
}
