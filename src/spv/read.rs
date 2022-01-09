//! Low-level parsing of SPIR-V binary form.

use crate::spv::{self, spec};
use owning_ref::{VecRef, VecRefMut};
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use std::borrow::Cow;
use std::num::NonZeroU32;
use std::path::Path;
use std::{fs, io, iter, mem, slice};

/// Defining instruction of an ID.
///
/// Used currently only to help parsing `LiteralContextDependentNumber`.
enum KnownIdDef {
    TypeInt(NonZeroU32),
    TypeFloat(NonZeroU32),
    Uncategorized {
        opcode: spec::Opcode,
        result_type_id: Option<spv::Id>,
    },
}

impl KnownIdDef {
    fn result_type_id(&self) -> Option<spv::Id> {
        match *self {
            Self::TypeInt(_) | Self::TypeFloat(_) => None,
            Self::Uncategorized { result_type_id, .. } => result_type_id,
        }
    }
}

// FIXME(eddyb) keep a `&'static spec::Spec` if that can even speed up anything.
struct InstParser<'a> {
    /// IDs defined so far in the module.
    known_ids: &'a FxHashMap<spv::Id, KnownIdDef>,

    /// Input words of an instruction.
    words: iter::Copied<slice::Iter<'a, u32>>,

    /// Output instruction, being parsed.
    inst: spv::Inst,
}

enum InstParseError {
    /// Ran out of words while parsing an instruction's operands.
    NotEnoughWords,

    /// Extra words were left over, after parsing an instruction's operands.
    TooManyWords,

    /// An illegal ID of `0`.
    IdZero,

    /// Unsupported enumerand value.
    UnsupportedEnumerand(spec::OperandKind, u32),

    /// An `IdResultType` ID referring to an ID not already defined.
    UnknownResultTypeId(spv::Id),

    /// The type of a `LiteralContextDependentNumber` could not be determined.
    MissingContextSensitiveLiteralType,

    /// The type of a `LiteralContextDependentNumber` was not a supported type
    /// (one of either `OpTypeInt` or `OpTypeFloat`).
    UnsupportedContextSensitiveLiteralType { type_opcode: spec::Opcode },
}

impl InstParseError {
    // FIXME(eddyb) improve messages and add more contextual information.
    fn message(&self) -> Cow<'static, str> {
        match *self {
            Self::NotEnoughWords => "truncated instruction".into(),
            Self::TooManyWords => "overlong instruction".into(),
            Self::IdZero => "ID %0 is illegal".into(),
            // FIXME(eddyb) deduplicate this with `spv::write`.
            Self::UnsupportedEnumerand(kind, word) => {
                let (name, def) = kind.name_and_def();
                match def {
                    spec::OperandKindDef::BitEnum { bits, .. } => {
                        let unsupported = spec::BitIdx::of_all_set_bits(word)
                            .filter(|&bit_idx| bits.get(bit_idx).is_none())
                            .fold(0u32, |x, i| x | (1 << i.0));
                        format!("unsupported {} bit-pattern 0x{:08x}", name, unsupported).into()
                    }

                    spec::OperandKindDef::ValueEnum { .. } => {
                        format!("unsupported {} value {}", name, word).into()
                    }

                    _ => unreachable!(),
                }
            }
            Self::UnknownResultTypeId(id) => {
                format!("ID %{} used as result type before definition", id).into()
            }
            Self::MissingContextSensitiveLiteralType => "missing type for literal".into(),
            Self::UnsupportedContextSensitiveLiteralType { type_opcode } => {
                format!("{} is not a supported literal type", type_opcode.name()).into()
            }
        }
    }
}

impl InstParser<'_> {
    fn is_exhausted(&self) -> bool {
        // FIXME(eddyb) use `self.words.is_empty()` when that is stabilized.
        self.words.len() == 0
    }

    fn enumerant_params(&mut self, enumerant: &spec::Enumerant) -> Result<(), InstParseError> {
        for (mode, kind) in enumerant.all_params() {
            if mode == spec::OperandMode::Optional {
                if self.is_exhausted() {
                    break;
                }
            }
            self.operand(kind)?;
        }

        Ok(())
    }

    fn operand(&mut self, kind: spec::OperandKind) -> Result<(), InstParseError> {
        use InstParseError as Error;

        let word = self.words.next().ok_or(Error::NotEnoughWords)?;
        match kind.def() {
            spec::OperandKindDef::BitEnum { bits, .. } => {
                self.inst.imms.push(spv::Imm::Short(kind, word));

                for bit_idx in spec::BitIdx::of_all_set_bits(word) {
                    let bit_def = bits
                        .get(bit_idx)
                        .ok_or(Error::UnsupportedEnumerand(kind, word))?;
                    self.enumerant_params(bit_def)?;
                }
            }

            spec::OperandKindDef::ValueEnum { variants } => {
                self.inst.imms.push(spv::Imm::Short(kind, word));

                let variant_def = u16::try_from(word)
                    .ok()
                    .and_then(|v| variants.get(v))
                    .ok_or(Error::UnsupportedEnumerand(kind, word))?;
                self.enumerant_params(variant_def)?;
            }

            spec::OperandKindDef::Id => {
                let id = word.try_into().map_err(|_| Error::IdZero)?;
                self.inst.ids.push(id);
            }

            spec::OperandKindDef::Literal {
                size: spec::LiteralSize::Word,
            } => {
                self.inst.imms.push(spv::Imm::Short(kind, word));
            }
            spec::OperandKindDef::Literal {
                size: spec::LiteralSize::NulTerminated,
            } => {
                let has_nul = |word: u32| word.to_le_bytes().contains(&0);
                if has_nul(word) {
                    self.inst.imms.push(spv::Imm::Short(kind, word));
                } else {
                    self.inst.imms.push(spv::Imm::LongStart(kind, word));
                    for word in &mut self.words {
                        self.inst.imms.push(spv::Imm::LongCont(kind, word));
                        if has_nul(word) {
                            break;
                        }
                    }
                }
            }
            spec::OperandKindDef::Literal {
                size: spec::LiteralSize::FromContextualType,
            } => {
                let contextual_type = self
                    .inst
                    .result_type_id
                    .or_else(|| {
                        // `OpSwitch` takes its literal type from the first operand.
                        let &id = self.inst.ids.get(0)?;
                        self.known_ids.get(&id)?.result_type_id()
                    })
                    .and_then(|id| self.known_ids.get(&id))
                    .ok_or(Error::MissingContextSensitiveLiteralType)?;

                let extra_word_count = match *contextual_type {
                    KnownIdDef::TypeInt(width) | KnownIdDef::TypeFloat(width) => {
                        // HACK(eddyb) `(width + 31) / 32 - 1` but without overflow.
                        (width.get() - 1) / 32
                    }
                    KnownIdDef::Uncategorized { opcode, .. } => {
                        return Err(Error::UnsupportedContextSensitiveLiteralType {
                            type_opcode: opcode,
                        });
                    }
                };

                if extra_word_count == 0 {
                    self.inst.imms.push(spv::Imm::Short(kind, word));
                } else {
                    self.inst.imms.push(spv::Imm::LongStart(kind, word));
                    for _ in 0..extra_word_count {
                        let word = self.words.next().ok_or(Error::NotEnoughWords)?;
                        self.inst.imms.push(spv::Imm::LongCont(kind, word));
                    }
                }
            }
        }

        Ok(())
    }

    fn inst(mut self, def: &spec::InstructionDef) -> Result<spv::Inst, InstParseError> {
        use InstParseError as Error;

        {
            // FIXME(eddyb) should this be a method?
            let mut id = || {
                self.words
                    .next()
                    .ok_or(Error::NotEnoughWords)?
                    .try_into()
                    .map_err(|_| Error::IdZero)
            };
            self.inst.result_type_id = def.has_result_type_id.then(|| id()).transpose()?;
            self.inst.result_id = def.has_result_id.then(|| id()).transpose()?;
        }

        if let Some(type_id) = self.inst.result_type_id {
            if !self.known_ids.contains_key(&type_id) {
                // FIXME(eddyb) also check that the ID is a valid type.
                return Err(Error::UnknownResultTypeId(type_id));
            }
        }

        for (mode, kind) in def.all_operands() {
            if mode == spec::OperandMode::Optional {
                if self.is_exhausted() {
                    break;
                }
            }
            self.operand(kind)?;
        }

        // The instruction must consume its entire word count.
        if !self.is_exhausted() {
            return Err(Error::TooManyWords);
        }

        Ok(self.inst)
    }
}

pub struct ModuleParser {
    /// Copy of the header words (for convenience).
    // FIXME(eddyb) add a `spec::Header` or `spv::Header` struct with named fields.
    pub header: [u32; spec::HEADER_LEN],

    /// Remaining (instructions') words in the module.
    words: VecRef<u8, [u32]>,

    /// IDs defined so far in the module.
    known_ids: FxHashMap<spv::Id, KnownIdDef>,
}

// FIXME(eddyb) stop abusing `io::Error` for error reporting.
fn invalid(reason: &str) -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        format!("malformed SPIR-V ({})", reason),
    )
}

impl ModuleParser {
    pub fn read_from_spv_file(path: impl AsRef<Path>) -> io::Result<Self> {
        let spv_spec = spec::Spec::get();

        let spv_bytes = VecRefMut::new(fs::read(path)?);
        if spv_bytes.len() % 4 != 0 {
            return Err(invalid("not a multiple of 4 bytes"));
        }
        let mut spv_words = {
            // FIXME(eddyb) find a safe wrapper crate for this.
            fn u8_slice_to_u32_slice_mut(xs: &mut [u8]) -> &mut [u32] {
                unsafe {
                    let (prefix, out, suffix) = xs.align_to_mut();
                    assert_eq!((prefix, suffix), (&mut [][..], &mut [][..]));
                    out
                }
            }
            spv_bytes.map_mut(u8_slice_to_u32_slice_mut)
        };

        if spv_words.len() < spec::HEADER_LEN {
            return Err(invalid("truncated header"));
        }

        // Check the magic, and swap endianness of all words if we have to.
        {
            let magic = spv_words[0];
            if magic == spv_spec.magic {
                // Nothing to do, all words already match native endianness.
            } else if magic.swap_bytes() == spv_spec.magic {
                for word in &mut spv_words[..] {
                    *word = word.swap_bytes();
                }
            } else {
                return Err(invalid("incorrect magic number"));
            }
        }

        Ok(Self {
            header: spv_words[..spec::HEADER_LEN].try_into().unwrap(),
            words: spv_words.map(|words| &words[spec::HEADER_LEN..]),

            known_ids: FxHashMap::default(),
        })
    }
}

impl Iterator for ModuleParser {
    type Item = io::Result<spv::Inst>;
    fn next(&mut self) -> Option<Self::Item> {
        let spv_spec = spec::Spec::get();
        let wk = &spv_spec.well_known;

        let &opcode = self.words.get(0)?;

        let (inst_len, opcode) = ((opcode >> 16) as usize, opcode as u16);

        let (opcode, inst_name, def) = match spec::Opcode::try_from_u16_with_name_and_def(opcode) {
            Some(opcode_name_and_def) => opcode_name_and_def,
            None => return Some(Err(invalid(&format!("unsupported opcode {}", opcode)))),
        };

        let invalid = |msg: &str| invalid(&format!("in {}: {}", inst_name, msg));

        if self.words.len() < inst_len {
            return Some(Err(invalid("truncated instruction")));
        }

        let parser = InstParser {
            known_ids: &self.known_ids,
            words: self.words[1..inst_len].iter().copied(),
            inst: spv::Inst {
                opcode,
                result_type_id: None,
                result_id: None,
                imms: SmallVec::new(),
                ids: SmallVec::new(),
            },
        };

        let inst = match parser.inst(def) {
            Ok(inst) => inst,
            Err(e) => return Some(Err(invalid(&e.message()))),
        };

        // HACK(eddyb) `Option::map` allows using `?` for `Result` in the closure.
        let maybe_known_id_result = inst.result_id.map(|id| {
            let known_id_def = if opcode == wk.OpTypeInt {
                KnownIdDef::TypeInt(match inst.imms[0] {
                    spv::Imm::Short(kind, n) => {
                        assert!(kind == wk.LiteralInteger);
                        n.try_into().map_err(|_| invalid("Width cannot be 0"))?
                    }
                    _ => unreachable!(),
                })
            } else if opcode == wk.OpTypeFloat {
                KnownIdDef::TypeFloat(match inst.imms[0] {
                    spv::Imm::Short(kind, n) => {
                        assert!(kind == wk.LiteralInteger);
                        n.try_into().map_err(|_| invalid("Width cannot be 0"))?
                    }
                    _ => unreachable!(),
                })
            } else {
                KnownIdDef::Uncategorized {
                    opcode,
                    result_type_id: inst.result_type_id,
                }
            };

            let old = self.known_ids.insert(id, known_id_def);
            if old.is_some() {
                return Err(invalid(&format!(
                    "ID %{} is a result of multiple instructions",
                    id
                )));
            }

            Ok(())
        });
        if let Some(Err(e)) = maybe_known_id_result {
            return Some(Err(e));
        }

        let empty_placeholder_vec_ref = VecRef::new(vec![]).map(|_| &[][..]);
        self.words = mem::replace(&mut self.words, empty_placeholder_vec_ref)
            .map(|words| &words[inst_len..]);

        Some(Ok(inst))
    }
}
