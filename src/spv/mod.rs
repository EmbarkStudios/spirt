use rustc_hash::FxHashSet;
use smallvec::SmallVec;
use std::borrow::Cow;
use std::path::Path;
use std::{fs, io, iter, slice, str};

pub mod spec;

// TODO(eddyb) have a way to generate "parsed instructions" out of the module,
// basically whatever would be the the basis for outputting words back out.
pub struct SpvModuleLayout {
    // FIXME(eddyb) parse the version in the header.
    pub header_version: u32,

    pub original_generator_magic: u32,
    pub original_id_bound: u32,
}

// FIXME(eddyb) keep a `&'static spec::Spec` if that can even speed up anything.
struct InstParser<'a> {
    /// IDs defined so far in the module.
    known_ids: &'a FxHashSet<super::SpvId>,

    /// Input words of an instruction.
    words: iter::Copied<slice::Iter<'a, u32>>,

    /// Output instruction, being parsed.
    inst: super::SpvInst,
}

/// Additional context for `OperandParser::operand`.
///
/// Used currently only to help parsing `LiteralContextDependentNumber`.
enum OperandContext {
    /// The operand is the only one in the instruction's definition (other than
    /// `IdResultType`/`IdResult`), and cannot be followed by more operands
    /// (other than its own parameters).
    SoleOperand,
}

enum InstParseError {
    /// Ran out of words while parsing an instruction's operands.
    NotEnoughWords,

    /// Extra words were left over, after parsing an instruction's operands.
    TooManyWords,

    /// An illegal ID of `0`.
    IdZero,

    /// An `IdResultType` ID referring to an ID not already defined.
    // FIXME(eddyb) this could also arise through unknown `OpType` instructions.
    UnknownResultTypeId(super::SpvId),

    /// Instruction may be valid, but contains an unexpected enumerand value.
    UnknownEnumerand,

    /// The general case of `LiteralContextDependentNumber`, TBD.
    UnimplementedContextSensitiveLiteral,
}

impl InstParseError {
    /// Only returns `Some(message)` if the error is guaranteed to be caused by
    /// an invalid SPIR-V module, and not a lack of support on our part.
    // FIXME(eddyb) improve messages and add more contextual information.
    fn is_unambiguously_invalid(&self) -> Option<Cow<'static, str>> {
        match *self {
            Self::NotEnoughWords => Some("truncated instruction".into()),
            Self::TooManyWords => Some("overlong instruction".into()),
            Self::IdZero => Some("ID %0 is illegal".into()),
            Self::UnknownResultTypeId(id) => {
                Some(format!("ID %{} used as result type before definition", id).into())
            }

            Self::UnknownEnumerand | Self::UnimplementedContextSensitiveLiteral => None,
        }
    }
}

impl InstParser<'_> {
    fn is_exhausted(&self) -> bool {
        // FIXME(eddyb) use `self.words.is_empty()` when that is stabilized.
        self.words.len() == 0
    }

    fn enumerant_params(&mut self, enumerant: &spec::Enumerant) -> Result<(), InstParseError> {
        for &kind in &enumerant.req_params {
            self.operand(kind, None)?;
        }

        if let Some(rest_kind) = enumerant.rest_params {
            while !self.is_exhausted() {
                self.operand(rest_kind, None)?;
            }
        }

        Ok(())
    }

    fn operand(
        &mut self,
        kind: spec::OperandKind,
        context: Option<OperandContext>,
    ) -> Result<(), InstParseError> {
        use InstParseError as Error;

        let word = self.words.next().ok_or(Error::NotEnoughWords)?;
        match kind.def() {
            spec::OperandKindDef::BitEnum { bits, .. } => {
                self.inst
                    .operands
                    .push(super::SpvOperand::ShortImm(kind, word));

                for bit_idx in spec::BitIdx::of_all_set_bits(word) {
                    let bit_def = bits.get(bit_idx).ok_or(Error::UnknownEnumerand)?;
                    self.enumerant_params(bit_def)?;
                }
            }

            spec::OperandKindDef::ValueEnum { variants } => {
                self.inst
                    .operands
                    .push(super::SpvOperand::ShortImm(kind, word));

                let variant_def = u16::try_from(word)
                    .ok()
                    .and_then(|v| variants.get(v))
                    .ok_or(Error::UnknownEnumerand)?;
                self.enumerant_params(variant_def)?;
            }

            spec::OperandKindDef::Id => {
                let id = word.try_into().map_err(|_| Error::IdZero)?;
                self.inst.operands.push(if self.known_ids.contains(&id) {
                    super::SpvOperand::Id(kind, id)
                } else {
                    super::SpvOperand::ForwardIdRef(kind, id)
                });
            }

            spec::OperandKindDef::Literal {
                size: spec::LiteralSize::Word,
            } => {
                self.inst
                    .operands
                    .push(super::SpvOperand::ShortImm(kind, word));
            }
            spec::OperandKindDef::Literal {
                size: spec::LiteralSize::NulTerminated,
            } => {
                let has_nul = |word: u32| word.to_le_bytes().contains(&0);
                if has_nul(word) {
                    self.inst
                        .operands
                        .push(super::SpvOperand::ShortImm(kind, word));
                } else {
                    self.inst
                        .operands
                        .push(super::SpvOperand::LongImmStart(kind, word));
                    for word in &mut self.words {
                        self.inst
                            .operands
                            .push(super::SpvOperand::LongImmCont(kind, word));
                        if has_nul(word) {
                            break;
                        }
                    }
                }
            }
            spec::OperandKindDef::Literal {
                size: spec::LiteralSize::FromContextualType,
            } => match context {
                // HACK(eddyb) the last operand can use up all remaining words.
                Some(OperandContext::SoleOperand) => {
                    if self.is_exhausted() {
                        self.inst
                            .operands
                            .push(super::SpvOperand::ShortImm(kind, word));
                    } else {
                        self.inst
                            .operands
                            .push(super::SpvOperand::LongImmStart(kind, word));
                        for word in &mut self.words {
                            self.inst
                                .operands
                                .push(super::SpvOperand::LongImmCont(kind, word));
                        }
                    }
                }
                None => {
                    // FIXME(eddyb) implement context-sensitive literals fully.
                    return Err(Error::UnimplementedContextSensitiveLiteral);
                }
            },
        }

        Ok(())
    }

    fn inst(mut self, def: &spec::InstructionDef) -> Result<super::SpvInst, InstParseError> {
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
            if !self.known_ids.contains(&type_id) {
                return Err(Error::UnknownResultTypeId(type_id));
            }
        }

        for &kind in &def.req_operands {
            self.operand(
                kind,
                if def.req_operands.len() == 1
                    && def.opt_operands.is_empty()
                    && def.rest_operands.is_none()
                {
                    Some(OperandContext::SoleOperand)
                } else {
                    None
                },
            )?;
        }
        for &kind in &def.opt_operands {
            if self.is_exhausted() {
                break;
            }
            self.operand(kind, None)?;
        }
        if let Some(rest_unit) = &def.rest_operands {
            while !self.is_exhausted() {
                match *rest_unit {
                    spec::RestOperandsUnit::One(kind) => {
                        self.operand(kind, None)?;
                    }
                    spec::RestOperandsUnit::Two([a_kind, b_kind]) => {
                        self.operand(a_kind, None)?;
                        self.operand(b_kind, None)?;
                    }
                }
            }
        }

        // The instruction must consume its entire word count.
        if !self.is_exhausted() {
            return Err(Error::TooManyWords);
        }

        Ok(self.inst)
    }
}

impl super::Module {
    pub fn read_from_spv_file(path: impl AsRef<Path>) -> io::Result<Self> {
        // FIXME(eddyb) stop abusing `io::Error` for error reporting.
        let invalid = |reason: &str| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!("malformed SPIR-V module ({})", reason),
            )
        };

        let spv_spec = spec::Spec::get();

        let mut spv_bytes = fs::read(path)?;
        if spv_bytes.len() % 4 != 0 {
            return Err(invalid("not a multiple of 4 bytes"));
        }
        let spv_words = {
            // FIXME(eddyb) find a safe wrapper crate for this.
            fn u8_slice_to_u32_slice_mut(xs: &mut [u8]) -> &mut [u32] {
                unsafe {
                    let (prefix, out, suffix) = xs.align_to_mut();
                    assert_eq!((prefix, suffix), (&mut [][..], &mut [][..]));
                    out
                }
            }
            u8_slice_to_u32_slice_mut(&mut spv_bytes)
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

        let (header, mut spv_words) = spv_words.split_at(spec::HEADER_LEN);

        let layout = {
            let &[magic, version, generator_magic, id_bound, reserved_inst_schema]: &[u32; spec::HEADER_LEN] =
                header.try_into().unwrap();

            // Ensure above (this is the value after any endianness swapping).
            assert_eq!(magic, spv_spec.magic);

            if reserved_inst_schema != 0 {
                return Err(invalid("unknown instruction schema - only 0 is supported"));
            }

            SpvModuleLayout {
                header_version: version,

                original_generator_magic: generator_magic,
                original_id_bound: id_bound,
            }
        };

        let mut known_ids = FxHashSet::default();

        let mut top_level = vec![];
        while let [opcode, ..] = spv_words {
            let (inst_len, opcode) = ((opcode >> 16) as usize, *opcode as u16);

            if spv_words.len() < inst_len {
                return Err(invalid("truncated instruction"));
            }

            let (inst_words, rest) = spv_words.split_at(inst_len);
            spv_words = rest;

            let operand_words = &inst_words[1..];
            if let Some(def) = spv_spec.instructions.get(opcode) {
                let parser = InstParser {
                    known_ids: &known_ids,
                    words: operand_words.iter().copied(),
                    inst: super::SpvInst {
                        opcode,
                        result_type_id: None,
                        result_id: None,
                        operands: SmallVec::new(),
                    },
                };

                match parser.inst(def) {
                    Ok(inst) => {
                        if let Some(id) = inst.result_id {
                            let is_new = known_ids.insert(id);
                            if !is_new {
                                return Err(invalid(&format!(
                                    "ID %{} is a result of multiple instructions",
                                    id
                                )));
                            }
                        }

                        top_level.push(super::TopLevel::SpvInst(inst));
                        continue;
                    }
                    Err(e) => {
                        if let Some(message) = e.is_unambiguously_invalid() {
                            return Err(invalid(&message));
                        }
                    }
                }
            }

            top_level.push(super::TopLevel::SpvUnknownInst {
                opcode,
                operands: operand_words.into(),
            });
        }

        Ok(Self {
            layout: super::ModuleLayout::Spv(layout),
            top_level,
        })
    }

    pub fn write_to_spv_file(&self, path: impl AsRef<Path>) -> io::Result<()> {
        let spv_spec = spec::Spec::get();
        let layout = match &self.layout {
            super::ModuleLayout::Spv(layout) => layout,

            #[allow(unreachable_patterns)]
            _ => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "not a SPIR-V module",
                ));
            }
        };
        let reserved_inst_schema = 0;

        // Start with the SPIR-V module header.
        let mut spv_words = vec![
            spv_spec.magic,
            layout.header_version,
            layout.original_generator_magic,
            // FIXME(eddyb) update this if the module has been modified.
            layout.original_id_bound,
            reserved_inst_schema,
        ];

        for top_level in &self.top_level {
            match top_level {
                super::TopLevel::SpvInst(inst) => {
                    let total_word_count = 1
                        + (inst.result_type_id.is_some() as usize)
                        + (inst.result_id.is_some() as usize)
                        + inst.operands.len();
                    let opcode = u32::from(inst.opcode)
                        | u32::from(u16::try_from(total_word_count).map_err(|_| {
                            io::Error::new(
                                io::ErrorKind::InvalidData,
                                "word count of SPIR-V instruction doesn't fit in 16 bits",
                            )
                        })?) << 16;
                    spv_words.extend(
                        iter::once(opcode)
                            .chain(inst.result_type_id.map(|id| id.get()))
                            .chain(inst.result_id.map(|id| id.get()))
                            .chain(inst.operands.iter().map(|operand| match *operand {
                                super::SpvOperand::ShortImm(_, word)
                                | super::SpvOperand::LongImmStart(_, word)
                                | super::SpvOperand::LongImmCont(_, word) => word,
                                super::SpvOperand::Id(_, id)
                                | super::SpvOperand::ForwardIdRef(_, id) => id.get(),
                            })),
                    );
                }
                super::TopLevel::SpvUnknownInst { opcode, operands } => {
                    let opcode = u32::from(*opcode)
                        | u32::from(u16::try_from(1 + operands.len()).map_err(|_| {
                            io::Error::new(
                                io::ErrorKind::InvalidData,
                                "word count of SPIR-V instruction doesn't fit in 16 bits",
                            )
                        })?) << 16;
                    spv_words.extend(iter::once(opcode).chain(operands.iter().copied()));
                }
            }
        }
        let spv_bytes = {
            // FIXME(eddyb) find a safe wrapper crate for this.
            fn u32_slice_to_u8_slice(xs: &[u32]) -> &[u8] {
                unsafe {
                    let (prefix, out, suffix) = xs.align_to();
                    assert_eq!((prefix, suffix), (&[][..], &[][..]));
                    out
                }
            }
            u32_slice_to_u8_slice(&spv_words)
        };
        fs::write(path, spv_bytes)
    }
}

// FIXME(eddyb) keep a `&'static spec::Spec` if that can even speed up anything.
pub struct OperandPrinter<'a, W> {
    /// Input operands to print from (may be grouped e.g. into literals).
    pub operands: slice::Iter<'a, super::SpvOperand>,

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
        while let Some(&super::SpvOperand::LongImmCont(cont_kind, word)) =
            self.operands.clone().next()
        {
            self.operands.next();
            assert!(kind == cont_kind);
            words.push(word);
        }

        let (name, def) = kind.name_and_def();
        assert!(matches!(def, spec::OperandKindDef::Literal { .. }));

        write!(self.out, "{}(", name)?;

        // HACK(eddyb) this shouldn't compare the `name` - but it's already here,
        // and this isn't exactly high-performance code anyway.
        if name == "LiteralString" {
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
            super::SpvOperand::ShortImm(kind, word) => {
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
            super::SpvOperand::LongImmStart(kind, word) => self.literal(kind, word),
            super::SpvOperand::LongImmCont(..) => unreachable!(),
            super::SpvOperand::Id(_, id) => write!(self.out, "%{}", id),
            super::SpvOperand::ForwardIdRef(_, id) => write!(self.out, "ForwardRef(%{})", id),
        }
    }

    pub fn all_operands(mut self) -> io::Result<()> {
        // FIXME(eddyb) use `!self.operands.is_empty()` when that is stabilized.
        while self.operands.len() != 0 {
            write!(self.out, " ")?;
            self.operand()?;
        }
        Ok(())
    }
}
