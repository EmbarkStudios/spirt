use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use std::borrow::Cow;
use std::num::NonZeroU32;
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

    // FIXME(eddyb) this could be an `IndexSet` if not for duplicates.
    pub capabilities: Vec<u32>,
}

/// Defining instruction of an ID.
///
/// Used currently only to help parsing `LiteralContextDependentNumber`.
enum KnownIdDef {
    TypeInt(NonZeroU32),
    TypeFloat(NonZeroU32),
    Uncategorized {
        opcode: u16,
        result_type_id: Option<super::SpvId>,
    },
}

impl KnownIdDef {
    fn result_type_id(&self) -> Option<super::SpvId> {
        match *self {
            Self::TypeInt(_) | Self::TypeFloat(_) => None,
            Self::Uncategorized { result_type_id, .. } => result_type_id,
        }
    }
}

// FIXME(eddyb) keep a `&'static spec::Spec` if that can even speed up anything.
struct InstParser<'a> {
    /// IDs defined so far in the module.
    known_ids: &'a FxHashMap<super::SpvId, KnownIdDef>,

    /// Input words of an instruction.
    words: iter::Copied<slice::Iter<'a, u32>>,

    /// Output instruction, being parsed.
    inst: super::SpvInst,
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
    UnknownResultTypeId(super::SpvId),

    /// The type of a `LiteralContextDependentNumber` could not be determined.
    MissingContextSensitiveLiteralType,

    /// The type of a `LiteralContextDependentNumber` was not a supported type
    /// (one of either `OpTypeInt` or `OpTypeFloat`).
    UnsupportedContextSensitiveLiteralType { type_opcode: u16 },
}

impl InstParseError {
    // FIXME(eddyb) improve messages and add more contextual information.
    fn message(&self) -> Cow<'static, str> {
        match *self {
            Self::NotEnoughWords => "truncated instruction".into(),
            Self::TooManyWords => "overlong instruction".into(),
            Self::IdZero => "ID %0 is illegal".into(),
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
            Self::UnsupportedContextSensitiveLiteralType { type_opcode } => format!(
                "{} is not a supported literal type",
                spec::Spec::get()
                    .instructions
                    .get_named(type_opcode)
                    .unwrap()
                    .0
            )
            .into(),
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
            self.operand(kind)?;
        }

        if let Some(rest_kind) = enumerant.rest_params {
            while !self.is_exhausted() {
                self.operand(rest_kind)?;
            }
        }

        Ok(())
    }

    fn operand(&mut self, kind: spec::OperandKind) -> Result<(), InstParseError> {
        use InstParseError as Error;

        let word = self.words.next().ok_or(Error::NotEnoughWords)?;
        match kind.def() {
            spec::OperandKindDef::BitEnum { bits, .. } => {
                self.inst
                    .operands
                    .push(super::SpvOperand::ShortImm(kind, word));

                for bit_idx in spec::BitIdx::of_all_set_bits(word) {
                    let bit_def = bits
                        .get(bit_idx)
                        .ok_or(Error::UnsupportedEnumerand(kind, word))?;
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
                    .ok_or(Error::UnsupportedEnumerand(kind, word))?;
                self.enumerant_params(variant_def)?;
            }

            spec::OperandKindDef::Id => {
                let id = word.try_into().map_err(|_| Error::IdZero)?;
                self.inst
                    .operands
                    .push(if self.known_ids.contains_key(&id) {
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
            } => {
                let contextual_type = self
                    .inst
                    .result_type_id
                    .or_else(|| {
                        // `OpSwitch` takes its literal type from the first operand.
                        match self.inst.operands.get(0)? {
                            super::SpvOperand::Id(_, id) => {
                                self.known_ids.get(&id)?.result_type_id()
                            }
                            _ => None,
                        }
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
                        })
                    }
                };

                if extra_word_count == 0 {
                    self.inst
                        .operands
                        .push(super::SpvOperand::ShortImm(kind, word));
                } else {
                    self.inst
                        .operands
                        .push(super::SpvOperand::LongImmStart(kind, word));
                    for _ in 0..extra_word_count {
                        let word = self.words.next().ok_or(Error::NotEnoughWords)?;
                        self.inst
                            .operands
                            .push(super::SpvOperand::LongImmCont(kind, word));
                    }
                }
            }
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
            if !self.known_ids.contains_key(&type_id) {
                // FIXME(eddyb) also check that the ID is a valid type.
                return Err(Error::UnknownResultTypeId(type_id));
            }
        }

        for &kind in &def.req_operands {
            self.operand(kind)?;
        }
        for &kind in &def.opt_operands {
            if self.is_exhausted() {
                break;
            }
            self.operand(kind)?;
        }
        if let Some(rest_unit) = &def.rest_operands {
            while !self.is_exhausted() {
                match *rest_unit {
                    spec::RestOperandsUnit::One(kind) => {
                        self.operand(kind)?;
                    }
                    spec::RestOperandsUnit::Two([a_kind, b_kind]) => {
                        self.operand(a_kind)?;
                        self.operand(b_kind)?;
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

        let mut layout = {
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

                capabilities: vec![],
            }
        };

        #[derive(Copy, Clone, Debug, PartialEq, PartialOrd)]
        enum Seq {
            Capability,
            Other,
        }
        let mut seq = None;

        let mut known_ids = FxHashMap::default();

        let mut top_level = vec![];
        while let &[opcode, ..] = spv_words {
            let (inst_len, opcode) = ((opcode >> 16) as usize, opcode as u16);

            let (inst_name, def) = spv_spec
                .instructions
                .get_named(opcode)
                .ok_or_else(|| invalid(&format!("unsupported opcode {}", opcode)))?;

            let invalid = |msg: &str| invalid(&format!("in {}: {}", inst_name, msg));

            if spv_words.len() < inst_len {
                return Err(invalid("truncated instruction"));
            }

            let (inst_words, rest) = spv_words.split_at(inst_len);
            spv_words = rest;

            let parser = InstParser {
                known_ids: &known_ids,
                words: inst_words[1..].iter().copied(),
                inst: super::SpvInst {
                    opcode,
                    result_type_id: None,
                    result_id: None,
                    operands: SmallVec::new(),
                },
            };

            let inst = parser.inst(def).map_err(|e| invalid(&e.message()))?;

            if let Some(id) = inst.result_id {
                let known_id_def = if opcode == spv_spec.well_known.op_type_int {
                    KnownIdDef::TypeInt(match inst.operands[0] {
                        super::SpvOperand::ShortImm(_, n) => {
                            n.try_into().map_err(|_| invalid("Width cannot be 0"))?
                        }
                        _ => unreachable!(),
                    })
                } else if opcode == spv_spec.well_known.op_type_float {
                    KnownIdDef::TypeFloat(match inst.operands[0] {
                        super::SpvOperand::ShortImm(_, n) => {
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

                let old = known_ids.insert(id, known_id_def);
                if old.is_some() {
                    return Err(invalid(&format!(
                        "ID %{} is a result of multiple instructions",
                        id
                    )));
                }
            }

            let next_seq = if opcode == spv_spec.well_known.op_capability {
                assert!(inst.result_type_id.is_none() && inst.result_id.is_none());
                match inst.operands[..] {
                    [super::SpvOperand::ShortImm(kind, cap)] => {
                        assert!(kind == spv_spec.well_known.capability);
                        layout.capabilities.push(cap);
                    }
                    _ => unreachable!(),
                }
                Seq::Capability
            } else {
                top_level.push(super::TopLevel::SpvInst(inst));
                Seq::Other
            };
            if !(seq <= Some(next_seq)) {
                return Err(invalid(&format!(
                    "out of order: {:?} instructions must precede {:?} instructions",
                    next_seq, seq
                )));
            }
            seq = Some(next_seq);
        }

        Ok(Self {
            layout: super::ModuleLayout::Spv(layout),
            top_level,
        })
    }
}

impl SpvModuleLayout {
    pub fn capability_insts(&self) -> impl Iterator<Item = super::SpvInst> + '_ {
        let spec::WellKnown {
            op_capability,
            capability,
            ..
        } = spec::Spec::get().well_known;
        self.capabilities.iter().map(move |&cap| super::SpvInst {
            opcode: op_capability,
            result_type_id: None,
            result_id: None,
            operands: iter::once(super::SpvOperand::ShortImm(capability, cap)).collect(),
        })
    }
}

impl super::Module {
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
        let mut push_inst = |inst: &super::SpvInst| -> io::Result<()> {
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
                        super::SpvOperand::Id(_, id) | super::SpvOperand::ForwardIdRef(_, id) => {
                            id.get()
                        }
                    })),
            );
            Ok(())
        };

        for cap_inst in layout.capability_insts() {
            push_inst(&cap_inst)?;
        }
        for top_level in &self.top_level {
            match top_level {
                super::TopLevel::SpvInst(inst) => push_inst(inst)?,
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
