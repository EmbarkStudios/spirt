use arrayvec::ArrayVec;
use lazy_static::lazy_static;
use rustc_hash::FxHashMap;
use std::iter;

use self::indexed::FlatIdx as _;

pub const HEADER_LEN: usize = 5;

pub struct Spec {
    pub magic: u32,

    /// Pre-cached IDs for "well-known" names.
    pub well_known: WellKnown,

    pub instructions: indexed::NamedIdxMap<Opcode, InstructionDef, indexed::KhrSegmented>,

    pub operand_kinds: indexed::NamedIdxMap<OperandKind, OperandKindDef, indexed::Flat>,
}

macro_rules! def_well_known {
    ($($group:ident: $ty:ty = [$($entry:ident),+ $(,)?]),+ $(,)?) => {
        // FIXME(eddyb) decide whether to split this type into one per-group.
        #[allow(non_snake_case)]
        pub struct WellKnown {
            $($(pub $entry: $ty,)+)+
        }

        #[allow(non_camel_case_types)]
        struct PerWellKnownGroup<$($group),+> {
            $($group: $group),+
        }

        impl WellKnown {
            fn lookup_with(lookup_fns: PerWellKnownGroup<$(impl Fn(&'static str) -> $ty),+>) -> Self {
                Self {
                    $($($entry: (lookup_fns.$group)(stringify!($entry)),)+)+
                }
            }
        }
    };
}

// FIXME(eddyb) maybe sort some of these groups alphabetically.
def_well_known! {
    opcode: Opcode = [
        OpCapability,
        OpExtension,
        OpExtInstImport,

        OpMemoryModel,

        OpEntryPoint,
        OpExecutionMode,
        OpExecutionModeId,

        OpString,
        OpSource,
        OpSourceContinued,
        OpSourceExtension,
        OpName,
        OpMemberName,
        OpModuleProcessed,

        OpDecorate,
        OpMemberDecorate,
        OpDecorateId,
        OpDecorateString,
        OpMemberDecorateString,

        OpLine,
        OpNoLine,

        OpTypeInt,
        OpTypeFloat,
        OpTypeForwardPointer,

        OpUndef,

        OpVariable,

        OpFunction,
        OpFunctionEnd,
        OpLabel,
    ],
    operand_kind: OperandKind = [
        Capability,
        AddressingModel,
        MemoryModel,
        SourceLanguage,
        StorageClass,
        FunctionControl,

        LiteralInteger,
        LiteralString,

        IdRef,
        IdResultType,
        IdResult,
    ],
    // FIXME(eddyb) find a way to namespace these to avoid conflicts.
    storage_class: u32 = [
        Function,
    ],
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Opcode(u16);

impl indexed::FlatIdx for Opcode {
    fn to_usize(self) -> usize {
        self.0.into()
    }
}

impl Opcode {
    /// Lookup the name & definition for `opcode` in the lazily-loaded `Spec`,
    /// returning `None` if it's not a known opcode.
    pub fn try_from_u16_with_name_and_def(
        opcode: u16,
    ) -> Option<(Self, &'static str, &'static InstructionDef)> {
        let opcode = Self(opcode);
        let (name, def) = Spec::get().instructions.get_named(opcode)?;
        Some((opcode, name, def))
    }

    pub fn as_u16(self) -> u16 {
        self.0
    }

    /// Lookup the name & definition for this opcode in the lazily-loaded `Spec`.
    #[inline]
    pub fn name_and_def(self) -> (&'static str, &'static InstructionDef) {
        Spec::get().instructions.get_named(self).unwrap()
    }

    /// Lookup the name for this opcode in the lazily-loaded `Spec`.
    #[inline]
    pub fn name(self) -> &'static str {
        self.name_and_def().0
    }

    /// Lookup the definition for this opcode in the lazily-loaded `Spec`.
    #[inline]
    pub fn def(self) -> &'static InstructionDef {
        self.name_and_def().1
    }
}

#[derive(PartialEq, Eq)]
pub struct InstructionDef {
    pub category: InstructionCategory,

    // FIXME(eddyb) consider nesting "Result Type ID" in "Result ID".
    pub has_result_type_id: bool,
    pub has_result_id: bool,

    pub req_operands: ArrayVec<OperandKind, 16>,
    pub opt_operands: ArrayVec<OperandKind, 2>,
    pub rest_operands: Option<RestOperandsUnit>,
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum InstructionCategory {
    Type,
    Const,
    Other,
}

/// Whether the trailing `*` "operand" (i.e. repeated arbitrarily many times),
/// consists of just one operand, or two per repeat (used by e.g. `OpPhi`).
#[derive(PartialEq, Eq)]
pub enum RestOperandsUnit {
    One(OperandKind),
    Two([OperandKind; 2]),
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct OperandKind(u8);

impl indexed::FlatIdx for OperandKind {
    fn to_usize(self) -> usize {
        self.0.into()
    }
}

impl OperandKind {
    /// Lookup the name & definition for this operand kind in the lazily-loaded `Spec`.
    #[inline]
    pub fn name_and_def(self) -> (&'static str, &'static OperandKindDef) {
        Spec::get().operand_kinds.get_named(self).unwrap()
    }

    /// Lookup the name for this operand kind in the lazily-loaded `Spec`.
    #[inline]
    pub fn name(self) -> &'static str {
        self.name_and_def().0
    }

    /// Lookup the definition for this operand kind in the lazily-loaded `Spec`.
    #[inline]
    pub fn def(self) -> &'static OperandKindDef {
        self.name_and_def().1
    }
}

pub enum OperandKindDef {
    BitEnum {
        empty_name: &'static str,
        bits: indexed::NamedIdxMap<BitIdx, Enumerant, indexed::FlatWithHoles>,
    },

    ValueEnum {
        variants: indexed::NamedIdxMap<u16, Enumerant, indexed::KhrSegmented>,
    },

    Id,
    Literal {
        size: LiteralSize,
    },
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct BitIdx(pub u8);

impl BitIdx {
    /// Returns `Some(BitIdx(i))` if and only if `x == (1 << i)`.
    pub fn of_single_set_bit(x: u32) -> Option<Self> {
        if x.is_power_of_two() {
            Some(Self(x.trailing_zeros() as u8))
        } else {
            None
        }
    }

    /// Returns an iterator of `BitIdx`s, from which `x` can be reconstructed
    /// by OR-ing together `1 << i` for every `BitIdx(i)`.
    ///
    /// The iterator is ordered: lower bit indices appear before higher ones.
    pub fn of_all_set_bits(mut x: u32) -> impl Iterator<Item = Self> {
        let mut consumed_bits = 0;
        iter::from_fn(move || {
            if x == 0 {
                None
            } else {
                let tz = x.trailing_zeros() as u8;
                let idx = Self(consumed_bits + tz);

                // Consume a sequence of bits `100...00`, where `tz` is just the
                // count of zeros, so `tz + 1` is the whole sequence's length.
                x >>= tz + 1;
                consumed_bits += tz + 1;

                Some(idx)
            }
        })
    }
}

impl indexed::FlatIdx for BitIdx {
    fn to_usize(self) -> usize {
        self.0.into()
    }
}

#[derive(PartialEq, Eq)]
pub struct Enumerant {
    pub req_params: ArrayVec<OperandKind, 4>,
    pub rest_params: Option<OperandKind>,
}

pub enum LiteralSize {
    /// The literal is always one word (but may occupy only part of it).
    Word,

    /// The literal is a word-encoded byte array, that ends with a `0` byte.
    NulTerminated,

    /// The literal uses as many words as required by its type, which is known
    /// contextually (`OpConstant`'s result type or `OpSwitch`'s selector type).
    FromContextualType,
}

impl Spec {
    /// Return a lazily-loaded `Spec` (only does significant work for the first call).
    #[inline(always)]
    pub fn get() -> &'static Spec {
        lazy_static! {
            static ref SPEC: Spec = {
                let raw_core_grammar: raw::CoreGrammar = serde_json::from_str(include_str!(
                    "../../khronos-spec/SPIRV-Headers/include/spirv/unified1/spirv.core.grammar.json"
                ))
                .unwrap();
                Spec::from_raw(raw_core_grammar)
            };
        }
        &SPEC
    }

    /// Implementation detail of `Spec::get`, indexes the raw data to produce a `Spec`.
    fn from_raw(raw_core_grammar: raw::CoreGrammar<'static>) -> Self {
        /// Helper for picking a name when the same index has multiple names.
        fn preferred_name_between_dups<'a>(a: &'a str, b: &'a str) -> &'a str {
            // Prefer standard / Khronos extensions over vendor extensions.
            let is_khr_and_vnd = |khr: &str, vnd: &str| {
                let base = khr.trim_end_matches("KHR");
                vnd.starts_with(base) && vnd.len() > base.len()
            };
            if is_khr_and_vnd(a, b) {
                a
            } else if is_khr_and_vnd(b, a) {
                b
            } else {
                // Worst case, use the first in alphabetical order.
                a.min(b)
            }
        }

        // Constructing the full `OperandKindDef` may require looking up other
        // `OperandKind`s by name, so build the lookup table for that up-front.
        let operand_kind_by_name: FxHashMap<_, _> = raw_core_grammar
            .operand_kinds
            .iter()
            .filter(|o| !matches!(o.category, raw::OperandKindCategory::Composite))
            .enumerate()
            .map(|(i, o)| (o.kind, OperandKind(i.try_into().unwrap())))
            .collect();

        let operand_kinds: Vec<_> = raw_core_grammar
            .operand_kinds
            .iter()
            .filter_map(|o| {
                let enumerant_from_raw = |e: &raw::OperandKindEnumerant| {
                    let mut all_params = e
                        .parameters
                        .iter()
                        .map(|p| (&p.quantifier, operand_kind_by_name[p.kind]));

                    let rest_params = match all_params.clone().next_back() {
                        Some((Some(raw::Quantifier::Rest), kind)) => {
                            all_params.next_back();
                            Some(kind)
                        }
                        _ => None,
                    };
                    let req_params = all_params
                        .map(|(quantifier, kind)| {
                            assert!(quantifier.is_none());
                            kind
                        })
                        .collect();

                    Enumerant {
                        req_params,
                        rest_params,
                    }
                };

                let def = match o.category {
                    raw::OperandKindCategory::BitEnum => {
                        assert!(o.bases.is_none());

                        let enumerants = o.enumerants.as_ref().unwrap();
                        let mut empty_name = None;
                        let mut bits = vec![];
                        for e in enumerants {
                            let new_name = e.enumerant;

                            // `BitEnum` enumerants with `"value" : "0x0000"`
                            // are only really provided to give a canonical name
                            // to the state with no bits set (usually `"None"`).
                            if e.value == 0 {
                                assert!(e.parameters.is_empty());

                                empty_name = Some(match empty_name {
                                    None => new_name,
                                    Some(prev_name) => {
                                        preferred_name_between_dups(prev_name, new_name)
                                    }
                                });

                                continue;
                            }

                            let new_enumerant = enumerant_from_raw(e);

                            let bit_idx = BitIdx::of_single_set_bit(e.value).unwrap();

                            // Make room for our new value, if necessary.
                            let i = bit_idx.to_usize();
                            if i >= bits.len() {
                                bits.resize_with(i + 1, || None);
                            }
                            let slot = &mut bits[i];

                            *slot = Some(match slot.take() {
                                None => (new_name, new_enumerant),
                                Some((prev_name, prev_enumerant)) => {
                                    // Only allow aliases that do not meaningfully differ.
                                    assert!(
                                        prev_enumerant == new_enumerant,
                                        "{} bits {} and {} share a bit index but differ in definition",
                                        o.kind,
                                        prev_name,
                                        new_name,
                                    );

                                    (
                                        preferred_name_between_dups(prev_name, new_name),
                                        new_enumerant,
                                    )
                                }
                            });
                        }

                        // FIXME(eddyb) automate this in `indexed::NamedIdxMap`.
                        let bits = indexed::NamedIdxMap {
                            idx_by_name: enumerants
                                .iter()
                                .filter_map(|e| {
                                    Some((e.enumerant, BitIdx::of_single_set_bit(e.value)?))
                                })
                                .collect(),
                            storage: bits,
                        };

                        OperandKindDef::BitEnum {
                            empty_name: empty_name.unwrap_or("None"),
                            bits,
                        }
                    }
                    raw::OperandKindCategory::ValueEnum => {
                        assert!(o.bases.is_none());

                        let enumerants = o.enumerants.as_ref().unwrap();
                        let variants = indexed::KhrSegmentedVec::from_in_order_iter(
                            enumerants.iter().map(|e| {
                                (
                                    e.value.try_into().unwrap(),
                                    (e.enumerant, enumerant_from_raw(e)),
                                )
                            }),
                            // `merge_duplicates` closure:
                            |(prev_name, prev_enumerant), (new_name, new_enumerant)| {
                                // Only allow aliases that do not meaningfully differ.
                                assert!(
                                    prev_enumerant == new_enumerant,
                                    "{} variants {} and {} share a value but differ in definition",
                                    o.kind,
                                    prev_name,
                                    new_name,
                                );

                                (
                                    preferred_name_between_dups(prev_name, new_name),
                                    new_enumerant,
                                )
                            },
                        );

                        // FIXME(eddyb) automate this in `indexed::NamedIdxMap`.
                        let variants = indexed::NamedIdxMap {
                            idx_by_name: enumerants
                                .iter()
                                .map(|e| (e.enumerant, e.value.try_into().unwrap()))
                                .collect(),
                            storage: variants,
                        };

                        OperandKindDef::ValueEnum { variants }
                    }
                    raw::OperandKindCategory::Id => {
                        assert!(o.enumerants.is_none() && o.bases.is_none());
                        OperandKindDef::Id
                    }
                    raw::OperandKindCategory::Literal => {
                        assert!(o.enumerants.is_none() && o.bases.is_none());
                        let size = match o.kind {
                            "LiteralInteger"
                            | "LiteralExtInstInteger"
                            | "LiteralSpecConstantOpInteger" => LiteralSize::Word,
                            "LiteralString" => LiteralSize::NulTerminated,
                            "LiteralContextDependentNumber" => LiteralSize::FromContextualType,
                            _ => unreachable!(),
                        };
                        OperandKindDef::Literal { size }
                    }
                    raw::OperandKindCategory::Composite => {
                        return None;
                    }
                };
                Some((o.kind, def))
            })
            .collect();

        // FIXME(eddyb) automate this in `indexed::NamedIdxMap`.
        assert_eq!(operand_kind_by_name.len(), operand_kinds.len());
        let operand_kinds = indexed::NamedIdxMap {
            idx_by_name: operand_kind_by_name,
            storage: operand_kinds,
        };

        let operand_kind_pairs_by_name: FxHashMap<_, _> = raw_core_grammar
            .operand_kinds
            .iter()
            .filter(|o| matches!(o.category, raw::OperandKindCategory::Composite))
            .map(|o| {
                assert!(o.enumerants.is_none());
                let mut bases: [_; 2] = o.bases.as_ref().unwrap()[..].try_into().unwrap();

                // HACK(eddyb) work around https://github.com/KhronosGroup/SPIRV-Headers/issues/38.
                if o.kind == "PairLiteralIntegerIdRef" {
                    assert_eq!(bases, ["LiteralInteger", "IdRef"]);
                    bases[0] = "LiteralContextDependentNumber";
                }

                (
                    o.kind,
                    [
                        operand_kinds.lookup(bases[0]).unwrap(),
                        operand_kinds.lookup(bases[1]).unwrap(),
                    ],
                )
            })
            .collect();

        let id_result_type = operand_kinds.lookup("IdResultType").unwrap();
        let id_result = operand_kinds.lookup("IdResult").unwrap();

        let instructions = indexed::KhrSegmentedVec::from_in_order_iter(
            raw_core_grammar.instructions.iter().map(|inst| {
                let mut def = InstructionDef {
                    category: match inst.class {
                        "Type-Declaration" => InstructionCategory::Type,
                        "Constant-Creation" => InstructionCategory::Const,
                        _ => InstructionCategory::Other,
                    },

                    has_result_type_id: false,
                    has_result_id: false,

                    req_operands: ArrayVec::new(),
                    opt_operands: ArrayVec::new(),
                    rest_operands: None,
                };

                #[derive(Copy, Clone, Debug, PartialEq, PartialOrd)]
                enum Seq {
                    IdResultType,
                    IdResult,
                    Required,
                    Optional,
                    Rest,
                }
                let mut seq = None;

                for o in &inst.operands {
                    let single = operand_kinds.lookup(o.kind);

                    let next_seq = match o.quantifier {
                        _ if single == Some(id_result_type) => {
                            assert!(matches!(o.quantifier, None));
                            assert!(!def.has_result_type_id);
                            def.has_result_type_id = true;
                            Seq::IdResultType
                        }
                        _ if single == Some(id_result) => {
                            assert!(matches!(o.quantifier, None));
                            assert!(!def.has_result_id);
                            def.has_result_id = true;
                            Seq::IdResult
                        }
                        None => {
                            def.req_operands.push(single.unwrap());
                            Seq::Required
                        }
                        Some(raw::Quantifier::Optional) => {
                            def.opt_operands.push(single.unwrap());
                            Seq::Optional
                        }
                        Some(raw::Quantifier::Rest) => {
                            def.rest_operands = Some(match single {
                                Some(kind) => RestOperandsUnit::One(kind),
                                None => RestOperandsUnit::Two(operand_kind_pairs_by_name[o.kind]),
                            });
                            Seq::Rest
                        }
                    };
                    assert!(seq <= Some(next_seq), "{:?} -> {:?}", next_seq, seq);
                    seq = Some(next_seq);
                }

                // `IdResultType` without `IdResult` is impossible.
                assert!(!(def.has_result_type_id && !def.has_result_id));

                (inst.opcode, (inst.opname, def))
            }),
            // `merge_duplicates` closure:
            |(prev_name, prev_def), (new_name, new_def)| {
                // Only allow aliases that do not meaningfully differ.
                assert!(
                    prev_def == new_def,
                    "instructions {} and {} share an opcode but differ in definition",
                    prev_name,
                    new_name,
                );

                (preferred_name_between_dups(prev_name, new_name), new_def)
            },
        );

        // FIXME(eddyb) automate this in `indexed::NamedIdxMap`.
        let instructions = indexed::NamedIdxMap {
            idx_by_name: raw_core_grammar
                .instructions
                .iter()
                .map(|inst| (inst.opname, Opcode(inst.opcode)))
                .collect(),
            storage: instructions,
        };

        let storage_classes = match &operand_kinds[operand_kinds.lookup("StorageClass").unwrap()] {
            OperandKindDef::ValueEnum { variants } => variants,
            _ => unreachable!(),
        };

        // FIXME(eddyb) if this is computed earlier, `IdResultType` and `IdResult`
        // wouldn't be looked up twice - but for now, this is mildly cleaner.
        let well_known = WellKnown::lookup_with(PerWellKnownGroup {
            opcode: |name| instructions.lookup(name).unwrap(),
            operand_kind: |name| operand_kinds.lookup(name).unwrap(),
            storage_class: |name| storage_classes.lookup(name).unwrap().into(),
        });

        Self {
            magic: raw_core_grammar.magic_number,

            instructions,
            well_known,
            operand_kinds,
        }
    }
}

/// Deserialization for the `.grammar.json` files, without any post-processing.
pub mod raw {
    use serde::Deserialize;
    use smallvec::SmallVec;
    use std::borrow::Cow;

    #[derive(Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct CoreGrammar<'a> {
        #[serde(borrow)]
        pub copyright: Vec<Cow<'a, str>>,

        #[serde(deserialize_with = "dew_u32_maybe_hex")]
        pub magic_number: u32,

        pub major_version: u8,
        pub minor_version: u8,
        pub revision: u8,

        pub instruction_printing_class: Vec<InstructionPrintingClass<'a>>,
        pub instructions: Vec<Instruction<'a>>,
        pub operand_kinds: Vec<OperandKind<'a>>,
    }

    #[derive(Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct InstructionPrintingClass<'a> {
        pub tag: &'a str,
        pub heading: Option<&'a str>,
    }

    #[derive(Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct Instruction<'a> {
        pub opname: &'a str,
        pub class: &'a str,
        pub opcode: u16,
        #[serde(default)]
        pub operands: Vec<Operand<'a>>,

        #[serde(default)]
        pub extensions: SmallVec<[&'a str; 1]>,
        #[serde(default)]
        pub capabilities: SmallVec<[&'a str; 1]>,

        pub version: Option<&'a str>,
        #[serde(rename = "lastVersion")]
        pub last_version: Option<&'a str>,
    }

    #[derive(Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct Operand<'a> {
        pub kind: &'a str,
        pub quantifier: Option<Quantifier>,
        pub name: Option<Cow<'a, str>>,
    }

    #[derive(Deserialize)]
    pub enum Quantifier {
        #[serde(rename = "?")]
        Optional,

        #[serde(rename = "*")]
        Rest,
    }

    #[derive(Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct OperandKind<'a> {
        pub category: OperandKindCategory,
        pub kind: &'a str,
        pub doc: Option<&'a str>,

        pub enumerants: Option<Vec<OperandKindEnumerant<'a>>>,

        pub bases: Option<Vec<&'a str>>,
    }

    #[derive(Deserialize)]
    pub enum OperandKindCategory {
        BitEnum,
        ValueEnum,

        Id,
        Literal,
        Composite,
    }

    #[derive(Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct OperandKindEnumerant<'a> {
        pub enumerant: &'a str,

        #[serde(deserialize_with = "dew_u32_maybe_hex")]
        pub value: u32,

        #[serde(default)]
        pub parameters: Vec<Operand<'a>>,

        #[serde(default)]
        pub extensions: SmallVec<[&'a str; 1]>,
        #[serde(default)]
        pub capabilities: SmallVec<[&'a str; 1]>,

        pub version: Option<&'a str>,
        #[serde(rename = "lastVersion")]
        pub last_version: Option<&'a str>,
    }

    /// Helper to generate functions usable with `deserialize_with` (hence "dew"),
    /// that deserialize to an intermediary type, which is then passed through the
    /// supplied closure, which is allowed to error. This is similar to the serde
    /// attribute `#[serde(try_from = "...")]`, but that only works for whole types.
    macro_rules! dew_and_then {
        ($($name:ident: |$x:ident: $in_ty:ty| -> $out_ty:ty $body:block),* $(,)?) => {
            $(fn $name<'de, D>(deserializer: D) -> Result<$out_ty, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                let x = Deserialize::deserialize(deserializer)?;
                (|$x: $in_ty| -> Result<$out_ty, _> { $body })(x)
                    .map_err(serde::de::Error::custom)
            })*
        };
    }

    dew_and_then! {
        dew_u32_maybe_hex: |x: DecOrHex<u32>| -> u32 { x.try_into() },
    }

    #[derive(Deserialize)]
    #[serde(untagged)]
    pub enum DecOrHex<'a, T> {
        Dec(T),
        Hex(&'a str),
    }

    impl TryInto<u32> for DecOrHex<'_, u32> {
        type Error = &'static str;
        fn try_into(self) -> Result<u32, Self::Error> {
            Ok(match self {
                DecOrHex::Dec(x) => x,
                DecOrHex::Hex(s) => {
                    s.strip_prefix("0x")
                        .ok_or("DecOrHex string form doesn't start with 0x")?
                        .chars()
                        .try_fold(0u32, |r, c| {
                            // HACK(eddyb) this uses `checked_mul` because `checked_shl`
                            // doesn't handle information loss (bits being shifted off).
                            Ok(r.checked_mul(16).ok_or("DecOrHex hex overflow into u32")?
                                + c.to_digit(16)
                                    .ok_or("DecOrHex hex has non-hex-nibble character")?)
                        })?
                }
            })
        }
    }
}

/// Utilities for indexing data in a variety of ways (names, compact indices, etc.).
// FIXME(eddyb) move this out of here?
pub mod indexed {
    use rustc_hash::FxHashMap;
    use smallvec::SmallVec;

    pub trait StorageShape<I, T> {
        type Storage;
        fn get_by_idx(storage: &Self::Storage, idx: I) -> Option<&T>;
    }

    pub trait FlatIdx: Copy {
        fn to_usize(self) -> usize;
    }

    impl FlatIdx for u16 {
        fn to_usize(self) -> usize {
            self.into()
        }
    }

    /// Flat array (`Vec`) storage, likely used with compact indices.
    pub enum Flat {}

    impl<I: FlatIdx, T> StorageShape<I, T> for Flat {
        type Storage = Vec<T>;
        fn get_by_idx(storage: &Self::Storage, idx: I) -> Option<&T> {
            storage.get(idx.to_usize())
        }
    }

    /// Like `Flat`, but the `Vec` elements are wrapped in `Option`.
    pub enum FlatWithHoles {}

    impl<I: FlatIdx, T> StorageShape<I, T> for FlatWithHoles {
        type Storage = Vec<Option<T>>;
        fn get_by_idx(storage: &Self::Storage, idx: I) -> Option<&T> {
            storage.get(idx.to_usize())?.as_ref()
        }
    }

    /// Segmented sparse storage, taking advantage of Khronos' predictable
    /// reservation policy for SPIR-V instruction opcodes and `ValueEnum`s:
    /// * indices in `0..=4096` are reserved for the standard, and mostly
    ///   allocated without gaps (~84% density at the time of writing)
    /// * indices in `4096..` are allocated in blocks of `64`; while sparser
    ///   than the standard range, the blockiness allows some optimizations
    pub enum KhrSegmented {}

    /// Khronos-oriented segmented sparse array (see `KhrSegmented`).
    pub struct KhrSegmentedVec<T> {
        /// Concatenation of values for indices lower than `4096`, with values
        /// for indices in a `64`-sized/aligned block starting at/above `4096`.
        ///
        /// Gaps are present (as `None`), but only if there are more values at
        /// some point after the gap, in the `0..=4096` index range, or in the
        /// same `64`-sized/aligned block (i.e. tailing gaps are elided).
        flattened: Vec<Option<T>>,

        /// Starting indices in `flattened` for every `64`-sized/aligned block.
        ///
        /// For example, if an index `i >= 4096` is present, its value can be
        /// found at `flattened[block_starts[(i - 4096) / 64] + (i % 64)]`.
        block_starts: SmallVec<[u16; 8]>,
    }

    impl<T> KhrSegmentedVec<T> {
        /// If `idx` is not in an out-of-range block, returns the pair of a
        /// "segment range" and an "intra-segment index".
        ///
        /// For example, if an index `i` is present, then `idx_to_segmented(i)`
        /// will return `Some((seg_range, intra_seg_idx))`, and the value can be
        /// found at `flattened[seg_range][intra_seg_idx]`.
        fn idx_to_segmented(&self, idx: u16) -> Option<(std::ops::Range<usize>, usize)> {
            let (block, intra_seg_idx) = if let Some(in_blocks_idx) = idx.checked_sub(4096) {
                (Some(usize::from(in_blocks_idx / 64)), idx % 64)
            } else {
                (None, idx)
            };
            let next_block = block.map_or(0, |b| b + 1);

            let seg_start = block.map_or(Some(0), |b| {
                self.block_starts.get(b).copied().map(usize::from)
            })?;
            let seg_end = self
                .block_starts
                .get(next_block)
                .copied()
                .map_or(self.flattened.len(), usize::from);

            Some((seg_start..seg_end, usize::from(intra_seg_idx)))
        }

        /// Add a new value, with an index greater than all previous indices.
        ///
        /// An exception is made for duplicates, which have to be handled by the
        /// `merge_duplicates` closure, instead of being outright disallowed.
        fn insert_in_order(&mut self, idx: u16, value: T, merge_duplicates: impl Fn(T, T) -> T) {
            let last_idx_plus_one = self.block_starts.len().checked_sub(1).map_or(
                self.flattened.len(),
                |last_block_idx| {
                    4096 + 64 * last_block_idx
                        + (self.flattened.len() - usize::from(self.block_starts[last_block_idx]))
                },
            );
            if let Some(last_idx) = last_idx_plus_one.checked_sub(1) {
                // HACK(eddyb) the condition being `<` instead of `<=` allows
                // for special handling of duplicates (via `merge_duplicates`).
                if usize::from(idx) < last_idx {
                    panic!(
                        "KhrSegmentedVec::insert_in_order: out of order indices ({} after {})",
                        idx, last_idx,
                    );
                }
            }

            // Reserve new blocks if needed (so `idx_to_segmented` can't fail).
            if let Some(block) = idx.checked_sub(4096).map(|i| i / 64) {
                let needed_blocks = usize::from(block).checked_add(1).unwrap();
                if needed_blocks > self.block_starts.len() {
                    self.block_starts
                        .resize(needed_blocks, self.flattened.len().try_into().unwrap());
                }
            }
            let (seg_range, intra_seg_idx) = self.idx_to_segmented(idx).unwrap();

            // The check at the start ensures we're never trying to insert in
            // an "already completed" segment.
            assert_eq!(seg_range.end, self.flattened.len());

            let slot_idx = seg_range.start + intra_seg_idx;
            let needed_slots = slot_idx.checked_add(1).unwrap();
            if needed_slots > self.flattened.len() {
                self.flattened.resize_with(needed_slots, || None);
            }
            let slot = &mut self.flattened[slot_idx];
            if let Some(prev) = slot.take() {
                *slot = Some(merge_duplicates(prev, value));
            } else {
                *slot = Some(value);
            }
        }

        /// Construct a `KhrSegmentedVec` out of an iterator with ordered indices.
        ///
        /// An exception is made for duplicates, which have to be handled by the
        /// `merge_duplicates` closure, instead of being outright disallowed.
        pub fn from_in_order_iter(
            it: impl IntoIterator<Item = (u16, T)>,
            merge_duplicates: impl Fn(T, T) -> T,
        ) -> Self {
            let iter = it.into_iter();

            let mut this = Self {
                flattened: Vec::with_capacity(
                    iter.size_hint().0.checked_next_power_of_two().unwrap_or(0),
                ),
                block_starts: SmallVec::new(),
            };

            for (idx, value) in iter {
                // FIXME(eddyb) the check at the start of `insert_in_order` may
                // be less efficient than if we checked the ordering here instead.
                this.insert_in_order(idx, value, &merge_duplicates);
            }

            this
        }
    }

    impl<I: FlatIdx, T> StorageShape<I, T> for KhrSegmented {
        type Storage = KhrSegmentedVec<T>;
        fn get_by_idx(storage: &Self::Storage, idx: I) -> Option<&T> {
            let (seg_range, intra_seg_idx) =
                storage.idx_to_segmented(idx.to_usize().try_into().ok()?)?;

            storage
                .flattened
                .get(seg_range)?
                .get(intra_seg_idx)?
                .as_ref()
        }
    }

    pub struct NamedIdxMap<I, T, S: StorageShape<I, (&'static str, T)>> {
        pub(super) idx_by_name: FxHashMap<&'static str, I>,
        pub(super) storage: S::Storage,
    }

    impl<I, T, S: StorageShape<I, (&'static str, T)>> NamedIdxMap<I, T, S> {
        /// Get an index from a name.
        pub fn lookup(&self, name: &str) -> Option<I>
        where
            I: Copy,
        {
            self.idx_by_name.get(name).copied()
        }

        pub fn get_named(&self, idx: I) -> Option<(&'static str, &T)> {
            let (name, value) = S::get_by_idx(&self.storage, idx)?;
            Some((name, value))
        }

        pub fn get(&self, idx: I) -> Option<&T> {
            let (_name, value) = self.get_named(idx)?;
            Some(value)
        }
    }

    impl<I, T, S: StorageShape<I, (&'static str, T)>> std::ops::Index<I> for NamedIdxMap<I, T, S> {
        type Output = T;
        fn index(&self, idx: I) -> &T {
            self.get(idx).unwrap()
        }
    }
}
