//! SPIR-V support, mainly conversions to/from SPIR-T ([`lower`]/[`lift`]).

// NOTE(eddyb) all the modules are declared here, but they're documented "inside"
// (i.e. using inner doc comments).
pub mod canonical;
pub mod lift;
pub mod lower;
pub mod print;
pub mod read;
pub mod spec;
pub mod write;

use crate::{Context, FxIndexMap, InternedStr, Type, TypeDef, TypeKind, TypeOrConst};
use smallvec::SmallVec;
use std::collections::{BTreeMap, BTreeSet};
use std::iter;
use std::num::NonZeroU32;
use std::ops::Range;
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

/// Most SPIR-V types can be used as SPIR-V (SSA) value types, but some require
/// non-trivial lowering into SPIR-T [`Value`](crate::Value)s (e.g. expanding
/// one SPIR-V value into any number of *valid* SPIR-T values).
//
// FIXME(eddyb) aggregates without known leaf counts using `Direct` is worse than
// treating them as an error (and e.g. generating `Diag`s), but it's also simpler.
#[derive(Clone, Default, PartialEq, Eq, Hash)]
pub enum ValueLowering {
    /// SPIR-V values of this type map to SPIR-T [`Value`](crate::Value)s with the same type
    /// (see [`Value`](crate::Value) documentation for more details, and valid types).
    #[default]
    Direct,

    /// SPIR-V values of this type can't be kept intract in SPIR-T, but instead
    /// require decomposion into their "leaves", i.e. valid SPIR-T [`Value`](crate::Value)s.
    Disaggregate(AggregateShape),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum AggregateShape {
    Struct { per_field_leaf_range_end: SmallVec<[u32; 4]> },
    Array { fixed_len: u32, total_leaf_count: u32 },
}

impl AggregateShape {
    // FIXME(eddyb) force this to be used via some kind of forced canonicalization.
    pub fn compute(
        cx: &Context,
        spv_inst: &Inst,
        type_and_const_inputs: &[TypeOrConst],
    ) -> Option<Self> {
        let wk = &spec::Spec::get().well_known;

        if spv_inst.opcode == wk.OpTypeStruct {
            let mut leaf_count = 0u32;
            let mut per_field_leaf_range_end = SmallVec::new();
            for &ty_or_ct in type_and_const_inputs {
                let field_type = match ty_or_ct {
                    TypeOrConst::Type(ty) => ty,
                    TypeOrConst::Const(_) => return None,
                };
                let field_leaf_count = cx[field_type].disaggregated_leaf_count_u32();

                leaf_count = leaf_count.checked_add(field_leaf_count)?;
                per_field_leaf_range_end.push(leaf_count);
            }
            Some(Self::Struct { per_field_leaf_range_end })
        } else if spv_inst.opcode == wk.OpTypeArray {
            let (elem_type, len) = match type_and_const_inputs[..] {
                [TypeOrConst::Type(elem_type), TypeOrConst::Const(len)] => (elem_type, len),
                _ => return None,
            };

            // NOTE(eddyb) this can legally be `None` when the length of
            // the array is given by a specialization constant.
            let fixed_len = len.as_scalar(cx).and_then(|len| len.int_as_u32());
            let fixed_len = fixed_len?;

            let elem_leaf_count = cx[elem_type].disaggregated_leaf_count_u32();

            Some(Self::Array {
                fixed_len,
                total_leaf_count: elem_leaf_count.checked_mul(fixed_len)?,
            })
        } else {
            None
        }
    }
}

// FIXME(eddyb) not the best place to put these utilities, but they're used in
// both `spv::lower` and `spv::lift` (and they use private methods defined here).
// FIXME(eddyb) consider moving some of this to `spv::canonical`.
impl TypeDef {
    fn spv_value_lowering(&self) -> &ValueLowering {
        match &self.kind {
            TypeKind::Scalar(_)
            | TypeKind::Vector(_)
            | TypeKind::QPtr
            | TypeKind::SpvStringLiteralForExtInst => &ValueLowering::Direct,
            TypeKind::SpvInst { value_lowering, .. } => value_lowering,
        }
    }

    fn disaggregated_leaf_count(&self) -> usize {
        self.disaggregated_leaf_count_u32() as usize
    }

    fn disaggregated_leaf_count_u32(&self) -> u32 {
        match self.spv_value_lowering() {
            ValueLowering::Direct => 1,
            ValueLowering::Disaggregate(AggregateShape::Struct { per_field_leaf_range_end }) => {
                per_field_leaf_range_end.last().copied().unwrap_or(0)
            }
            &ValueLowering::Disaggregate(AggregateShape::Array { total_leaf_count, .. }) => {
                total_leaf_count
            }
        }
    }
}

/// Tree-like (preorder) traversal tool for [`ValueLowering::Disaggregate`] types.
struct AggregateCursor<'a> {
    cx: &'a Context,
    // FIXME(eddyb) should this cache any references into `&Context`?
    current: Type,
    parent_component_path: SmallVec<[(Type, u32); 8]>,
}

impl AggregateCursor<'_> {
    // HACK(eddyb) this returns `true` iff a new node was found.
    fn try_advance(&mut self) -> bool {
        // FIXME(eddyb) this isn't the best organization possible.
        let cx = self.cx;
        let get_component = move |ty: Type, idx: u32| -> Option<Type> {
            let ty_def = &cx[ty];
            let type_input_idx = match ty_def.spv_value_lowering() {
                ValueLowering::Direct => return None,
                ValueLowering::Disaggregate(AggregateShape::Struct { .. }) => idx,
                &ValueLowering::Disaggregate(AggregateShape::Array { fixed_len, .. }) => {
                    if idx >= fixed_len {
                        return None;
                    }
                    0
                }
            };
            let type_and_const_inputs = match &ty_def.kind {
                TypeKind::Scalar(_)
                | TypeKind::Vector(_)
                | TypeKind::QPtr
                | TypeKind::SpvStringLiteralForExtInst => &[][..],
                TypeKind::SpvInst { type_and_const_inputs, .. } => &type_and_const_inputs[..],
            };
            let expect_type = |ty_or_ct| match ty_or_ct {
                TypeOrConst::Type(ty) => ty,
                TypeOrConst::Const(_) => unreachable!(),
            };
            Some(expect_type(*type_and_const_inputs.get(usize::try_from(type_input_idx).ok()?)?))
        };

        // Try descending first, into the first child.
        if let Some(first_child_type) = get_component(self.current, 0) {
            self.parent_component_path.push((self.current, 0));
            self.current = first_child_type;
            return true;
        }

        // Try ascending until there is a next sibling to descend into, but only
        // modifying `self` iff any such node is found, otherwise calling this
        // method without checking its success, could result in infinite cycles.
        for depth in (0..self.parent_component_path.len()).rev() {
            let (ancestor_type, ancestor_child_idx) = &mut self.parent_component_path[depth];
            if let Some(sibling_idx) = ancestor_child_idx.checked_add(1) {
                if let Some(sibling_type) = get_component(*ancestor_type, sibling_idx) {
                    *ancestor_child_idx = sibling_idx;
                    self.current = sibling_type;
                    self.parent_component_path.truncate(depth + 1);
                    return true;
                }
            }
        }

        false
    }

    // FIXME(eddyb) can't find a great name for this - crucially, if this is a
    // leaf, it's a noop, it doesn't find the next leaf!
    // HACK(eddyb) this returns `true` iff a leaf node was found.
    fn try_ensure_at_leaf(&mut self) -> bool {
        loop {
            if let ValueLowering::Direct = self.cx[self.current].spv_value_lowering() {
                return true;
            }
            if !self.try_advance() {
                return false;
            }
        }
    }
}

/// Recursively flattening iterator for [`ValueLowering::Disaggregate`] types.
struct DisaggregatedLeafTypes<'a>(Option<AggregateCursor<'a>>);

impl Iterator for DisaggregatedLeafTypes<'_> {
    type Item = Type;

    fn size_hint(&self) -> (usize, Option<usize>) {
        // HACK(eddyb) only compute a size hint for the fresh iterator.
        if let Self(Some(cursor)) = self {
            if cursor.parent_component_path.is_empty() {
                let leaf_count = cursor.cx[cursor.current].disaggregated_leaf_count();
                return (leaf_count, Some(leaf_count));
            }
        }
        (0, None)
    }

    fn next(&mut self) -> Option<Type> {
        let cursor = self.0.as_mut()?;
        let next = cursor.try_ensure_at_leaf().then_some(cursor.current);

        // Record advancement failure, ensuring future calls to `next` return `None`.
        if !(next.is_some() && cursor.try_advance()) {
            *self = Self(None);
        }

        next
    }
}

// HACK(eddyb) `impl Trait` helper for when a non-bound lifetime needs capturing.
// FIXME(eddyb) should `map_with_parent_component_path` even use `impl Trait`?
trait Captures<'a> {}
impl<T> Captures<'_> for T {}

impl<'a> DisaggregatedLeafTypes<'a> {
    // HACK(eddyb) like `map`, but acessing the `parent_component_path` of
    // the inner `AggregateCursor`, when it is possitioned at each leaf.
    fn map_with_parent_component_path<T>(
        self,
        mut f: impl FnMut(Type, &[(Type, u32)]) -> T,
    ) -> impl Iterator<Item = T> + Captures<'a> {
        let Self(mut cursor_slot) = self;
        iter::from_fn(move || {
            let cursor = cursor_slot.as_mut()?;
            let next = cursor
                .try_ensure_at_leaf()
                .then(|| f(cursor.current, &cursor.parent_component_path));

            // Record advancement failure, ensuring future calls to `next` return `None`.
            if !(next.is_some() && cursor.try_advance()) {
                cursor_slot = None;
            }

            next
        })
    }
}

// FIXME(eddyb) not the best place to put these utilities, but they're used in
// both `spv::lower` and `spv::lift` (and they use private methods defined here).
// FIXME(eddyb) consider moving some of this to `spv::canonical`.
impl Type {
    fn disaggregated_leaf_types(self, cx: &Context) -> DisaggregatedLeafTypes<'_> {
        DisaggregatedLeafTypes(Some(AggregateCursor {
            cx,
            current: self,
            parent_component_path: SmallVec::new(),
        }))
    }

    fn aggregate_component_type_and_leaf_range(
        self,
        cx: &Context,
        idx: u32,
    ) -> Option<(Type, Range<usize>)> {
        let (type_and_const_inputs, aggregate_shape) = match &cx[self].kind {
            TypeKind::SpvInst {
                spv_inst: _,
                type_and_const_inputs,
                value_lowering: ValueLowering::Disaggregate(aggregate_shape),
            } => (type_and_const_inputs, aggregate_shape),
            _ => return None,
        };
        let expect_type = |ty_or_ct| match ty_or_ct {
            TypeOrConst::Type(ty) => ty,
            TypeOrConst::Const(_) => unreachable!(),
        };

        let idx_usize = idx as usize;
        let component_type = match aggregate_shape {
            AggregateShape::Struct { .. } => expect_type(*type_and_const_inputs.get(idx_usize)?),
            &AggregateShape::Array { fixed_len, .. } => {
                if idx >= fixed_len {
                    return None;
                }
                expect_type(type_and_const_inputs[0])
            }
        };
        let component_leaf_count = cx[component_type].disaggregated_leaf_count();

        let component_leaf_range = match aggregate_shape {
            AggregateShape::Struct { per_field_leaf_range_end } => {
                let end = per_field_leaf_range_end[idx_usize] as usize;
                let start = end.checked_sub(component_leaf_count)?;
                start..end
            }
            AggregateShape::Array { .. } => {
                let start = component_leaf_count.checked_mul(idx_usize)?;
                let end = start.checked_add(component_leaf_count)?;
                start..end
            }
        };
        Some((component_type, component_leaf_range))
    }
}

/// Aspects of how a [`spv::Inst`](Inst) was produced by [`spv::lower`](lower),
/// which were otherwise lost in the SPIR-T form, but are still required for
/// [`spv::lift`](lift) to reproduce the original SPIR-V instruction.
///
/// Primarily used within [`DataInstKind`](crate::DataInstKind) due to SPIR-V
/// instructions that take or produce "aggregates" (`OpTypeStruct`/`OpTypeArray`)
/// and which may require the exact original types (i.e. may not be valid when
/// using a fresh `OpTypeStruct` of the flattened non-"aggregate" components).
#[derive(Clone, Default, PartialEq, Eq, Hash)]
pub struct InstLowering {
    // FIXME(eddyb) should this be named "result" instead of "output", somewhat
    // standardizing the idea that 1 SPIR-V "result" maps to N SPIR-T "outputs"?
    pub disaggregated_output: Option<Type>,

    // FIXME(eddyb) only store the starts, and get the leaf counts from the `Type`.
    pub disaggregated_inputs: SmallVec<[(Range<u32>, Type); 1]>,
}

/// Helper type for [`InstLowering::reaggreate_inputs`], which corresponds to
/// one or more inputs of a SPIR-V instruction (after being lowered to SPIR-T),
/// according to the [`InstLowering`] (and its `disaggregated_inputs` field).
#[derive(Copy, Clone)]
pub enum ReaggregatedIdOperand<'a, T> {
    Direct(T),
    Aggregate { ty: Type, leaves: &'a [T] },
}

impl InstLowering {
    pub fn reaggreate_inputs<'a, T: Copy>(
        &'a self,
        inputs: &'a [T],
    ) -> impl Iterator<Item = ReaggregatedIdOperand<'a, T>> + Clone {
        // HACK(eddyb) the `None` at the end handles remainining direct inputs.
        let mut prev_end = 0;
        self.disaggregated_inputs.iter().map(Some).chain([None]).flat_map(
            move |maybe_disaggregated| {
                // FIXME(eddyb) the range manipulation is all over the place here.
                let direct_range = prev_end
                    ..maybe_disaggregated.map_or(inputs.len(), |(range, _)| range.start as usize);
                assert!(direct_range.start <= direct_range.end);
                prev_end = direct_range.end;

                let direct_inputs =
                    inputs[direct_range].iter().copied().map(ReaggregatedIdOperand::Direct);

                let aggregate_input = maybe_disaggregated.map(|(range, ty)| {
                    let leaves_range = range.start as usize..range.end as usize;
                    prev_end = leaves_range.end;

                    ReaggregatedIdOperand::Aggregate { ty: *ty, leaves: &inputs[leaves_range] }
                });

                direct_inputs.chain(aggregate_input)
            },
        )
    }
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
        Self { opcode, imms: SmallVec::new() }
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
pub fn extract_literal_string(imms: &[Imm]) -> Result<String, FromUtf8Error> {
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
pub fn encode_literal_string(s: &str) -> impl Iterator<Item = Imm> + '_ {
    let wk = &spec::Spec::get().well_known;

    let bytes = s.as_bytes();

    // FIXME(eddyb) replace with `array_chunks` once that is stabilized.
    let full_words = bytes.chunks_exact(4).map(|w| <[u8; 4]>::try_from(w).unwrap());

    let leftover_bytes = &bytes[full_words.len() * 4..];
    let mut last_word = [0; 4];
    last_word[..leftover_bytes.len()].copy_from_slice(leftover_bytes);

    let total_words = full_words.len() + 1;

    full_words.chain(iter::once(last_word)).map(u32::from_le_bytes).enumerate().map(
        move |(i, word)| {
            let kind = wk.LiteralString;
            match (i, total_words) {
                (0, 1) => Imm::Short(kind, word),
                (0, _) => Imm::LongStart(kind, word),
                (_, _) => Imm::LongCont(kind, word),
            }
        },
    )
}
