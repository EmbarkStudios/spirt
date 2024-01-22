//! Scalar (`bool`, integer, and floating-point) types and associated functionality.
//!
//! **Note**: pointers are never scalars (like SPIR-V, but unlike other IRs).

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum TypeKind {
    Bool,
    Float,
    UInt,
    SInt,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Bool,
    S8, S16, S32, S64, S128,
    U8, U16, U32, U64, U128,
    F16, F32, F64,
}

impl Type {
    pub const fn bit_width(self) -> u32 {
        match self {
            Type::Bool => 1,
            Type::S8 | Type::U8 => 8,
            Type::S16 | Type::U16 | Type::F16 => 16,
            Type::S32 | Type::U32 | Type::F32 => 32,
            Type::S64 | Type::U64 | Type::F64 => 64,
            Type::S128 | Type::U128 => 128,
        }
    }

    pub const fn kind(self) -> TypeKind {
        match self {
            Type::Bool => TypeKind::Bool,
            Type::S8 | Type::S16 | Type::S32 | Type::S64 | Type::S128 => TypeKind::SInt,
            Type::U8 | Type::U16 | Type::U32 | Type::U64 | Type::U128 => TypeKind::UInt,
            Type::F16 | Type::F32 | Type::F64 => TypeKind::Float,
        }
    }

    pub const fn is_integer(self) -> bool {
        matches!(self.kind(), TypeKind::UInt | TypeKind::SInt)
    }

    pub const fn is_signed_integer(self) -> bool {
        matches!(self.kind(), TypeKind::SInt)
    }

    pub const fn uint_from_bit_width(bit_width: u32) -> Option<Self> {
        Some(match bit_width {
            8 => Self::U8,
            16 => Self::U16,
            32 => Self::U32,
            64 => Self::U64,
            128 => Self::U128,
            _ => return None,
        })
    }

    pub const fn sint_from_bit_width(bit_width: u32) -> Option<Self> {
        Some(match bit_width {
            8 => Self::S8,
            16 => Self::S16,
            32 => Self::S32,
            64 => Self::S64,
            128 => Self::S128,
            _ => return None,
        })
    }

    pub const fn float_from_bit_width(bit_width: u32) -> Option<Self> {
        Some(match bit_width {
            16 => Self::F16,
            32 => Self::F32,
            64 => Self::F64,
            _ => return None,
        })
    }
}


// FIXME(eddyb) document the 128-bit limitations.
// HACK(eddyb) `(Type, u128)` would waste almost half its size on padding, and
// packing will only impact accessing the `bits`, while allowing e.g. being
// wrapped in an outer `enum`, before reaching the same size as `(u128, u128)`.
#[repr(packed)]
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Const {
    ty: Type,
    bits: u128,
}

impl Const {
    pub const FALSE: Const = Const::from_bool(false);
    pub const TRUE: Const = Const::from_bool(true);

    // FIXME(eddyb) document the panic conditions.
    // FIXME(eddyb) make this public?
    const fn from_bits_trunc(ty: Type, bits: u128) -> Const {
        // FIXME(eddyb) this ensures `Const`s cannot be created when that could
        // potentially need more than 128 bits for e.g. constant-folding.
        let width = ty.bit_width();
        assert!(width <= 128);

        Const { ty, bits: bits & (!0u128 >> (128 - width)) }
    }

    // FIXME(eddyb) document the panic conditions.
    pub const fn from_bits(ty: Type, bits: u128) -> Const {
        let ct_trunc = Const::from_bits_trunc(ty, bits);
        assert!(ct_trunc.bits == bits);
        ct_trunc
    }

    pub const fn try_from_bits(ty: Type, bits: u128) -> Option<Const> {
        let ct_trunc = Const::from_bits_trunc(ty, bits);
        if ct_trunc.bits == bits { Some(ct_trunc) } else { None }
    }

    pub const fn from_bool(v: bool) -> Const {
        Const::from_bits(Type::Bool, v as u128)
    }

    pub const fn from_u32(v: u32) -> Const {
        Const::from_bits(Type::U32, v as u128)
    }

    /// Returns `Some(ct)` iff `ty` is `{S,U}Int` and can represent `v: i128`
    /// (i.e. `ct` has the same sign and absolute value as `v` does).
    pub fn int_try_from_i128(ty: Type, v: i128) -> Option<Const> {
        let ct_trunc = Const::from_bits_trunc(ty, v as u128);
        (ct_trunc.int_as_i128() == Some(v)).then_some(ct_trunc)
    }

    pub const fn ty(&self) -> Type {
        self.ty
    }

    pub const fn bits(&self) -> u128 {
        self.bits
    }

    /// Returns `Some(v)` iff `self` is `{S,U}Int` and representable by `v: i128`
    /// (i.e. `self` has the same sign and absolute value as `v` does).
    pub fn int_as_i128(&self) -> Option<i128> {
        match self.ty.kind() {
            TypeKind::Bool | TypeKind::Float => None,
            TypeKind::SInt => {
                let width = self.ty.bit_width();
                Some((self.bits as i128) << (128 - width) >> (128 - width))
            }
            TypeKind::UInt => self.bits.try_into().ok(),
        }
    }

    /// Returns `Some(v)` iff `self` is `{S,U}Int` and representable by `v: u128`
    /// (i.e. `self` is positive and has the same absolute value as `v` does).
    pub fn int_as_u128(&self) -> Option<u128> {
        match self.ty.kind() {
            TypeKind::Bool | TypeKind::Float => None,
            TypeKind::SInt => self.int_as_i128()?.try_into().ok(),
            TypeKind::UInt => Some(self.bits),
        }
    }

    /// Returns `Some(v)` iff `self` is `{S,U}Int` and representable by `v: i32`
    /// (i.e. `self` has the same sign and absolute value as `v` does).
    pub fn int_as_i32(&self) -> Option<i32> {
        self.int_as_i128()?.try_into().ok()
    }

    /// Returns `Some(v)` iff `self` is `{S,U}Int` and representable by `v: u32`
    /// (i.e. `self` is positive and has the same absolute value as `v` does).
    pub fn int_as_u32(&self) -> Option<u32> {
        self.int_as_u128()?.try_into().ok()
    }
}

/// Pure operations with scalar inputs and outputs.
//
// FIXME(eddyb) these are not some "perfect" grouping, but allow for more
// flexibility in users of this `enum` (and its component `enum`s).
#[derive(Copy, Clone, PartialEq, Eq, Hash, derive_more::From)]
pub enum Op {
    BoolUnary(BoolUnOp),
    BoolBinary(BoolBinOp),

    IntUnary(IntUnOp),
    IntBinary(IntBinOp),

    FloatUnary(FloatUnOp),
    FloatBinary(FloatBinOp),
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum BoolUnOp {
    Not,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum BoolBinOp {
    Eq,
    // FIXME(eddyb) should this be `Xor` instead?
    Ne,
    Or,
    And,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum IntUnOp {
    Neg,
    Not,
    CountOnes,

    // FIXME(eddyb) ideally `Trunc` should be separated and common.
    TruncOrZeroExtend,
    TruncOrSignExtend,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum IntBinOp {
    // I×I→I
    Add,
    Sub,
    Mul,
    DivU,
    DivS,
    ModU,
    RemS,
    ModS,
    ShrU,
    ShrS,
    Shl,
    Or,
    Xor,
    And,

    // I×I→I×I
    CarryingAdd,
    BorrowingSub,
    WideningMulU,
    WideningMulS,

    // I×I→B
    Eq,
    Ne,
    // FIXME(eddyb) deduplicate between signed and unsigned.
    GtU,
    GtS,
    GeU,
    GeS,
    LtU,
    LtS,
    LeU,
    LeS,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum FloatUnOp {
    // F→F
    Neg,

    // F→B
    IsNan,
    IsInf,

    // FIXME(eddyb) these are a complicated mix of signatures.
    FromUInt,
    FromSInt,
    ToUInt,
    ToSInt,
    Convert,
    QuantizeAsF16,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum FloatBinOp {
    // F×F→F
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Mod,

    // F×F→B
    Cmp(FloatCmp),
    // FIXME(eddyb) this doesn't properly convey that this is effectively the
    // boolean flip of the opposite comparison, e.g. `CmpOrUnord(Ge)` is really
    // a fused version of `Not(Cmp(Lt))`, because `x < y` is never `true` for
    // unordered `x` and `y` (i.e. `PartialOrd::partial_cmp(x, y) == None`),
    // but that maps to `!(x < y)` always being `true` for unordered `x` and `y`,
    // and thus `x >= y` is only equivalent for the ordered cases.
    CmpOrUnord(FloatCmp),
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum FloatCmp {
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
}

impl Op {
    pub fn output_count(self) -> usize {
        match self {
            Op::IntBinary(op) => op.output_count(),
            _ => 1,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            Op::BoolUnary(op) => op.name(),
            Op::BoolBinary(op) => op.name(),

            Op::IntUnary(op) => op.name(),
            Op::IntBinary(op) => op.name(),

            Op::FloatUnary(op) => op.name(),
            Op::FloatBinary(op) => op.name(),
        }
    }
}

impl BoolUnOp {
    pub fn name(self) -> &'static str {
        match self {
            BoolUnOp::Not => "bool.not",
        }
    }
}

impl BoolBinOp {
    pub fn name(self) -> &'static str {
        match self {
            BoolBinOp::Eq => "bool.eq",
            BoolBinOp::Ne => "bool.ne",
            BoolBinOp::Or => "bool.or",
            BoolBinOp::And => "bool.and",
        }
    }
}

impl IntUnOp {
    pub fn name(self) -> &'static str {
        match self {
            IntUnOp::Neg => "i.neg",
            IntUnOp::Not => "i.not",
            IntUnOp::CountOnes => "i.count_ones",

            IntUnOp::TruncOrZeroExtend => "u.trunc_or_zext",
            IntUnOp::TruncOrSignExtend => "s.trunc_or_sext",
        }
    }
}

impl IntBinOp {
    pub fn output_count(self) -> usize {
        // FIXME(eddyb) should these 4 go into a different `enum`?
        match self {
            IntBinOp::CarryingAdd
            | IntBinOp::BorrowingSub
            | IntBinOp::WideningMulU
            | IntBinOp::WideningMulS => 2,
            _ => 1,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            IntBinOp::Add => "i.add",
            IntBinOp::Sub => "i.sub",
            IntBinOp::Mul => "i.mul",
            IntBinOp::DivU => "u.div",
            IntBinOp::DivS => "s.div",
            IntBinOp::ModU => "u.mod",
            IntBinOp::RemS => "s.rem",
            IntBinOp::ModS => "s.mod",
            IntBinOp::ShrU => "u.shr",
            IntBinOp::ShrS => "s.shr",
            IntBinOp::Shl => "i.shl",
            IntBinOp::Or => "i.or",
            IntBinOp::Xor => "i.xor",
            IntBinOp::And => "i.and",
            IntBinOp::CarryingAdd => "i.carrying_add",
            IntBinOp::BorrowingSub => "i.borrowing_sub",
            IntBinOp::WideningMulU => "u.widening_mul",
            IntBinOp::WideningMulS => "s.widening_mul",
            IntBinOp::Eq => "i.eq",
            IntBinOp::Ne => "i.ne",
            IntBinOp::GtU => "u.gt",
            IntBinOp::GtS => "s.gt",
            IntBinOp::GeU => "u.ge",
            IntBinOp::GeS => "s.ge",
            IntBinOp::LtU => "u.lt",
            IntBinOp::LtS => "s.lt",
            IntBinOp::LeU => "u.le",
            IntBinOp::LeS => "s.le",
        }
    }
}

impl FloatUnOp {
    pub fn name(self) -> &'static str {
        match self {
            FloatUnOp::Neg => "f.neg",

            FloatUnOp::IsNan => "f.is_nan",
            FloatUnOp::IsInf => "f.is_inf",

            FloatUnOp::FromUInt => "f.from_uint",
            FloatUnOp::FromSInt => "f.from_sint",
            FloatUnOp::ToUInt => "f.to_uint",
            FloatUnOp::ToSInt => "f.to_sint",
            FloatUnOp::Convert => "f.convert",
            FloatUnOp::QuantizeAsF16 => "f.quantize_as_f16",
        }
    }
}

impl FloatBinOp {
    pub fn name(self) -> &'static str {
        match self {
            FloatBinOp::Add => "f.add",
            FloatBinOp::Sub => "f.sub",
            FloatBinOp::Mul => "f.mul",
            FloatBinOp::Div => "f.div",
            FloatBinOp::Rem => "f.rem",
            FloatBinOp::Mod => "f.mod",
            FloatBinOp::Cmp(FloatCmp::Eq) => "f.eq",
            FloatBinOp::Cmp(FloatCmp::Ne) => "f.ne",
            FloatBinOp::Cmp(FloatCmp::Lt) => "f.lt",
            FloatBinOp::Cmp(FloatCmp::Gt) => "f.gt",
            FloatBinOp::Cmp(FloatCmp::Le) => "f.le",
            FloatBinOp::Cmp(FloatCmp::Ge) => "f.ge",
            FloatBinOp::CmpOrUnord(FloatCmp::Eq) => "f.eq_or_unord",
            FloatBinOp::CmpOrUnord(FloatCmp::Ne) => "f.ne_or_unord",
            FloatBinOp::CmpOrUnord(FloatCmp::Lt) => "f.lt_or_unord",
            FloatBinOp::CmpOrUnord(FloatCmp::Gt) => "f.gt_or_unord",
            FloatBinOp::CmpOrUnord(FloatCmp::Le) => "f.le_or_unord",
            FloatBinOp::CmpOrUnord(FloatCmp::Ge) => "f.ge_or_unord",
        }
    }
}
