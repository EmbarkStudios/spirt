//! Scalar (`bool`, integer, and floating-point) types and associated functionality.
//!
//! **Note**: pointers are never scalars (like SPIR-V, but unlike other IRs).

// HACK(eddyb) this could be some `struct` with private fields, but this `enum`
// is only 2 bytes in size, and has better ergonomics overall.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Bool,
    SInt(IntWidth),
    UInt(IntWidth),
    Float(FloatWidth),
}

impl Type {
    // HACK(eddyb) only common widths, as a convenience, expand as-needed.
    pub const S32: Type = Type::SInt(IntWidth::I32);
    pub const U32: Type = Type::UInt(IntWidth::I32);
    pub const F32: Type = Type::Float(FloatWidth::F32);
    pub const F64: Type = Type::Float(FloatWidth::F64);

    pub const fn bit_width(self) -> u32 {
        match self {
            Type::Bool => 1,
            Type::SInt(w) | Type::UInt(w) => w.bits(),
            Type::Float(w) => w.bits(),
        }
    }
}

/// Bit-width of a supported integer type (only power-of-two multiples of a byte).
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct IntWidth {
    // HACK(eddyb) this is so compact that only 3 bits of this byte are used
    // to encode integer types from `i8` to `i128`, and so `Type` could all fit
    // in one byte, but that'd need a new `enum` for `Bool`/`{S,U}Int`/`Float`.
    log2_bytes: u8,
}

impl IntWidth {
    pub const I8: Self = Self::try_from_bits_unwrap(8);
    pub const I16: Self = Self::try_from_bits_unwrap(16);
    pub const I32: Self = Self::try_from_bits_unwrap(32);
    pub const I64: Self = Self::try_from_bits_unwrap(64);
    pub const I128: Self = Self::try_from_bits_unwrap(128);

    // FIXME(eddyb) remove when `Option::unwrap` is stabilized.
    const fn try_from_bits_unwrap(bits: u32) -> Self {
        match Self::try_from_bits(bits) {
            Some(w) => w,
            None => unreachable!(),
        }
    }

    pub const fn try_from_bits(bits: u32) -> Option<Self> {
        if bits % 8 != 0 {
            return None;
        }
        let bytes = bits / 8;
        match bytes.checked_ilog2() {
            Some(log2_bytes_u32) => {
                let log2_bytes = log2_bytes_u32 as u8;
                assert!(log2_bytes as u32 == log2_bytes_u32);
                Some(Self { log2_bytes })
            }
            None => None,
        }
    }

    pub const fn bits(self) -> u32 {
        8 * (1 << self.log2_bytes)
    }
}

/// Bit-width of a supported floating-point type (only power-of-two multiples of a byte).
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct FloatWidth(IntWidth);

impl FloatWidth {
    pub const F32: Self = Self::try_from_bits_unwrap(32);
    pub const F64: Self = Self::try_from_bits_unwrap(64);

    // FIXME(eddyb) remove when `Option::unwrap` is stabilized.
    const fn try_from_bits_unwrap(bits: u32) -> Self {
        match Self::try_from_bits(bits) {
            Some(w) => w,
            None => unreachable!(),
        }
    }

    pub const fn try_from_bits(bits: u32) -> Option<Self> {
        match IntWidth::try_from_bits(bits) {
            Some(w) => Some(Self(w)),
            None => None,
        }
    }

    pub const fn bits(self) -> u32 {
        self.0.bits()
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
        match self.ty {
            Type::Bool | Type::Float(_) => None,
            Type::SInt(_) => {
                let width = self.ty.bit_width();
                Some((self.bits as i128) << (128 - width) >> (128 - width))
            }
            Type::UInt(_) => self.bits.try_into().ok(),
        }
    }

    /// Returns `Some(v)` iff `self` is `{S,U}Int` and representable by `v: u128`
    /// (i.e. `self` is positive and has the same absolute value as `v` does).
    pub fn int_as_u128(&self) -> Option<u128> {
        match self.ty {
            Type::Bool | Type::Float(_) => None,
            Type::SInt(_) => self.int_as_i128()?.try_into().ok(),
            Type::UInt(_) => Some(self.bits),
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
