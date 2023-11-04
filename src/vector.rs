//! Vector types (small arrays of [`scalar`](crate::scalar)s) and associated functionality.
//!
//! **Note**: these are similar to SIMD types in other IRs, but SPIR-V often uses
//! its `OpTypeVector` to represent geometrical vectors, colors, etc. without any
//! expectation of SIMD execution (which most GPU execution models use implicitly,
//! i.e. one non-uniform scalar becomes a hardware SIMD vector, while a high-level
//! "vector" of N "lanes", becomes N separate hardware SIMD vectors).

use crate::scalar;
use smallvec::SmallVec;
use std::num::NonZeroU8;
use std::rc::Rc;

// FIXME(eddyb) this entire module shorthands "element" as "elem", is that good?

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Type {
    pub elem: scalar::Type,
    // FIXME(eddyb) maybe wrap this in a type that abstracts away the encoding?
    pub elem_count: NonZeroU8,
}

// FIXME(eddyb) document the 128-bit limitations inherited from `scalar::Const`.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Const(ConstRepr);

// HACK(eddyb) `#[repr(packed)]` not allowed on `enum`s themselves.
#[repr(packed)]
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
struct Packed<T>(T);

// FIXME(eddyb) maybe build an abstraction for "N-dimensional" bit arrays?
#[derive(Clone, PartialEq, Eq, Hash)]
#[repr(u8)]
enum ConstRepr {
    // HACK(eddyb) `(Type, u128)` would waste almost half its size on padding, and
    // packing will only impact accessing the bits, while allowing e.g. being
    // wrapped in an outer `enum`, before reaching the same size as `(u128, u128)`.
    Inline(Type, Packed<u128>),

    // HACK(eddyb) this does raise the alignment, but the size and alignment are
    // kept at one pointer (so likely half of `u128`) - `Packed<Rc<_>>` is sadly
    // not an option because `#[derive(...)]` + `#[repr(packed)]` often requires
    // `Copy` in order to be able to safely take references (to a copy of a field).
    Boxed(Type, Rc<Vec<u128>>),
}

impl Const {
    pub const fn ty(&self) -> Type {
        match self.0 {
            ConstRepr::Inline(ty, _) | ConstRepr::Boxed(ty, _) => ty,
        }
    }

    pub fn from_elems(ty: Type, elems: impl IntoIterator<Item = scalar::Const>) -> Const {
        let elem_width = ty.elem.bit_width();
        assert!(elem_width <= 128);

        let expected_elem_count = u32::from(ty.elem_count.get());

        let num_limbs = elem_width.checked_mul(expected_elem_count).unwrap().div_ceil(128);
        assert_ne!(num_limbs, 0);
        let mut limbs = SmallVec::<[u128; 1]>::from_elem(0, usize::try_from(num_limbs).unwrap());

        let mut found_elem_count = 0;
        for ct in elems {
            let i: u32 = found_elem_count;
            found_elem_count = found_elem_count.checked_add(1).unwrap();
            if i >= expected_elem_count {
                continue;
            }

            // FIXME(eddyb) get better names (perhaps from miri-like memory?).
            let first_bit_idx = i.checked_mul(elem_width).unwrap();
            let limb_idx = first_bit_idx / 128;
            let intra_limb_first_bit_idx = first_bit_idx % 128;
            assert!(intra_limb_first_bit_idx + elem_width <= 128);

            limbs[usize::try_from(limb_idx).unwrap()] |= ct.bits() << intra_limb_first_bit_idx;
        }
        assert_eq!(found_elem_count, expected_elem_count);

        match limbs.into_inner() {
            Ok([limb]) => Const(ConstRepr::Inline(ty, Packed(limb))),
            Err(limbs) => Const(ConstRepr::Boxed(ty, Rc::new(limbs.into_vec()))),
        }
    }

    pub fn get_elem(&self, i: usize) -> Option<scalar::Const> {
        let ty = self.ty();
        if i >= usize::from(ty.elem_count.get()) {
            return None;
        }
        let i = u32::try_from(i).unwrap();
        let elem_width = ty.elem.bit_width();
        assert!(elem_width <= 128);

        // FIXME(eddyb) get better names (perhaps from miri-like memory?).
        let first_bit_idx = i.checked_mul(elem_width).unwrap();
        let limb_idx = first_bit_idx / 128;
        let intra_limb_first_bit_idx = first_bit_idx % 128;
        assert!(intra_limb_first_bit_idx + elem_width <= 128);

        let limb = match &self.0 {
            ConstRepr::Inline(_, limb) => {
                assert_eq!(limb_idx, 0);
                limb.0
            }
            ConstRepr::Boxed(_, limbs) => limbs[usize::try_from(limb_idx).unwrap()],
        };

        Some(scalar::Const::from_bits(
            ty.elem,
            (limb >> intra_limb_first_bit_idx) & (!0 >> (128 - elem_width)),
        ))
    }

    pub fn elems(&self) -> impl Iterator<Item = scalar::Const> + '_ {
        let ty = self.ty();
        // FIXME(eddyb) there should be a more efficient way to do this.
        (0..usize::from(ty.elem_count.get())).map(|i| self.get_elem(i).unwrap())
    }
}
