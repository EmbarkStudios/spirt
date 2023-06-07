//! [`QPtr`](crate::TypeCtor::QPtr)-related type definitions and passes.
//
// FIXME(eddyb) consider `#[cfg(doc)] use crate::TypeCtor::QPtr;` for doc comments.
// FIXME(eddyb) PR description of https://github.com/EmbarkStudios/spirt/pull/24
// has more useful docs that could be copied here.

use crate::{AddrSpace, Attr, DataInstKind, OrdAssertEq, Type};
use std::collections::BTreeMap;
use std::num::NonZeroU32;
use std::ops::Range;
use std::rc::Rc;

// NOTE(eddyb) all the modules are declared here, but they're documented "inside"
// (i.e. using inner doc comments).
pub mod analyze;
mod layout;
pub mod lift;
pub mod lower;
pub mod shapes;

pub use layout::LayoutConfig;

/// `QPtr`-specific attributes ([`Attr::QPtr`]).
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum QPtrAttr {
    /// When applied to a `DataInst` with a `QPtr`-typed `inputs[input_idx]`,
    /// this describes the original `OpTypePointer` consumed by an unknown
    /// SPIR-V instruction (which may, or may not, access memory, at all).
    ///
    /// Assumes the original SPIR-V `StorageClass` is redundant (i.e. can be
    /// deduced from the pointer's provenance), and that any accesses performed
    /// through the pointer (or any pointers derived from it) stay within bounds
    /// (i.e. logical pointer semantics, unsuited for e.g. `OpPtrAccessChain`).
    //
    // FIXME(eddyb) reduce usage by modeling more of SPIR-V inside SPIR-T.
    ToSpvPtrInput {
        input_idx: u32,
        pointee: OrdAssertEq<Type>,
    },

    /// When applied to a `DataInst` with a `QPtr`-typed output value,
    /// this describes the original `OpTypePointer` produced by an unknown
    /// SPIR-V instruction (likely creating it, without deriving from an input).
    ///
    /// Assumes the original SPIR-V `StorageClass` is significant (e.g. fresh
    /// provenance being created on the fly via `OpConvertUToPtr`, or derived
    /// internally by the implementation via `OpImageTexelPointer`).
    //
    // FIXME(eddyb) reduce usage by modeling more of SPIR-V inside SPIR-T, or
    // at least using some kind of bitcast instead of `QPtr` + this attribute.
    // FIXME(eddyb) `OpConvertUToPtr` creates a physical pointer, could we avoid
    // dealing with those at all in `QPtr`? (as its focus is logical legalization)
    FromSpvPtrOutput {
        // FIXME(eddyb) should this use a special `spv::StorageClass` type?
        addr_space: OrdAssertEq<AddrSpace>,
        pointee: OrdAssertEq<Type>,
    },

    /// When applied to a `QPtr`-typed `GlobalVar`, `DataInst`,
    /// `ControlRegionInputDecl` or `ControlNodeOutputDecl`, this tracks all the
    /// ways in which the pointer may be used (see `QPtrUsage`).
    Usage(OrdAssertEq<QPtrUsage>),
}

impl From<QPtrAttr> for Attr {
    fn from(attr: QPtrAttr) -> Self {
        Attr::QPtr(attr)
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum QPtrUsage {
    /// Used to access one or more handles (i.e. optionally indexed by
    /// [`QPtrOp::HandleArrayIndex`]), which can be:
    /// - `Handle::Opaque(handle_type)`: all uses involve [`QPtrOp::Load`] or
    ///   [`QPtrAttr::ToSpvPtrInput`], with the common type `handle_type`
    /// - `Handle::Buffer(data_usage)`: carries with it `data_usage`, i.e. the
    ///   usage of the memory that can be accessed through [`QPtrOp::BufferData`]
    Handles(shapes::Handle<QPtrMemUsage>),

    // FIXME(eddyb) unify terminology around "concrete"/"memory"/"untyped (data)".
    Memory(QPtrMemUsage),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct QPtrMemUsage {
    /// If present, this is a worst-case upper bound on memory accesses that may
    /// be performed through this pointer.
    //
    // FIXME(eddyb) use proper newtypes for byte amounts.
    //
    // FIXME(eddyb) suboptimal naming choice, but other options are too verbose,
    // including maybe using `RangeTo<_>` to explicitly indicate "exclusive".
    //
    // FIXME(eddyb) consider renaming such information to "extent", but that might
    // be ambiguous with an offset range (as opposed to min/max of *possible*
    // `offset_range.end`, i.e. "size").
    pub max_size: Option<u32>,

    pub kind: QPtrMemUsageKind,
}

impl QPtrMemUsage {
    pub const UNUSED: Self = Self {
        max_size: Some(0),
        kind: QPtrMemUsageKind::Unused,
    };
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum QPtrMemUsageKind {
    /// Not actually used, which could be caused by pointer offsetting operations
    /// with unused results, or as an intermediary state during analyses.
    Unused,

    // FIXME(eddyb) replace the two leaves with e.g. `Leaf(Type, QPtrMemLeafUsage)`.
    //
    //
    //
    /// Used as a typed pointer (e.g. via unknown SPIR-V instructions), requiring
    /// a specific choice of pointee type which cannot be modified, and has to be
    /// reused as-is when lifting `QPtr`s back to typed pointers.
    ///
    /// Other overlapping uses can be merged into this one as long as they can
    /// be fully expressed using the (transitive) components of this type.
    StrictlyTyped(Type),

    /// Used directly to access memory (e.g. [`QPtrOp::Load`], [`QPtrOp::Store`]),
    /// which can be decomposed as necessary (down to individual scalar leaves),
    /// to allow maximal merging opportunities.
    //
    // FIXME(eddyb) track whether `Load`s and/or `Store`s are used, so that we
    // can infer `NonWritable`/`NonReadable` annotations as well.
    DirectAccess(Type),

    /// Used as a common base for (constant) offsetting, which requires it to have
    /// its own (aggregate) type, when lifting `QPtr`s back to typed pointers.
    OffsetBase(Rc<BTreeMap<u32, QPtrMemUsage>>),

    /// Used as a common base for (dynamic) offsetting, which requires it to have
    /// its own (array) type, when lifting `QPtr`s back to typed pointers, with
    /// one single element type being repeated across the entire size.
    DynOffsetBase {
        // FIXME(eddyb) this feels inefficient.
        element: Rc<QPtrMemUsage>,
        stride: NonZeroU32,
    },
    // FIXME(eddyb) consider adding an `Union` case for driving legalization.
}

/// `QPtr`-specific operations ([`DataInstKind::QPtr`]).
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum QPtrOp {
    // HACK(eddyb) `OpVariable` replacement, which itself should not be kept as
    // a `SpvInst` - once fn-local variables are lowered, this should go there.
    FuncLocalVar(shapes::MemLayout),

    /// Adjust a **handle array** `QPtr` (`inputs[0]`), by selecting the handle
    /// at the index (`inputs[1]`) from the handle array (i.e. the resulting
    /// `QPtr` is limited to that one handle and can't be further "moved around").
    //
    // FIXME(eddyb) this could maybe use `DynOffset`, if `stride` is changed to
    // be `enum { Handle, Bytes(u32) }`, but that feels a bit too much?
    HandleArrayIndex,

    /// Get a **memory** `QPtr` pointing at the contents of the buffer whose
    /// handle is (implicitly) loaded from a **handle** `QPtr` (`inputs[0]`).
    //
    // FIXME(eddyb) should buffers be a `Type` of their own, that can be loaded
    // from a handle `QPtr`, and then has data pointer / length ops *on that*?
    BufferData,

    /// Get the length of the buffer whose handle is (implicitly) loaded from a
    /// **handle** `QPtr` (`inputs[0]`), converted to a count of "dynamic units"
    /// (as per [`shapes::MaybeDynMemLayout`]) by subtracting `fixed_base_size`,
    /// then dividing by `dyn_unit_stride`.
    //
    // FIXME(eddyb) should this handle _only_ "length in bytes", with additional
    // integer subtraction+division operations on lowering to `QPtr`, and then
    // multiplication+addition on lifting back to SPIR-V, followed by simplifying
    // the redundant `(x * a + b - b) / a` to just `x`?
    //
    // FIXME(eddyb) actually lower `OpArrayLength` to this!
    BufferDynLen {
        fixed_base_size: u32,
        dyn_unit_stride: NonZeroU32,
    },

    /// Adjust a **memory** `QPtr` (`inputs[0]`), by adding a (signed) immediate
    /// amount of bytes to its "address" (whether physical or conceptual).
    //
    // FIXME(eddyb) some kind of `inbounds` would be very useful here, up to and
    // including "capability slicing" to limit the usable range of the output.
    Offset(i32),

    /// Adjust a **memory** `QPtr` (`inputs[0]`), by adding a (signed) dynamic
    /// "index" (`inputs[1]`), multiplied by `stride` (bytes per element),
    /// to its "address" (whether physical or conceptual).
    DynOffset {
        stride: NonZeroU32,

        /// Bounds on the dynamic "index" (`inputs[1]`).
        //
        // FIXME(eddyb) should this be an attribute/refinement?
        index_bounds: Option<Range<i32>>,
    },

    /// Read a single value from a `QPtr` (`inputs[0]`).
    //
    // FIXME(eddyb) limit this to memory, and scalars, maybe vectors at most.
    Load,

    /// Write a single value (`inputs[1]`) to a `QPtr` (`inputs[0]`).
    //
    // FIXME(eddyb) limit this to memory, and scalars, maybe vectors at most.
    Store,
    //
    // FIXME(eddyb) implement more ops! at the very least copying!
    // (and lowering could ignore pointercasts, I guess?)
}

impl From<QPtrOp> for DataInstKind {
    fn from(op: QPtrOp) -> Self {
        DataInstKind::QPtr(op)
    }
}
