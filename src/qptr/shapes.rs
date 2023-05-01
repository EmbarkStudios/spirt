//! Variable shapes (untyped memory layouts vs abstract resources).
//
// FIXME(eddyb) does this need its own module still?

use crate::{AddrSpace, Type};
use std::num::NonZeroU32;

/// `GlobalVar`s are currently used for both chunks of plain data (i.e. memory),
/// and the "shader interface" (inherited by `Shader` SPIR-V from GLSL, whereas
/// `Kernel` SPIR-V ended up with `OpenCL`'s "resources are passed to entry-points
/// as regular function arguments", with `BuiltIn`+`Input` as a sole exception).
#[derive(Copy, Clone, PartialEq, Eq)]
pub enum GlobalVarShape {
    /// One or more (i.e. optionally arrayed) "abstract resource" `Handle`s
    /// (see `Handle` documentation for more on what it can represent).
    ///
    /// The single handle case is equivalent to a length `1` array of handles,
    /// and as such is represented by having `fixed_count` be `Some(1)`.
    Handles {
        handle: Handle,
        fixed_count: Option<NonZeroU32>,
    },

    // FIXME(eddyb) unify terminology around "concrete"/"memory"/"untyped (data)".
    UntypedData(MemLayout),

    /// Non-memory pipeline interface, which must keep the exact original type,
    /// even if that type is concrete and could be handled just like memory.
    ///
    /// Typically `Input` or `Output`, but extensions (e.g. ray-tracing) may add
    /// more such interface storage classes with strict type requirements.
    //
    // FIXME(eddyb) consider replacing this with by-value entry-point args/return
    // (though that would not solve some of the weirder ones).
    TypedInterface(Type),
}

/// "Abstract resource" handle, that can be found in non-memory `GlobalVar`s.
///
/// This largely corresponds to the Vulkan concept of a "descriptor", and arrays
/// of handles (e.g. `GlobalVarShape::Handles` with `fixed_count != Some(1)`)
/// map to the "descriptor indexing" usecase.
//
// FIXME(eddyb) consider implementing "descriptor indexing" more like HLSL's
// "resource heap" (with types only specified at use sites, "casts" almost).
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum Handle<BL = MaybeDynMemLayout> {
    /// Fully opaque resources (e.g. samplers, images).
    Opaque(Type),

    /// Buffer resources, describing ranges of (technically) untyped memory in
    /// some address space (e.g. `Uniform`, `StorageBuffer`), but being limited
    /// by SPIR-V logical addressing (unlike e.g. `PhysicalStorageBuffer`).
    ///
    /// SPIR-V makes this particularly painful, through a couple of design flaws:
    /// - forcing a static type (for the buffer contents) and disallowing any
    ///   pointer casts, despite the fact that any plausible representation for
    ///   "logical pointer into a buffer" (e.g. `(BufferDescriptor, Offset)`)
    ///   must be *fundamentally* untyped (as it must allow access to relatively
    ///   large amounts of memory, and also support dynamic array indexing),
    ///   even when not a "GPU memory address" (like `PhysicalStorageBuffer`)
    /// - encoding the buffer type using a (GLSL-style) "interface block", where
    ///   instead of a special type (or a pointer with the right storage class),
    ///   an `OpTypeStruct` (having the statically typed buffer contents as fields)
    ///   with the `Block` decoration is used, and then this "interface block"
    ///   type can be further nested in `OpTypeArray` or `OpTypeRuntimeArray`
    ///   to allow descriptor indexing - which leads to constructs like a GLSL
    ///   `buffer { uint data[]; } bufs[];` being encoded with two levels of
    ///   `OpTypeRuntimeArray`, separated not by any explicit indirection, but
    ///   only by the `Block` decoration on the `OpTypeStruct` for `buffer {...}`
    //
    // FIXME(eddyb) should `PushConstant` use `GlobalVarShape::UntypedData`
    // instead of being treated like a buffer?
    //
    // FIXME(eddyb) should this be a `Type` of its own, that can be loaded from
    // a handle `QPtr`, and then has data pointer / length ops *on that*?
    Buffer(AddrSpace, BL),
}

/// Untyped memory shape with constant alignment and size.
///
/// `align`/`legacy_align` correspond to "scalar"/"base" alignments in Vulkan,
/// and are both kept track of to detect ambiguity in implicit layouts, e.g.
/// field offsets when the `Offset` decoration isn't being used.
/// Note, however, that `legacy_align` can be raised to "extended" alignment,
/// or completeley ignored, using [`LayoutConfig`](crate::qptr::LayoutConfig).
///
/// Only `align` is *required*, that is `size % align == 0` must be always enforced.
//
// FIXME(eddyb) consider supporting specialization-constant-length arrays.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct MemLayout {
    // FIXME(eddyb) use proper newtypes (and log2 for align!).
    pub align: u32,
    pub legacy_align: u32,
    pub size: u32,
}

/// Untyped memory shape with constant alignment but potentially-dynamic size,
/// roughly corresponding to a Rust `(FixedBase, [DynUnit])` type's layout.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct MaybeDynMemLayout {
    pub fixed_base: MemLayout,
    pub dyn_unit_stride: Option<NonZeroU32>,
}
