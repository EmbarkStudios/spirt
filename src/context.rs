use rustc_hash::FxHashMap;
use std::num::NonZeroU32;

/// Context object with global resources for SPIR-T.
///
/// Those resources currently are:
/// * interners, for anything without an identity, and which can be deduplicated
/// * "entity" allocators, for everything else - i.e. anything with an identity
///   that needs to remain unique across an entire `Context`
///   * the *definition* of an entity isn't kept in the `Context`, but rather in
///     some `EntityDefs` collection somewhere in a `Module` (or further nested),
///     with only the entity *indices* being allocated by the `Context`
#[derive(Default)]
pub struct Context {
    interners: Interners,
    entity_allocs: EntityAllocs,
}

/// Private module containing traits (and related types) used in public APIs,
/// but which should not be usable outside of the `context` module.
mod sealed {
    use std::cell::Cell;
    use std::num::NonZeroU32;

    pub trait Interned: Sized + 'static {
        type Def: ?Sized + Eq + std::hash::Hash;

        fn preintern(_interner: &Interner<Self>) {}
        fn from_u32(i: u32) -> Self;
        fn to_u32(self) -> u32;
        fn cx_interner(cx: &super::Context) -> &Interner<Self>;
    }

    pub struct Interner<I: Interned>(
        elsa::FrozenIndexSet<Box<I::Def>, std::hash::BuildHasherDefault<rustc_hash::FxHasher>>,
    );

    impl<I: Interned> Default for Interner<I> {
        fn default() -> Self {
            let interner = Self(Default::default());
            I::preintern(&interner);
            interner
        }
    }

    impl<I: Interned> Interner<I> {
        #[track_caller]
        pub(super) fn intern(&self, value: impl AsRef<I::Def> + Into<Box<I::Def>>) -> I {
            if let Some((i, _)) = self.0.get_full(value.as_ref()) {
                return I::from_u32(i as u32);
            }
            let (i, _) = self.0.insert_full(value.into());
            I::from_u32(i.try_into().expect("interner overflowed u32"))
        }
    }

    impl<I: Interned> std::ops::Index<I> for Interner<I> {
        type Output = I::Def;

        fn index(&self, interned: I) -> &Self::Output {
            &self.0[interned.to_u32() as usize]
        }
    }

    pub trait Entity: Sized + Copy + Eq + std::hash::Hash + 'static {
        type Def;

        const CHUNK_SIZE: u32;
        const CHUNK_MASK: u32 = {
            assert!(Self::CHUNK_SIZE.is_power_of_two());
            assert!(Self::CHUNK_SIZE as usize as u32 == Self::CHUNK_SIZE);
            Self::CHUNK_SIZE - 1
        };

        fn from_non_zero_u32(i: NonZeroU32) -> Self;
        fn to_non_zero_u32(self) -> NonZeroU32;
        fn cx_entity_alloc(cx: &super::Context) -> &EntityAlloc<Self>;
    }

    pub struct EntityAlloc<E: Entity>(Cell<E>);

    impl<E: Entity> Default for EntityAlloc<E> {
        fn default() -> Self {
            // NOTE(eddyb) always skip chunk `0`, as a sort of "null page",
            // to allow using `NonZeroU32` instead of merely `u32`.
            Self(Cell::new(E::from_non_zero_u32(
                NonZeroU32::new(E::CHUNK_SIZE).unwrap(),
            )))
        }
    }

    impl<E: Entity> EntityAlloc<E> {
        #[track_caller]
        pub(super) fn alloc_chunk(&self) -> E {
            let chunk_start = self.0.get();
            let next_chunk_start = E::from_non_zero_u32(
                // FIXME(eddyb) use `NonZeroU32::checked_add`
                // when that gets stabilized.
                NonZeroU32::new(
                    chunk_start
                        .to_non_zero_u32()
                        .get()
                        .checked_add(E::CHUNK_SIZE)
                        .expect("entity index overflowed u32"),
                )
                .unwrap(),
            );
            self.0.set(next_chunk_start);
            chunk_start
        }
    }
}

/// Dispatch helper, to allow implementing interning logic on
/// the type passed to `cx.intern(...)`.
pub trait InternInCx<I> {
    #[track_caller]
    fn intern_in_cx(self, cx: &Context) -> I;
}

impl Context {
    pub fn new() -> Self {
        Self::default()
    }

    #[track_caller]
    pub fn intern<T: InternInCx<I>, I>(&self, x: T) -> I {
        x.intern_in_cx(self)
    }
}

impl<I: sealed::Interned> std::ops::Index<I> for Context {
    type Output = I::Def;

    fn index(&self, interned: I) -> &Self::Output {
        &I::cx_interner(self)[interned]
    }
}

/// Collection holding the actual definitions for `Context`-allocated entities.
///
/// By design there is no way to iterate the contents of an `EntityDefs`, or
/// generate entity indices without defining the entity in an `EntityDefs`.
//
// FIXME(eddyb) add an "entity-keyed map" that has similar restrictions, and
// some optimizations; will likely need both "dense" and "sparse" versions,
// where the sparse one is probably just a `FxHashMap` wrapper?
pub struct EntityDefs<E: sealed::Entity> {
    /// Entities are grouped into chunks, with per-entity-type chunk sizes
    /// (powers of 2) specified via `entities!` below.
    /// This allows different `EntityDefs`s to independently define more
    /// entities, without losing compactness (until a whole chunk is filled).
    //
    // FIXME(eddyb) consider using `u32` instead of `usize` for the "flattened base".
    complete_chunk_start_to_flattened_base: FxHashMap<E, usize>,

    /// Similar to a single entry in `complete_chunk_start_to_flattened_base`,
    /// but kept outside of the map for efficiency. Also, this is the only
    /// chunk that doesn't have its full size already (and therefore allows
    /// defining more entities into it, without allocating new chunks).
    incomplete_chunk_start_and_flattened_base: Option<(E, usize)>,

    /// All chunks' definitions are flattened into one contiguous `Vec`, where
    /// the start of each chunk's definitions in `flattened` is indicated by
    /// either `complete_chunk_start_to_flattened_base` (for completed chunks)
    /// or `incomplete_chunk_start_and_flattened_base`.
    flattened: Vec<E::Def>,
}

impl<E: sealed::Entity> Default for EntityDefs<E> {
    fn default() -> Self {
        Self {
            complete_chunk_start_to_flattened_base: FxHashMap::default(),
            incomplete_chunk_start_and_flattened_base: None,
            flattened: vec![],
        }
    }
}

impl<E: sealed::Entity> EntityDefs<E> {
    pub fn new() -> Self {
        Self::default()
    }

    #[track_caller]
    pub fn define(&mut self, cx: &Context, def: E::Def) -> E {
        let entity = match self.incomplete_chunk_start_and_flattened_base {
            Some((chunk_start, flattened_base)) => {
                let chunk_len = self.flattened.len() - flattened_base;
                if chunk_len == (E::CHUNK_SIZE - 1) as usize {
                    self.complete_chunk_start_to_flattened_base
                        .extend(self.incomplete_chunk_start_and_flattened_base.take());
                    panic!();
                }
                E::from_non_zero_u32(
                    NonZeroU32::new(chunk_start.to_non_zero_u32().get() + chunk_len as u32)
                        .unwrap(),
                )
            }
            None => {
                let chunk_start = E::cx_entity_alloc(cx).alloc_chunk();

                self.incomplete_chunk_start_and_flattened_base =
                    Some((chunk_start, self.flattened.len()));

                chunk_start
            }
        };
        self.flattened.push(def);
        entity
    }

    fn entity_to_flattened(&self, entity: E) -> Option<usize> {
        let (chunk_start, intra_chunk_idx) = {
            let e_u32 = entity.to_non_zero_u32().get();
            (
                E::from_non_zero_u32(NonZeroU32::new(e_u32 & !E::CHUNK_MASK).unwrap()),
                e_u32 & E::CHUNK_MASK,
            )
        };
        let flattened_base = match self.incomplete_chunk_start_and_flattened_base {
            Some((incomplete_chunk_start, incomplete_flattened_base))
                if chunk_start == incomplete_chunk_start =>
            {
                incomplete_flattened_base
            }
            _ => *self
                .complete_chunk_start_to_flattened_base
                .get(&chunk_start)?,
        };
        Some(flattened_base + intra_chunk_idx as usize)
    }
}

impl<E: sealed::Entity> std::ops::Index<E> for EntityDefs<E> {
    type Output = E::Def;

    fn index(&self, entity: E) -> &Self::Output {
        self.entity_to_flattened(entity)
            .and_then(|i| self.flattened.get(i))
            .unwrap()
    }
}

impl<E: sealed::Entity> std::ops::IndexMut<E> for EntityDefs<E> {
    fn index_mut(&mut self, entity: E) -> &mut Self::Output {
        self.entity_to_flattened(entity)
            .and_then(|i| self.flattened.get_mut(i))
            .unwrap()
    }
}

macro_rules! interners {
    (
        needs_as_ref { $($needs_as_ref_ty:ty),* $(,)? }
        $($name:ident $(default($default:expr))? => $ty:ty),+ $(,)?
    ) => {
        $(impl AsRef<Self> for $needs_as_ref_ty {
            fn as_ref(&self) -> &Self {
                self
            }
        })*

        #[allow(non_snake_case)]
        #[derive(Default)]
        struct Interners {
            $($name: sealed::Interner<$name>),*
        }

        $(
            // NOTE(eddyb) never derive `PartialOrd, Ord` for these types, as
            // observing the interning order shouldn't be allowed.
            #[derive(Copy, Clone, PartialEq, Eq, Hash)]
            pub struct $name(
                // FIXME(eddyb) figure out how to sneak niches into these types, to
                // allow e.g. `Option` around them to not increase the size.
                u32,
            );

            $(impl Default for $name {
                fn default() -> Self {
                    // HACK(eddyb) have to mention `$default` in this `$(...)?`
                    // to gate its presence on `$default`'s presence.
                    if false { let _ = $default; }

                    Self(0)
                }
            })?

            impl sealed::Interned for $name {
                type Def = $ty;

                $(fn preintern(interner: &sealed::Interner<Self>) {
                    interner.intern($default);
                })?
                #[inline(always)]
                fn from_u32(i: u32) -> Self {
                    Self(i)
                }
                #[inline(always)]
                fn to_u32(self) -> u32 {
                    self.0
                }
                #[inline(always)]
                fn cx_interner(cx: &Context) -> &sealed::Interner<Self> {
                    &cx.interners.$name
                }
            }
        )*
    };
}

interners! {
    needs_as_ref {
        crate::AttrSetDef,
        crate::TypeDef,
        crate::ConstDef,
    }

    // FIXME(eddyb) consider a more uniform naming scheme than the combination
    // of `InternedFoo => Foo` and `Foo => FooDef`.
    InternedStr => str,
    AttrSet default(crate::AttrSetDef::default()) => crate::AttrSetDef,
    Type => crate::TypeDef,
    Const => crate::ConstDef,
}

impl<I: sealed::Interned> InternInCx<I> for I::Def
where
    I::Def: Sized + AsRef<I::Def>,
{
    fn intern_in_cx(self, cx: &Context) -> I {
        I::cx_interner(cx).intern(self)
    }
}

impl InternInCx<InternedStr> for &'_ str {
    fn intern_in_cx(self, cx: &Context) -> InternedStr {
        cx.interners.InternedStr.intern(self)
    }
}

impl InternInCx<InternedStr> for String {
    fn intern_in_cx(self, cx: &Context) -> InternedStr {
        cx.interners.InternedStr.intern(self)
    }
}

macro_rules! entities {
    (
        $($name:ident => chunk_size($chunk_size:literal) $def:ty),+ $(,)?
    ) => {
        #[allow(non_snake_case)]
        #[derive(Default)]
        struct EntityAllocs {
            $($name: sealed::EntityAlloc<$name>),*
        }

        $(
            // NOTE(eddyb) never derive `PartialOrd, Ord` for these types, as
            // observing the entity index allocation order shouldn't be allowed.
            #[derive(Copy, Clone, PartialEq, Eq, Hash)]
            pub struct $name(NonZeroU32);

            impl sealed::Entity for $name {
                type Def = $def;

                const CHUNK_SIZE: u32 = $chunk_size;

                #[inline(always)]
                fn from_non_zero_u32(i: NonZeroU32) -> Self {
                    Self(i)
                }
                #[inline(always)]
                fn to_non_zero_u32(self) -> NonZeroU32 {
                    self.0
                }
                #[inline(always)]
                fn cx_entity_alloc(cx: &Context) -> &sealed::EntityAlloc<Self> {
                    &cx.entity_allocs.$name
                }
            }
        )*
    };
}

entities! {
    GlobalVar => chunk_size(0x1_0000) crate::GlobalVarDecl,
    Func => chunk_size(0x1_0000) crate::FuncDecl,
    Region => chunk_size(0x1000) crate::RegionDef,
    DataInst => chunk_size(0x1000) crate::DataInstDef,
}
