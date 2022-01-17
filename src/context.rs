use rustc_hash::FxHashMap;
use std::hash::Hash;
use std::mem;
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

        #[inline(always)]
        fn to_chunk_start_and_intra_chunk_idx(self) -> (Self, usize) {
            let self_u32 = self.to_non_zero_u32().get();
            (
                Self::from_non_zero_u32(NonZeroU32::new(self_u32 & !Self::CHUNK_MASK).unwrap()),
                (self_u32 & Self::CHUNK_MASK) as usize,
            )
        }
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
        let (chunk_start, intra_chunk_idx) = entity.to_chunk_start_and_intra_chunk_idx();
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
        Some(flattened_base + intra_chunk_idx)
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

/// Map with `E` (entity) keys and `V` values, that is "dense" in the sense of
/// few (or no) missing entries, relative to the corresponding `EntityDefs`.
///
/// By design there is no way to iterate the entries in an `EntityKeyedDenseMap`.
//
// FIXME(eddyb) implement a "sparse" version as well, and maybe some bitsets?
pub struct EntityKeyedDenseMap<E: sealed::Entity, V> {
    /// Like in `EntityDefs`, entities are grouped into chunks, but there is no
    /// flattening, since arbitrary insertion orders have to be supported.
    chunk_start_to_values: SmallFxHashMap<E, Vec<Option<V>>>,
}

// FIXME(eddyb) find a better "small map" design and/or fine-tune this - though,
// since the ideal state is one chunk per map, the slow case might never be hit,
// unless one `EntityKeyedDenseMap` is used with more than one `EntityDefs`,
// which could still maybe be implemented more efficiently than `FxHashMap`.
enum SmallFxHashMap<K, V> {
    Empty,
    One(K, V),
    More(FxHashMap<K, V>),
}

impl<K, V> Default for SmallFxHashMap<K, V> {
    fn default() -> Self {
        Self::Empty
    }
}

impl<K: Copy + Eq + Hash, V: Default> SmallFxHashMap<K, V> {
    fn get_mut_or_insert_default(&mut self, k: K) -> &mut V {
        // HACK(eddyb) to avoid borrowing issues, this is done in two stages:
        // 1. ensure `self` is `One(k, _) | More`, i.e. `One` implies same key
        match *self {
            Self::Empty => {
                *self = Self::One(k, V::default());
            }
            Self::One(old_k, _) => {
                if old_k != k {
                    let old = mem::replace(self, Self::More(Default::default()));
                    match (old, &mut *self) {
                        (Self::One(_, old_v), Self::More(map)) => {
                            map.insert(old_k, old_v);
                        }
                        _ => unreachable!(),
                    }
                }
            }
            Self::More(_) => {}
        }

        // 2. get the value from `One` or potentially insert one into `More`
        match self {
            Self::Empty => unreachable!(),
            Self::One(_, v) => v,
            Self::More(map) => map.entry(k).or_default(),
        }
    }

    fn get(&self, k: K) -> Option<&V> {
        match self {
            Self::Empty => None,
            Self::One(old_k, old_v) if *old_k == k => Some(old_v),
            Self::One(..) => None,
            Self::More(map) => map.get(&k),
        }
    }

    fn get_mut(&mut self, k: K) -> Option<&mut V> {
        match self {
            Self::Empty => None,
            Self::One(old_k, old_v) if *old_k == k => Some(old_v),
            Self::One(..) => None,
            Self::More(map) => map.get_mut(&k),
        }
    }
}

impl<E: sealed::Entity, V> Default for EntityKeyedDenseMap<E, V> {
    fn default() -> Self {
        Self {
            chunk_start_to_values: Default::default(),
        }
    }
}

impl<E: sealed::Entity, V> EntityKeyedDenseMap<E, V> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, entity: E, value: V) {
        let (chunk_start, intra_chunk_idx) = entity.to_chunk_start_and_intra_chunk_idx();
        let chunk_values = self
            .chunk_start_to_values
            .get_mut_or_insert_default(chunk_start);

        // Ensure there are enough slots for the new entry.
        let needed_len = intra_chunk_idx + 1;
        if chunk_values.len() < needed_len {
            chunk_values.resize_with(needed_len, || None);
        }

        chunk_values[intra_chunk_idx] = Some(value);
    }

    pub fn get(&self, entity: E) -> Option<&V> {
        let (chunk_start, intra_chunk_idx) = entity.to_chunk_start_and_intra_chunk_idx();
        self.chunk_start_to_values
            .get(chunk_start)?
            .get(intra_chunk_idx)?
            .as_ref()
    }

    pub fn get_mut(&mut self, entity: E) -> Option<&mut V> {
        let (chunk_start, intra_chunk_idx) = entity.to_chunk_start_and_intra_chunk_idx();
        self.chunk_start_to_values
            .get_mut(chunk_start)?
            .get_mut(intra_chunk_idx)?
            .as_mut()
    }
}

impl<E: sealed::Entity, V> std::ops::Index<E> for EntityKeyedDenseMap<E, V> {
    type Output = V;

    fn index(&self, entity: E) -> &V {
        self.get(entity).expect("no entry found for key")
    }
}

impl<E: sealed::Entity, V> std::ops::IndexMut<E> for EntityKeyedDenseMap<E, V> {
    fn index_mut(&mut self, entity: E) -> &mut V {
        self.get_mut(entity).expect("no entry found for key")
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
