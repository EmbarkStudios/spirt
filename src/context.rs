//! [`Context`](struct.Context.html) and related types/traits.

use rustc_hash::FxHashMap;
use std::hash::Hash;
use std::mem;
use std::num::NonZeroU32;
use std::ops::{Deref, DerefMut};

/// Context object with global resources for SPIR-T.
///
/// Those resources currently are:
/// * interners, for anything without an identity, and which can be deduplicated
/// * "entity" allocators, for everything else - i.e. anything with an identity
///   that needs to remain unique across an entire [`Context`]
///   * the *definition* of an entity isn't kept in the [`Context`], but rather in
///     some [`EntityDefs`] collection somewhere in a [`Module`](crate::Module) (or further nested),
///     with only the entity *indices* being allocated by the [`Context`]
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

    // FIXME(eddyb) one `Box` per element is inefficient, figure out if e.g.
    // the `rental` crate could allow keeping an `arena: TypedArena<I::Def>`
    // alongside the `FrozenIndexSet` (which would then use `&'arena I::Def`).
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

    // FIXME(eddyb) reflect "is an `Entity`" in a non-sealed way, by having an
    // e.g. `pub trait IsEntity: Entity {}` w/ a blanket impl, that users could
    // not implement themselves because of the `Entity` requirement, but could
    // still bound on, and it would imply `Entity` as needed - this could even
    // be named `Entity`, with `sealed::Entity` only used (by `context`) for:
    // - `impl sealed::Entity for $name` to define an entity
    // - `use sealed::Entity as _;` to use associated items from the trait
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
use sealed::Entity as _;

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

// FIXME(eddyb) consider including `Rc<Context>` in `EntityDefs` to avoid having
// to pass it manually to the `EntityDefs::define` methods (which feels dangerous!).
//
/// Collection holding the actual definitions for [`Context`]-allocated entities.
///
/// By design there is no way to iterate the contents of an [`EntityDefs`], or
/// generate entity indices without defining the entity in an [`EntityDefs`].
#[derive(Clone)]
pub struct EntityDefs<E: sealed::Entity> {
    /// Entities are grouped into chunks, with per-entity-type chunk sizes
    /// (powers of 2) specified via `entities!` below.
    /// This allows different [`EntityDefs`]s to independently define more
    /// entities, without losing compactness (until a whole chunk is filled).
    //
    // FIXME(eddyb) consider using `u32` instead of `usize` for the "flattened base".
    complete_chunk_start_to_flattened_base: FxHashMap<E, usize>,

    /// Similar to a single entry in `complete_chunk_start_to_flattened_base`,
    /// but kept outside of the map for efficiency. Also, this is the only
    /// chunk that doesn't have its full size already (and therefore allows
    /// defining more entities into it, without allocating new chunks).
    incomplete_chunk_start_and_flattened_base: Option<(E, usize)>,

    /// All chunks' definitions are flattened into one contiguous [`Vec`], where
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

                // This is the last entity in this chunk, completing it.
                // NB: no new chunk is allocated here, but instead the next
                // `define` call will find no incomplete chunk, which will
                // prompt it to allocate a new chunk itself.
                if chunk_len == (E::CHUNK_SIZE - 1) as usize {
                    self.complete_chunk_start_to_flattened_base
                        .extend(self.incomplete_chunk_start_and_flattened_base.take());
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

/// `EntityOriented*Map<Self, V>` support trait, implemented for entity types,
/// but which can also be implemented by users for their own newtypes and other
/// types wrapping entity types (such as finite `enum`s).
pub trait EntityOrientedMapKey<V>: Copy {
    /// The entity type that appears exactly once in every value of `Self`.
    type Entity: sealed::Entity;
    fn to_entity(key: Self) -> Self::Entity;

    /// A type holding enough different `Option<V>` slots, for all possible
    /// values of `Self`, for a given `Self::Entity` value contained inside.
    //
    // FIXME(eddyb) consider making this just an array length?
    type DenseValueSlots: Default;
    fn get_dense_value_slot(key: Self, slots: &Self::DenseValueSlots) -> &Option<V>;
    fn get_dense_value_slot_mut(key: Self, slots: &mut Self::DenseValueSlots) -> &mut Option<V>;
}

impl<E: sealed::Entity, V> EntityOrientedMapKey<V> for E {
    type Entity = E;
    fn to_entity(key: E) -> E {
        key
    }

    type DenseValueSlots = Option<V>;
    fn get_dense_value_slot(_: Self, slot: &Option<V>) -> &Option<V> {
        slot
    }
    fn get_dense_value_slot_mut(_: Self, slot: &mut Option<V>) -> &mut Option<V> {
        slot
    }
}

/// Map with `K` keys and `V` values, that is:
/// * "entity-oriented" `K` keys, i.e. that are or contain exactly one entity
///   (supported via [`K: EntityOrientedMapKey<V>`](EntityOrientedMapKey) for extensibility)
/// * "dense" in the sense of few (or no) gaps in (the entities in) its keys
///   (relative to the entities defined in the corresponding [`EntityDefs`])
///
/// By design there is no way to iterate the entries in an [`EntityOrientedDenseMap`].
//
// FIXME(eddyb) implement a "sparse" version as well, and maybe some bitsets?
#[derive(Clone)]
pub struct EntityOrientedDenseMap<K: EntityOrientedMapKey<V>, V> {
    /// Like in [`EntityDefs`], entities are grouped into chunks, but there is no
    /// flattening, since arbitrary insertion orders have to be supported.
    chunk_start_to_value_slots: SmallFxHashMap<K::Entity, Vec<K::DenseValueSlots>>,
}

// FIXME(eddyb) find a better "small map" design and/or fine-tune this - though,
// since the ideal state is one chunk per map, the slow case might never be hit,
// unless one `EntityOrientedDenseMap` is used with more than one `EntityDefs`,
// which could still maybe be implemented more efficiently than `FxHashMap`.
#[derive(Clone)]
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
        #[allow(clippy::match_same_arms)]
        match self {
            Self::Empty => None,
            Self::One(old_k, old_v) if *old_k == k => Some(old_v),
            Self::One(..) => None,
            Self::More(map) => map.get(&k),
        }
    }

    fn get_mut(&mut self, k: K) -> Option<&mut V> {
        #[allow(clippy::match_same_arms)]
        match self {
            Self::Empty => None,
            Self::One(old_k, old_v) if *old_k == k => Some(old_v),
            Self::One(..) => None,
            Self::More(map) => map.get_mut(&k),
        }
    }
}

impl<K: EntityOrientedMapKey<V>, V> Default for EntityOrientedDenseMap<K, V> {
    fn default() -> Self {
        Self {
            chunk_start_to_value_slots: Default::default(),
        }
    }
}

impl<K: EntityOrientedMapKey<V>, V> EntityOrientedDenseMap<K, V> {
    pub fn new() -> Self {
        Self::default()
    }

    // FIXME(eddyb) this should not allocate space unconditionally, but offer an
    // API where "vacant entry" may or may not have a `&mut Option<V>` in it.
    pub fn entry(&mut self, key: K) -> &mut Option<V> {
        let entity = K::to_entity(key);
        let (chunk_start, intra_chunk_idx) = entity.to_chunk_start_and_intra_chunk_idx();
        let chunk_value_slots = self
            .chunk_start_to_value_slots
            .get_mut_or_insert_default(chunk_start);

        // Ensure there are enough slots for the new entry.
        let needed_len = intra_chunk_idx + 1;
        if chunk_value_slots.len() < needed_len {
            chunk_value_slots.resize_with(needed_len, Default::default);
        }

        let value_slots = &mut chunk_value_slots[intra_chunk_idx];
        K::get_dense_value_slot_mut(key, value_slots)
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.entry(key).replace(value)
    }

    pub fn get(&self, key: K) -> Option<&V> {
        let entity = K::to_entity(key);
        let (chunk_start, intra_chunk_idx) = entity.to_chunk_start_and_intra_chunk_idx();
        let value_slots = self
            .chunk_start_to_value_slots
            .get(chunk_start)?
            .get(intra_chunk_idx)?;
        K::get_dense_value_slot(key, value_slots).as_ref()
    }

    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        self.get_slot_mut(key)?.as_mut()
    }

    pub fn remove(&mut self, key: K) -> Option<V> {
        self.get_slot_mut(key)?.take()
    }

    // FIXME(eddyb) deduplicate with `entry`.
    fn get_slot_mut(&mut self, key: K) -> Option<&mut Option<V>> {
        let entity = K::to_entity(key);
        let (chunk_start, intra_chunk_idx) = entity.to_chunk_start_and_intra_chunk_idx();
        let value_slots = self
            .chunk_start_to_value_slots
            .get_mut(chunk_start)?
            .get_mut(intra_chunk_idx)?;
        Some(K::get_dense_value_slot_mut(key, value_slots))
    }
}

impl<K: EntityOrientedMapKey<V>, V> std::ops::Index<K> for EntityOrientedDenseMap<K, V> {
    type Output = V;

    fn index(&self, key: K) -> &V {
        self.get(key).expect("no entry found for key")
    }
}

impl<K: EntityOrientedMapKey<V>, V> std::ops::IndexMut<K> for EntityOrientedDenseMap<K, V> {
    fn index_mut(&mut self, key: K) -> &mut V {
        self.get_mut(key).expect("no entry found for key")
    }
}

#[allow(rustdoc::private_intra_doc_links)]
/// Doubly-linked list, "intrusively" going through `E::Def`, which must be an
/// [`EntityListNode<E, _>`] (to hold the "previous/next node" links).
///
/// Fields are private to avoid arbitrary user interactions.
#[derive(Copy, Clone)]
pub struct EntityList<E: sealed::Entity>(Option<FirstLast<E, E>>);

// HACK(eddyb) this only exists to give field names to the non-empty case.
#[derive(Copy, Clone)]
struct FirstLast<F, L> {
    first: F,
    last: L,
}

impl<E: sealed::Entity> Default for EntityList<E> {
    fn default() -> Self {
        Self(None)
    }
}

impl<E: sealed::Entity<Def = EntityListNode<E, D>>, D> EntityList<E> {
    pub fn empty() -> Self {
        Self::default()
    }

    pub fn is_empty(self) -> bool {
        self.0.is_none()
    }

    pub fn iter(self) -> EntityListIter<E> {
        EntityListIter {
            first: self.0.map(|list| list.first),
            last: self.0.map(|list| list.last),
        }
    }

    /// Insert `new_node` (defined in `defs`) at the start of `self`.
    #[track_caller]
    pub fn insert_first(&mut self, new_node: E, defs: &mut EntityDefs<E>) {
        let new_node_def = &mut defs[new_node];
        assert!(
            new_node_def.prev.is_none() && new_node_def.next.is_none(),
            "EntityList::insert_first: new node already linked into a (different?) list"
        );

        new_node_def.next = self.0.map(|this| this.first);
        if let Some(old_first) = new_node_def.next {
            let old_first_def = &mut defs[old_first];

            // FIXME(eddyb) this situation should be impossible anyway, as it
            // involves the `EntityListNode`s links, which should be unforgeable,
            // but it's still possible to keep around outdated `EntityList`s
            // (should `EntityList` not implement `Copy`/`Clone` *at all*?)
            assert!(
                old_first_def.prev.is_none(),
                "invalid EntityList: `first->prev != None`"
            );

            old_first_def.prev = Some(new_node);
        }

        self.0 = Some(FirstLast {
            first: new_node,
            last: self.0.map_or(new_node, |this| this.last),
        });
    }

    /// Insert `new_node` (defined in `defs`) at the end of `self`.
    #[track_caller]
    pub fn insert_last(&mut self, new_node: E, defs: &mut EntityDefs<E>) {
        let new_node_def = &mut defs[new_node];
        assert!(
            new_node_def.prev.is_none() && new_node_def.next.is_none(),
            "EntityList::insert_last: new node already linked into a (different?) list"
        );

        new_node_def.prev = self.0.map(|this| this.last);
        if let Some(old_last) = new_node_def.prev {
            let old_last_def = &mut defs[old_last];

            // FIXME(eddyb) this situation should be impossible anyway, as it
            // involves the `EntityListNode`s links, which should be unforgeable,
            // but it's still possible to keep around outdated `EntityList`s
            // (should `EntityList` not implement `Copy`/`Clone` *at all*?)
            assert!(
                old_last_def.next.is_none(),
                "invalid EntityList: `last->next != None`"
            );

            old_last_def.next = Some(new_node);
        }

        self.0 = Some(FirstLast {
            first: self.0.map_or(new_node, |this| this.first),
            last: new_node,
        });
    }

    /// Insert `new_node` (defined in `defs`) into `self`, before `next`.
    //
    // FIXME(eddyb) unify this with the other insert methods, maybe with a new
    // "insert position" type?
    #[track_caller]
    pub fn insert_before(&mut self, new_node: E, next: E, defs: &mut EntityDefs<E>) {
        let prev = defs[next].prev.replace(new_node);

        let new_node_def = &mut defs[new_node];
        assert!(
            new_node_def.prev.is_none() && new_node_def.next.is_none(),
            "EntityList::insert_before: new node already linked into a (different?) list"
        );

        new_node_def.prev = prev;
        new_node_def.next = Some(next);

        match prev {
            Some(prev) => {
                let old_prev_next = defs[prev].next.replace(new_node);

                // FIXME(eddyb) this situation should be impossible anyway, as it
                // involves the `EntityListNode`s links, which should be unforgeable.
                assert!(
                    old_prev_next == Some(next),
                    "invalid EntityListNode: `node->prev->next != node`"
                );
            }
            None => {
                // FIXME(eddyb) this situation should be impossible anyway, as it
                // involves the `EntityListNode`s links, which should be unforgeable,
                // but it's still possible to keep around outdated `EntityList`s
                // (should `EntityList` not implement `Copy`/`Clone` *at all*?)
                assert!(
                    self.0.map(|this| this.first) == Some(next),
                    "invalid EntityList: `node->prev == None` but `node != first`"
                );

                self.0.as_mut().unwrap().first = new_node;
            }
        }
    }

    /// Insert all of `list_to_prepend`'s nodes at the start of `self`.
    #[track_caller]
    pub fn prepend(&mut self, list_to_prepend: Self, defs: &mut EntityDefs<E>) {
        *self = Self::concat(list_to_prepend, *self, defs);
    }

    /// Insert all of `list_to_append`'s nodes at the end of `self`.
    #[track_caller]
    pub fn append(&mut self, list_to_append: Self, defs: &mut EntityDefs<E>) {
        *self = Self::concat(*self, list_to_append, defs);
    }

    /// Private helper for `prepend`/`append`.
    #[track_caller]
    fn concat(a: Self, b: Self, defs: &mut EntityDefs<E>) -> Self {
        let (a, b) = match (a.0, b.0) {
            (Some(a), Some(b)) => (a, b),
            (a, b) => return Self(a.or(b)),
        };

        {
            let a_last_def = &mut defs[a.last];

            // FIXME(eddyb) this situation should be impossible anyway, as it
            // involves the `EntityListNode`s links, which should be unforgeable,
            // but it's still possible to keep around outdated `EntityList`s
            // (should `EntityList` not implement `Copy`/`Clone` *at all*?)
            assert!(
                a_last_def.next.is_none(),
                "invalid EntityList: `last->next != None`"
            );

            a_last_def.next = Some(b.first);
        }
        {
            let b_first_def = &mut defs[b.first];

            // FIXME(eddyb) this situation should be impossible anyway, as it
            // involves the `EntityListNode`s links, which should be unforgeable,
            // but it's still possible to keep around outdated `EntityList`s
            // (should `EntityList` not implement `Copy`/`Clone` *at all*?)
            assert!(
                b_first_def.prev.is_none(),
                "invalid EntityList: `first->prev != None`"
            );

            b_first_def.prev = Some(a.last);
        }

        Self(Some(FirstLast {
            first: a.first,
            last: b.last,
        }))
    }

    /// Remove `node` (defined in `defs`) from `self`.
    #[track_caller]
    pub fn remove(&mut self, node: E, defs: &mut EntityDefs<E>) {
        // Unlink `node->{prev,next}` first (also allowing re-insertion elsewhere).
        let (prev, next) = {
            let node_def = &mut defs[node];
            (node_def.prev.take(), node_def.next.take())
        };

        // Unlink `prev->next = node` (or validate `first = node`).
        match prev {
            Some(prev) => {
                let old_prev_next = mem::replace(&mut defs[prev].next, next);

                // FIXME(eddyb) this situation should be impossible anyway, as it
                // involves the `EntityListNode`s links, which should be unforgeable.
                assert!(
                    old_prev_next == Some(node),
                    "invalid EntityListNode: `node->prev->next != node`"
                );
            }
            None => {
                // FIXME(eddyb) this situation should be impossible anyway, as it
                // involves the `EntityListNode`s links, which should be unforgeable,
                // but it's still possible to keep around outdated `EntityList`s
                // (should `EntityList` not implement `Copy`/`Clone` *at all*?)
                assert!(
                    self.0.map(|this| this.first) == Some(node),
                    "invalid EntityList: `node->prev == None` but `node != first`"
                );
            }
        }

        // Unlink `next->prev = node` (or validate `last = node`).
        match next {
            Some(next) => {
                let old_next_prev = mem::replace(&mut defs[next].prev, prev);

                // FIXME(eddyb) this situation should be impossible anyway, as it
                // involves the `EntityListNode`s links, which should be unforgeable.
                assert!(
                    old_next_prev == Some(node),
                    "invalid EntityListNode: `node->next->prev != node`"
                );
            }
            None => {
                // FIXME(eddyb) this situation should be impossible anyway, as it
                // involves the `EntityListNode`s links, which should be unforgeable,
                // but it's still possible to keep around outdated `EntityList`s
                // (should `EntityList` not implement `Copy`/`Clone` *at all*?)
                assert!(
                    self.0.map(|this| this.last) == Some(node),
                    "invalid EntityList: `node->next == None` but `node != last`"
                );
            }
        }

        // Update list end-points (overwritten `first`/`last` validated above).
        match (prev, next) {
            (Some(_), Some(_)) => {}
            (None, Some(next)) => self.0.as_mut().unwrap().first = next,
            (Some(prev), None) => self.0.as_mut().unwrap().last = prev,
            (None, None) => self.0 = None,
        }
    }
}

/// [`EntityList<E>`] iterator, but with a different API than [`Iterator`].
///
/// This can also be considered a (non-random-access) "subslice" of the list.
#[derive(Copy, Clone)]
pub struct EntityListIter<E: sealed::Entity> {
    pub first: Option<E>,
    pub last: Option<E>,
}

impl<E: sealed::Entity<Def = EntityListNode<E, D>>, D> EntityListIter<E> {
    #[track_caller]
    pub fn split_first(self, defs: &EntityDefs<E>) -> Option<(E, Self)> {
        let Self { first, last } = self;
        let current = first?;
        let next = defs[current].next;
        match next {
            // FIXME(eddyb) this situation should be impossible anyway, as it
            // involves the `EntityListNode`s links, which should be unforgeable.
            Some(next) => assert!(
                defs[next].prev == Some(current),
                "invalid EntityListNode: `node->next->prev != node`"
            ),

            None => assert!(
                Some(current) == last,
                "invalid EntityListIter: `first->next->...->next != last`"
            ),
        }
        Some((current, Self { first: next, last }))
    }

    #[track_caller]
    pub fn split_last(self, defs: &EntityDefs<E>) -> Option<(E, Self)> {
        let Self { first, last } = self;
        let current = last?;
        let prev = defs[current].prev;
        match prev {
            // FIXME(eddyb) this situation should be impossible anyway, as it
            // involves the `EntityListNode`s links, which should be unforgeable.
            Some(prev) => assert!(
                defs[prev].next == Some(current),
                "invalid EntityListNode: `node->prev->next != node`"
            ),

            None => assert!(
                Some(current) == first,
                "invalid EntityListIter: `last->prev->...->prev != first`"
            ),
        }
        Some((current, Self { first, last: prev }))
    }
}

/// [`EntityList<E>`] node, containing the "intrusive" list links, and the rest of
/// the entity definition (the `inner_def` field of type `D`).
///
/// Fields are private to avoid arbitrary user interactions outside of special
/// methods and [`Deref`]/[`DerefMut`].
//
// FIXME(eddyb) `Deref`/`DerefMut` aren't the best API, could this be hidden
// further by making `EntityDefs` hide the list links in the `Index` impl?
#[derive(Clone)]
pub struct EntityListNode<E: sealed::Entity<Def = Self>, D> {
    prev: Option<E>,
    next: Option<E>,

    inner_def: D,
}

impl<E: sealed::Entity<Def = Self>, D> From<D> for EntityListNode<E, D> {
    fn from(inner_def: D) -> Self {
        Self {
            prev: None,
            next: None,
            inner_def,
        }
    }
}

impl<E: sealed::Entity<Def = Self>, D> EntityListNode<E, D> {
    pub fn prev_in_list(&self) -> Option<E> {
        self.prev
    }
    pub fn next_in_list(&self) -> Option<E> {
        self.next
    }
}

impl<E: sealed::Entity<Def = Self>, D> Deref for EntityListNode<E, D> {
    type Target = D;
    fn deref(&self) -> &D {
        &self.inner_def
    }
}

impl<E: sealed::Entity<Def = Self>, D> DerefMut for EntityListNode<E, D> {
    fn deref_mut(&mut self) -> &mut D {
        &mut self.inner_def
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
                #[doc(hidden)] u32,
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
        crate::DataInstFormDef,
    }

    // FIXME(eddyb) consider a more uniform naming scheme than the combination
    // of `InternedFoo => Foo` and `Foo => FooDef`.
    InternedStr => str,
    AttrSet default(crate::AttrSetDef::default()) => crate::AttrSetDef,
    Type => crate::TypeDef,
    Const => crate::ConstDef,
    DataInstForm => crate::DataInstFormDef,
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
            pub struct $name(#[doc(hidden)] NonZeroU32);

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
    ControlRegion => chunk_size(0x1000) crate::ControlRegionDef,
    ControlNode => chunk_size(0x1000) EntityListNode<ControlNode, crate::ControlNodeDef>,
    DataInst => chunk_size(0x1000) EntityListNode<DataInst, crate::DataInstDef>,
}
