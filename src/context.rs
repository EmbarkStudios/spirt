use rustc_hash::FxHashMap;

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
    pub trait Interned: Sized + 'static {
        type Def: ?Sized + Eq + std::hash::Hash;

        fn preintern(_interner: &Interner<Self>) {}
        fn from_u32(i: u32) -> Self;
        fn to_u32(self) -> u32;
        fn cx_interner(cx: &super::Context) -> &Interner<Self>;
    }

    pub struct Interner<I: Interned>(elsa::FrozenIndexSet<Box<I::Def>>);

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

        fn from_u32(i: u32) -> Self;
        fn to_u32(self) -> u32;
        fn cx_entity_alloc(cx: &super::Context) -> &EntityAlloc<Self>;
    }

    pub struct EntityAlloc<E: Entity>(std::cell::Cell<E>);

    impl<E: Entity> Default for EntityAlloc<E> {
        fn default() -> Self {
            Self(std::cell::Cell::new(E::from_u32(0)))
        }
    }

    impl<E: Entity> EntityAlloc<E> {
        #[track_caller]
        pub(super) fn alloc(&self) -> E {
            let entity = self.0.get();
            let next_entity = E::from_u32(
                entity
                    .to_u32()
                    .checked_add(1)
                    .expect("entity index overflowed u32"),
            );
            self.0.set(next_entity);
            entity
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
    // FIXME(eddyb) use more efficient storage by optimizing for compact ranges,
    // allowing the use of `Vec` (plus the base index) for the fast path, and
    // keeping the map as a fallback.
    map: FxHashMap<E, E::Def>,
}

impl<E: sealed::Entity> Default for EntityDefs<E> {
    fn default() -> Self {
        Self {
            map: FxHashMap::default(),
        }
    }
}

impl<E: sealed::Entity> EntityDefs<E> {
    pub fn new() -> Self {
        Self::default()
    }

    #[track_caller]
    pub fn define(&mut self, cx: &Context, def: E::Def) -> E {
        let entity = E::cx_entity_alloc(cx).alloc();
        assert!(self.map.insert(entity, def).is_none());
        entity
    }
}

impl<E: sealed::Entity> std::ops::Index<E> for EntityDefs<E> {
    type Output = E::Def;

    fn index(&self, entity: E) -> &Self::Output {
        &self.map[&entity]
    }
}

impl<E: sealed::Entity> std::ops::IndexMut<E> for EntityDefs<E> {
    fn index_mut(&mut self, entity: E) -> &mut Self::Output {
        self.map.get_mut(&entity).unwrap()
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
        $($name:ident => $def:ty),+ $(,)?
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
            pub struct $name(
                // FIXME(eddyb) figure out how to sneak niches into these types, to
                // allow e.g. `Option` around them to not increase the size.
                u32,
            );

            impl sealed::Entity for $name {
                type Def = $def;

                #[inline(always)]
                fn from_u32(i: u32) -> Self {
                    Self(i)
                }
                #[inline(always)]
                fn to_u32(self) -> u32 {
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
    GlobalVar => crate::GlobalVarDecl,
    Func => crate::FuncDecl,
    Region => crate::RegionDef,
    DataInst => crate::DataInstDef,
}
