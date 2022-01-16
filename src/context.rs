use elsa::FrozenIndexSet;
use rustc_hash::FxHashMap;
use std::cell::Cell;
use std::convert::TryInto;
use std::hash::Hash;

/// Context object with global resources for SPIR-T.
///
/// Those resources currently are:
/// * interners, for anything without an identity, and which can be deduplicated
/// * "entity" allocators, for everything else - i.e. anything with an identity
///   that needs to remain unique across an entire `Context`
///   * the *definition* of an entity isn't kept in the `Context`, but rather in
///     some `EntityDefs` collection somewhere in a `Module` (or further nested),
///     with only the entity *indices* being allocated by the `Context`
pub struct Context {
    interners: Interners,
    entity_allocs: EntityAllocs,
}

/// Dispatch helper, to allow implementing interning logic on
/// the type passed to `cx.intern(...)`.
pub trait InternInCx {
    type Interned;

    fn intern_in_cx(self, cx: &Context) -> Self::Interned;
}

impl Context {
    pub fn new() -> Self {
        Context {
            interners: Interners::default(),
            entity_allocs: EntityAllocs::default(),
        }
    }

    pub fn intern<T: InternInCx>(&self, x: T) -> T::Interned {
        x.intern_in_cx(self)
    }
}

/// Collection holding the actual definitions for `Context`-allocated entities.
///
/// The only `E` (entity) and `D` (entity definition) type combinations allowed
/// are the ones declared by the `entities!` macro below.
///
/// By design there is no way to iterate the contents of an `EntityDefs`, or
/// generate entity indices without defining the entity in an `EntityDefs`.
pub struct EntityDefs<E, D> {
    // FIXME(eddyb) use more efficient storage by optimizing for compact ranges,
    // allowing the use of `Vec` (plus the base index) for the fast path, and
    // keeping the map as a fallback.
    map: FxHashMap<E, D>,
}

impl<E, D> Default for EntityDefs<E, D> {
    fn default() -> Self {
        Self {
            map: FxHashMap::default(),
        }
    }
}

impl<E, D> EntityDefs<E, D> {
    pub fn new() -> Self {
        Self::default()
    }

    // NOTE(eddyb) `define`/`index` is defined by the `entities!` macro below.
}

struct Interner<T: ?Sized>(FrozenIndexSet<Box<T>>);

impl<T: ?Sized + Eq + Hash> Default for Interner<T> {
    fn default() -> Self {
        Self(FrozenIndexSet::new())
    }
}

impl<T: ?Sized + Eq + Hash> Interner<T> {
    #[track_caller]
    fn intern(&self, value: impl AsRef<T> + Into<Box<T>>) -> u32 {
        if let Some((i, _)) = self.0.get_full(value.as_ref()) {
            return i as u32;
        }
        let (i, _) = self.0.insert_full(value.into());
        i.try_into().expect("interner overflowed u32")
    }
}

macro_rules! interners {
    (
        needs_as_ref { $($needs_as_ref_ty:ty),* $(,)? }
        needs_default { $($needs_default_name:ident => $needs_default_ty:ty),* $(,)? }
        $($name:ident => $ty:ty),+ $(,)?
    ) => {
        $(impl AsRef<Self> for $needs_as_ref_ty {
            fn as_ref(&self) -> &Self {
                self
            }
        })*

        $(impl Default for $needs_default_name {
            fn default() -> Self {
                Self(0)
            }
        })*

        #[allow(non_snake_case)]
        struct Interners {
            $($name: Interner<$ty>),*
        }

        impl Default for Interners {
            fn default() -> Self {
                let interners = Self {
                    $($name: Default::default()),*
                };

                // Pre-intern every `$needs_default_{name,ty}`.
                $(assert_eq!(
                    interners.$needs_default_name.intern(<$needs_default_ty>::default()),
                    0
                );)*

                interners
            }
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

            impl std::ops::Index<$name> for Context {
                type Output = $ty;

                fn index(&self, interned: $name) -> &Self::Output {
                    &self.interners.$name.0[interned.0 as usize]
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
    needs_default {
        AttrSet => crate::AttrSetDef,
    }

    // FIXME(eddyb) consider a more uniform naming scheme than the combination
    // of `InternedFoo => Foo` and `Foo => FooDef`.
    InternedStr => str,
    AttrSet => crate::AttrSetDef,
    Type => crate::TypeDef,
    Const => crate::ConstDef,
}

impl InternInCx for &'_ str {
    type Interned = InternedStr;

    fn intern_in_cx(self, cx: &Context) -> InternedStr {
        InternedStr(cx.interners.InternedStr.intern(self))
    }
}

impl InternInCx for String {
    type Interned = InternedStr;

    fn intern_in_cx(self, cx: &Context) -> InternedStr {
        InternedStr(cx.interners.InternedStr.intern(self))
    }
}

// FIXME(eddyb) automate the common form of this away.
impl InternInCx for crate::AttrSetDef {
    type Interned = AttrSet;

    fn intern_in_cx(self, cx: &Context) -> Self::Interned {
        AttrSet(cx.interners.AttrSet.intern(self))
    }
}

// FIXME(eddyb) automate the common form of this away.
impl InternInCx for crate::TypeDef {
    type Interned = Type;

    fn intern_in_cx(self, cx: &Context) -> Self::Interned {
        Type(cx.interners.Type.intern(self))
    }
}

// FIXME(eddyb) automate the common form of this away.
impl InternInCx for crate::ConstDef {
    type Interned = Const;

    fn intern_in_cx(self, cx: &Context) -> Self::Interned {
        Const(cx.interners.Const.intern(self))
    }
}

macro_rules! entities {
    (
        $($name:ident => $def:ty),+ $(,)?
    ) => {
        #[allow(non_snake_case)]
        struct EntityAllocs {
            $($name: Cell<u32>),*
        }

        impl Default for EntityAllocs {
            fn default() -> Self {
                Self {
                    $($name: Default::default()),*
                }
            }
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

            impl EntityDefs<$name, $def> {
                pub fn define(&mut self, cx: &Context, def: $def) -> $name {
                    let idx = $name(cx.entity_allocs.$name.get());
                    let next_idx = idx.0.checked_add(1).expect("entity index overflowed u32");
                    cx.entity_allocs.$name.set(next_idx);

                    assert!(self.map.insert(idx, def).is_none());

                    idx
                }
            }

            impl std::ops::Index<$name> for EntityDefs<$name, $def> {
                type Output = $def;

                fn index(&self, idx: $name) -> &Self::Output {
                    &self.map[&idx]
                }
            }

            impl std::ops::IndexMut<$name> for EntityDefs<$name, $def> {
                fn index_mut(&mut self, idx: $name) -> &mut Self::Output {
                    self.map.get_mut(&idx).unwrap()
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
