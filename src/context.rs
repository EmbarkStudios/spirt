use crate::AttrSetDef;
use elsa::FrozenIndexSet;
use std::convert::TryInto;
use std::hash::Hash;

/// Context object with global resources for SPIR-T, such as interners.
pub struct Context {
    interners: Interners,
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
        }
    }

    pub fn intern<T: InternInCx>(&self, x: T) -> T::Interned {
        x.intern_in_cx(self)
    }
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
                let interners = Interners {
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
            pub struct $name(u32);

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
        AttrSetDef,
    }
    needs_default {
        AttrSet => AttrSetDef,
    }

    // FIXME(eddyb) consider a more uniform naming scheme than the combination
    // of `InternedFoo => Foo` and `Foo => FooDef`.
    InternedStr => str,
    AttrSet => AttrSetDef,
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
impl InternInCx for AttrSetDef {
    type Interned = AttrSet;

    fn intern_in_cx(self, cx: &Context) -> Self::Interned {
        AttrSet(cx.interners.AttrSet.intern(self))
    }
}
