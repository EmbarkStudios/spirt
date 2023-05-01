//! [`QPtr`](crate::TypeCtor::QPtr) usage analysis (for legalizing/lifting).

// HACK(eddyb) sharing layout code with other modules.
use super::{layout::*, QPtrMemUsageKind};

use super::{shapes, QPtrAttr, QPtrMemUsage, QPtrOp, QPtrUsage};
use crate::func_at::FuncAt;
use crate::visit::{InnerVisit, Visitor};
use crate::{
    AddrSpace, Attr, AttrSet, AttrSetDef, Const, ConstCtor, Context, ControlNode, ControlNodeKind,
    DataInst, DataInstForm, DataInstKind, DeclDef, Diag, EntityList, ExportKey, Exportee, Func,
    FxIndexMap, GlobalVar, Module, OrdAssertEq, Type, TypeCtor, Value,
};
use itertools::Either;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use std::mem;
use std::num::NonZeroU32;
use std::ops::Bound;
use std::rc::Rc;

#[derive(Clone)]
struct AnalysisError(Diag);

struct UsageMerger<'a> {
    layout_cache: &'a LayoutCache<'a>,
}

/// Result type for `UsageMerger` methods - unlike `Result<T, AnalysisError>`,
/// this always keeps the `T` value, even in the case of an error.
struct MergeResult<T> {
    merged: T,
    error: Option<AnalysisError>,
}

impl<T> MergeResult<T> {
    fn ok(merged: T) -> Self {
        Self {
            merged,
            error: None,
        }
    }

    fn into_result(self) -> Result<T, AnalysisError> {
        let Self { merged, error } = self;
        match error {
            None => Ok(merged),
            Some(e) => Err(e),
        }
    }

    fn map<U>(self, f: impl FnOnce(T) -> U) -> MergeResult<U> {
        let Self { merged, error } = self;
        let merged = f(merged);
        MergeResult { merged, error }
    }
}

impl UsageMerger<'_> {
    fn merge(&self, a: QPtrUsage, b: QPtrUsage) -> MergeResult<QPtrUsage> {
        match (a, b) {
            (
                QPtrUsage::Handles(shapes::Handle::Opaque(a)),
                QPtrUsage::Handles(shapes::Handle::Opaque(b)),
            ) if a == b => MergeResult::ok(QPtrUsage::Handles(shapes::Handle::Opaque(a))),

            (
                QPtrUsage::Handles(shapes::Handle::Buffer(a_as, a)),
                QPtrUsage::Handles(shapes::Handle::Buffer(b_as, b)),
            ) => {
                // HACK(eddyb) the `AddrSpace` field is entirely redundant.
                assert!(a_as == AddrSpace::Handles && b_as == AddrSpace::Handles);

                self.merge_mem(a, b).map(|usage| {
                    QPtrUsage::Handles(shapes::Handle::Buffer(AddrSpace::Handles, usage))
                })
            }

            (QPtrUsage::Memory(a), QPtrUsage::Memory(b)) => {
                self.merge_mem(a, b).map(QPtrUsage::Memory)
            }

            (a, b) => {
                MergeResult {
                    // FIXME(eddyb) there may be a better choice here, but it
                    // generally doesn't matter, as this method only has one
                    // caller, and it just calls `.into_result()` right away.
                    merged: a.clone(),
                    error: Some(AnalysisError(Diag::bug([
                        "merge: ".into(),
                        a.into(),
                        " vs ".into(),
                        b.into(),
                    ]))),
                }
            }
        }
    }

    fn merge_mem(&self, a: QPtrMemUsage, b: QPtrMemUsage) -> MergeResult<QPtrMemUsage> {
        // NOTE(eddyb) this is possible because it's currently impossible for
        // the merged usage to be outside the bounds of *both* `a` and `b`.
        let max_size = match (a.max_size, b.max_size) {
            (Some(a), Some(b)) => Some(a.max(b)),
            (None, _) | (_, None) => None,
        };

        // Ensure that `a` is "larger" than `b`, or at least the same size
        // (when either they're identical, or one is a "newtype" of the other),
        // to make it easier to handle all the possible interactions below,
        // by skipping (or deprioritizing, if supported) the "wrong direction".
        let mut sorted = [a, b];
        sorted.sort_by_key(|usage| {
            #[derive(PartialEq, Eq, PartialOrd, Ord)]
            enum MaxSize<T> {
                Fixed(T),
                // FIXME(eddyb) this probably needs to track "min size"?
                Dynamic,
            }
            let max_size = usage.max_size.map_or(MaxSize::Dynamic, MaxSize::Fixed);

            // When sizes are equal, pick the more restrictive side.
            #[derive(PartialEq, Eq, PartialOrd, Ord)]
            enum TypeStrictness {
                Any,
                Array,
                Exact,
            }
            #[allow(clippy::match_same_arms)]
            let type_strictness = match usage.kind {
                QPtrMemUsageKind::Unused | QPtrMemUsageKind::OffsetBase(_) => TypeStrictness::Any,

                QPtrMemUsageKind::DynOffsetBase { .. } => TypeStrictness::Array,

                // FIXME(eddyb) this should be `Any`, even if in theory it
                // could contain arrays or structs that need decomposition
                // (note that, for typed reads/write, arrays do not need to be
                // *indexed* to work, i.e. they *do not* require `DynOffset`s,
                // `Offset`s suffice, and for them `DynOffsetBase` is at most
                // a "run-length"/deduplication optimization over `OffsetBase`).
                // NOTE(eddyb) this should still prefer `OpTypeVector` over `DynOffsetBase`!
                QPtrMemUsageKind::DirectAccess(_) => TypeStrictness::Exact,

                QPtrMemUsageKind::StrictlyTyped(_) => TypeStrictness::Exact,
            };

            (max_size, type_strictness)
        });
        let [b, a] = sorted;
        assert_eq!(max_size, a.max_size);

        self.merge_mem_at(a, 0, b)
    }

    // FIXME(eddyb) make the name of this clarify the asymmetric effect, something
    // like "make `a` compatible with `offset => b`".
    fn merge_mem_at(
        &self,
        a: QPtrMemUsage,
        b_offset_in_a: u32,
        b: QPtrMemUsage,
    ) -> MergeResult<QPtrMemUsage> {
        // NOTE(eddyb) this is possible because it's currently impossible for
        // the merged usage to be outside the bounds of *both* `a` and `b`.
        let max_size = match (a.max_size, b.max_size) {
            (Some(a), Some(b)) => Some(a.max(b.checked_add(b_offset_in_a).unwrap())),
            (None, _) | (_, None) => None,
        };

        // HACK(eddyb) we require biased `a` vs `b` (see `merge_mem` method above).
        assert_eq!(max_size, a.max_size);

        // Decompose the "smaller" and/or "less strict" side (`b`) first.
        match b.kind {
            // `Unused`s are always ignored.
            QPtrMemUsageKind::Unused => return MergeResult::ok(a),

            QPtrMemUsageKind::OffsetBase(b_entries)
                if {
                    // HACK(eddyb) this check was added later, after it turned out
                    // that *deep* flattening of arbitrary offsets in `b` would've
                    // required constant-folding of `qptr.offset` in `qptr::lift`,
                    // to not need all the type nesting levels for `OpAccessChain`.
                    b_offset_in_a == 0
                } =>
            {
                // FIXME(eddyb) this whole dance only needed due to `Rc`.
                let b_entries = Rc::try_unwrap(b_entries);
                let b_entries = match b_entries {
                    Ok(entries) => Either::Left(entries.into_iter()),
                    Err(ref entries) => Either::Right(entries.iter().map(|(&k, v)| (k, v.clone()))),
                };

                let mut ab = a;
                let mut all_errors = None;
                for (b_offset, b_sub_usage) in b_entries {
                    let MergeResult {
                        merged,
                        error: new_error,
                    } = self.merge_mem_at(
                        ab,
                        b_offset.checked_add(b_offset_in_a).unwrap(),
                        b_sub_usage,
                    );
                    ab = merged;

                    // FIXME(eddyb) move some of this into `MergeResult`!
                    if let Some(AnalysisError(e)) = new_error {
                        let all_errors = &mut all_errors
                            .get_or_insert(AnalysisError(Diag::bug([])))
                            .0
                            .message;
                        // FIXME(eddyb) should this mean `MergeResult` should
                        // use `errors: Vec<AnalysisError>` instead of `Option`?
                        if !all_errors.is_empty() {
                            all_errors.push("\n".into());
                        }
                        // FIXME(eddyb) this is scuffed because the error might
                        // (or really *should*) already refer to the right offset!
                        all_errors.push(format!("+{b_offset} => ").into());
                        all_errors.extend(e.message);
                    }
                }
                return MergeResult {
                    merged: ab,
                    // FIXME(eddyb) should this mean `MergeResult` should
                    // use `errors: Vec<AnalysisError>` instead of `Option`?
                    error: all_errors.map(|AnalysisError(mut e)| {
                        e.message.insert(0, "merge_mem: conflicts:\n".into());
                        AnalysisError(e)
                    }),
                };
            }

            _ => {}
        }

        let kind = match a.kind {
            // `Unused`s are always ignored.
            QPtrMemUsageKind::Unused => MergeResult::ok(b.kind),

            // Typed leaves must support any possible usage applied to them
            // (when they match, or overtake, that usage, in size, like here),
            // with their inherent hierarchy (i.e. their array/struct nesting).
            QPtrMemUsageKind::StrictlyTyped(a_type) | QPtrMemUsageKind::DirectAccess(a_type) => {
                let b_type_at_offset_0 = match b.kind {
                    QPtrMemUsageKind::StrictlyTyped(b_type)
                    | QPtrMemUsageKind::DirectAccess(b_type)
                        if b_offset_in_a == 0 =>
                    {
                        Some(b_type)
                    }
                    _ => None,
                };
                let ty = if Some(a_type) == b_type_at_offset_0 {
                    MergeResult::ok(a_type)
                } else {
                    // Returns `Some(MergeResult::ok(ty))` iff `usage` is valid
                    // for type `ty`, and `None` iff invalid w/o layout errors
                    // (see `mem_layout_supports_usage_at_offset` for more details).
                    let type_supporting_usage_at_offset = |ty, usage_offset, usage| {
                        let supports_usage = match self.layout_of(ty) {
                            // FIXME(eddyb) should this be `unreachable!()`? also, is
                            // it possible to end up with `ty` being an `OpTypeStruct`
                            // decorated with `Block`, showing up as a `Buffer` handle?
                            //
                            // NOTE(eddyb) `Block`-annotated buffer types are *not*
                            // usable anywhere inside buffer data, since they would
                            // conflict with our own `Block`-annotated wrapper.
                            Ok(TypeLayout::Handle(_) | TypeLayout::HandleArray(..)) => {
                                Err(AnalysisError(Diag::bug([
                                    "merge_mem: impossible handle type for QPtrMemUsage".into(),
                                ])))
                            }
                            Ok(TypeLayout::Concrete(concrete)) => {
                                Ok(concrete.supports_usage_at_offset(usage_offset, usage))
                            }

                            Err(e) => Err(e),
                        };
                        match supports_usage {
                            Ok(false) => None,
                            Ok(true) | Err(_) => Some(MergeResult {
                                merged: ty,
                                error: supports_usage.err(),
                            }),
                        }
                    };

                    type_supporting_usage_at_offset(a_type, b_offset_in_a, &b)
                        .or_else(|| {
                            b_type_at_offset_0.and_then(|b_type_at_offset_0| {
                                type_supporting_usage_at_offset(b_type_at_offset_0, 0, &a)
                            })
                        })
                        .unwrap_or_else(|| {
                            MergeResult {
                                merged: a_type,
                                // FIXME(eddyb) this should ideally embed the types in the
                                // error somehow.
                                error: Some(AnalysisError(Diag::bug([
                                    "merge_mem: type subcomponents incompatible with usage ("
                                        .into(),
                                    QPtrUsage::Memory(a.clone()).into(),
                                    " vs ".into(),
                                    QPtrUsage::Memory(b.clone()).into(),
                                    ")".into(),
                                ]))),
                            }
                        })
                };

                // FIXME(eddyb) if the chosen (maybe-larger) side isn't strict,
                // it should also be possible to expand it into its components,
                // with the other (maybe-smaller) side becoming a leaf.

                // FIXME(eddyb) this might not enough because the
                // strict leaf could be *nested* inside `b`!!!
                let is_strict = |kind| matches!(kind, &QPtrMemUsageKind::StrictlyTyped(_));
                if is_strict(&a.kind) || is_strict(&b.kind) {
                    ty.map(QPtrMemUsageKind::StrictlyTyped)
                } else {
                    ty.map(QPtrMemUsageKind::DirectAccess)
                }
            }

            QPtrMemUsageKind::DynOffsetBase {
                element: mut a_element,
                stride: a_stride,
            } => {
                let b_offset_in_a_element = b_offset_in_a % a_stride;

                // Array-like dynamic offsetting needs to always merge any usage that
                // fits inside the stride, with its "element" usage, no matter how
                // complex it may be (notably, this is needed for nested arrays).
                if b.max_size
                    .and_then(|b_max_size| b_max_size.checked_add(b_offset_in_a_element))
                    .map_or(false, |b_in_a_max_size| b_in_a_max_size <= a_stride.get())
                {
                    // FIXME(eddyb) this in-place merging dance only needed due to `Rc`.
                    ({
                        let a_element_mut = Rc::make_mut(&mut a_element);
                        let a_element = mem::replace(a_element_mut, QPtrMemUsage::UNUSED);
                        // FIXME(eddyb) remove this silliness by making `merge_mem_at` do symmetrical sorting.
                        if b_offset_in_a_element == 0 {
                            self.merge_mem(a_element, b)
                        } else {
                            self.merge_mem_at(a_element, b_offset_in_a_element, b)
                        }
                        .map(|merged| *a_element_mut = merged)
                    })
                    .map(|()| QPtrMemUsageKind::DynOffsetBase {
                        element: a_element,
                        stride: a_stride,
                    })
                } else {
                    match b.kind {
                        QPtrMemUsageKind::DynOffsetBase {
                            element: b_element,
                            stride: b_stride,
                        } if b_offset_in_a_element == 0 && a_stride == b_stride => {
                            // FIXME(eddyb) this in-place merging dance only needed due to `Rc`.
                            ({
                                let a_element_mut = Rc::make_mut(&mut a_element);
                                let a_element = mem::replace(a_element_mut, QPtrMemUsage::UNUSED);
                                let b_element =
                                    Rc::try_unwrap(b_element).unwrap_or_else(|e| (*e).clone());
                                self.merge_mem(a_element, b_element)
                                    .map(|merged| *a_element_mut = merged)
                            })
                            .map(|()| {
                                QPtrMemUsageKind::DynOffsetBase {
                                    element: a_element,
                                    stride: a_stride,
                                }
                            })
                        }
                        _ => {
                            // FIXME(eddyb) implement somehow (by adjusting stride?).
                            // NOTE(eddyb) with `b` as an `DynOffsetBase`/`OffsetBase`, it could
                            // also be possible to superimpose its offset patterns onto `a`,
                            // though that's easier for `OffsetBase` than `DynOffsetBase`.
                            // HACK(eddyb) needed due to `a` being moved out of.
                            let a = QPtrMemUsage {
                                max_size: a.max_size,
                                kind: QPtrMemUsageKind::DynOffsetBase {
                                    element: a_element,
                                    stride: a_stride,
                                },
                            };
                            MergeResult {
                                merged: a.kind.clone(),
                                error: Some(AnalysisError(Diag::bug([
                                    format!("merge_mem: unimplemented non-intra-element merging into stride={a_stride} (")
                                        .into(),
                                    QPtrUsage::Memory(a).into(),
                                    " vs ".into(),
                                    QPtrUsage::Memory(b).into(),
                                    ")".into(),
                                ]))),
                            }
                        }
                    }
                }
            }

            QPtrMemUsageKind::OffsetBase(mut a_entries) => {
                let overlapping_entries = a_entries
                    .range((
                        Bound::Unbounded,
                        b.max_size.map_or(Bound::Unbounded, |b_max_size| {
                            Bound::Excluded(b_offset_in_a.checked_add(b_max_size).unwrap())
                        }),
                    ))
                    .rev()
                    .take_while(|(a_sub_offset, a_sub_usage)| {
                        a_sub_usage.max_size.map_or(true, |a_sub_max_size| {
                            a_sub_offset.checked_add(a_sub_max_size).unwrap() > b_offset_in_a
                        })
                    });

                // FIXME(eddyb) this is a bit inefficient but we don't have
                // cursors, so we have to buffer the `BTreeMap` keys here.
                let overlapping_offsets: SmallVec<[u32; 16]> = overlapping_entries
                    .map(|(&a_sub_offset, _)| a_sub_offset)
                    .collect();
                let a_entries_mut = Rc::make_mut(&mut a_entries);
                let mut all_errors = None;
                let (mut b_offset_in_a, mut b) = (b_offset_in_a, b);
                for a_sub_offset in overlapping_offsets {
                    let a_sub_usage = a_entries_mut.remove(&a_sub_offset).unwrap();

                    // HACK(eddyb) this replicates the condition in which
                    // `merge_mem_at` would fail its similar assert, some of
                    // the cases denied here might be legal, but they're rare
                    // enough that we can do this for now.
                    let is_illegal = a_sub_offset != b_offset_in_a && {
                        let (a_sub_total_max_size, b_total_max_size) = (
                            a_sub_usage
                                .max_size
                                .map(|a| a.checked_add(a_sub_offset).unwrap()),
                            b.max_size.map(|b| b.checked_add(b_offset_in_a).unwrap()),
                        );
                        let total_max_size_merged = match (a_sub_total_max_size, b_total_max_size) {
                            (Some(a), Some(b)) => Some(a.max(b)),
                            (None, _) | (_, None) => None,
                        };
                        total_max_size_merged
                            != if a_sub_offset < b_offset_in_a {
                                a_sub_total_max_size
                            } else {
                                b_total_max_size
                            }
                    };
                    if is_illegal {
                        // HACK(eddyb) needed due to `a` being moved out of.
                        let a = QPtrMemUsage {
                            max_size: a.max_size,
                            kind: QPtrMemUsageKind::OffsetBase(a_entries.clone()),
                        };
                        return MergeResult {
                            merged: QPtrMemUsage {
                                max_size,
                                kind: QPtrMemUsageKind::OffsetBase(a_entries),
                            },
                            error: Some(AnalysisError(Diag::bug([
                                format!(
                                    "merge_mem: unsupported straddling overlap \
                                     at offsets {a_sub_offset} vs {b_offset_in_a} ("
                                )
                                .into(),
                                QPtrUsage::Memory(a).into(),
                                " vs ".into(),
                                QPtrUsage::Memory(b).into(),
                                ")".into(),
                            ]))),
                        };
                    }

                    let new_error;
                    (
                        b_offset_in_a,
                        MergeResult {
                            merged: b,
                            error: new_error,
                        },
                    ) = if a_sub_offset < b_offset_in_a {
                        (
                            a_sub_offset,
                            self.merge_mem_at(a_sub_usage, b_offset_in_a - a_sub_offset, b),
                        )
                    } else {
                        // FIXME(eddyb) remove this silliness by making `merge_mem_at` do symmetrical sorting.
                        if a_sub_offset - b_offset_in_a == 0 {
                            (b_offset_in_a, self.merge_mem(b, a_sub_usage))
                        } else {
                            (
                                b_offset_in_a,
                                self.merge_mem_at(b, a_sub_offset - b_offset_in_a, a_sub_usage),
                            )
                        }
                    };

                    // FIXME(eddyb) move some of this into `MergeResult`!
                    if let Some(AnalysisError(e)) = new_error {
                        let all_errors = &mut all_errors
                            .get_or_insert(AnalysisError(Diag::bug([])))
                            .0
                            .message;
                        // FIXME(eddyb) should this mean `MergeResult` should
                        // use `errors: Vec<AnalysisError>` instead of `Option`?
                        if !all_errors.is_empty() {
                            all_errors.push("\n".into());
                        }
                        // FIXME(eddyb) this is scuffed because the error might
                        // (or really *should*) already refer to the right offset!
                        all_errors.push(format!("+{a_sub_offset} => ").into());
                        all_errors.extend(e.message);
                    }
                }
                a_entries_mut.insert(b_offset_in_a, b);
                MergeResult {
                    merged: QPtrMemUsageKind::OffsetBase(a_entries),
                    // FIXME(eddyb) should this mean `MergeResult` should
                    // use `errors: Vec<AnalysisError>` instead of `Option`?
                    error: all_errors.map(|AnalysisError(mut e)| {
                        e.message.insert(0, "merge_mem: conflicts:\n".into());
                        AnalysisError(e)
                    }),
                }
            }
        };
        kind.map(|kind| QPtrMemUsage { max_size, kind })
    }

    /// Attempt to compute a `TypeLayout` for a given (SPIR-V) `Type`.
    fn layout_of(&self, ty: Type) -> Result<TypeLayout, AnalysisError> {
        self.layout_cache
            .layout_of(ty)
            .map_err(|LayoutError(err)| AnalysisError(err))
    }
}

impl MemTypeLayout {
    /// Determine if this layout is compatible with `usage` at `usage_offset`.
    ///
    /// That is, all typed leaves of `usage` must be found inside `self`, at
    /// their respective offsets, and all [`QPtrMemUsageKind::DynOffsetBase`]s
    /// must find a same-stride array inside `self` (to allow dynamic indexing).
    //
    // FIXME(eddyb) consider using `Result` to make it unambiguous.
    fn supports_usage_at_offset(&self, usage_offset: u32, usage: &QPtrMemUsage) -> bool {
        if let QPtrMemUsageKind::Unused = usage.kind {
            return true;
        }

        // "Fast accept" based on type alone (expected as recursion base case).
        if let QPtrMemUsageKind::StrictlyTyped(usage_type)
        | QPtrMemUsageKind::DirectAccess(usage_type) = usage.kind
        {
            if usage_offset == 0 && self.original_type == usage_type {
                return true;
            }
        }

        {
            // FIXME(eddyb) should `QPtrMemUsage` track a `min_size` as well?
            // FIXME(eddyb) duplicated below.
            let min_usage_offset_range =
                usage_offset..usage_offset.saturating_add(usage.max_size.unwrap_or(0));

            // "Fast reject" based on size alone (expected w/ multiple attempts).
            if self.mem_layout.dyn_unit_stride.is_none()
                && (self.mem_layout.fixed_base.size < min_usage_offset_range.end
                    || usage.max_size.is_none())
            {
                return false;
            }
        }

        let any_component_supports = |usage_offset: u32, usage: &QPtrMemUsage| {
            // FIXME(eddyb) should `QPtrMemUsage` track a `min_size` as well?
            // FIXME(eddyb) duplicated above.
            let min_usage_offset_range =
                usage_offset..usage_offset.saturating_add(usage.max_size.unwrap_or(0));

            // FIXME(eddyb) `find_components_containing` is linear today but
            // could be made logarithmic (via binary search).
            self.components
                .find_components_containing(min_usage_offset_range)
                .any(|idx| match &self.components {
                    Components::Scalar => unreachable!(),
                    Components::Elements { stride, elem, .. } => {
                        elem.supports_usage_at_offset(usage_offset % stride.get(), usage)
                    }
                    Components::Fields {
                        offsets, layouts, ..
                    } => layouts[idx].supports_usage_at_offset(usage_offset - offsets[idx], usage),
                })
        };
        match &usage.kind {
            _ if any_component_supports(usage_offset, usage) => true,

            QPtrMemUsageKind::Unused => unreachable!(),

            QPtrMemUsageKind::StrictlyTyped(_) | QPtrMemUsageKind::DirectAccess(_) => false,

            QPtrMemUsageKind::OffsetBase(entries) => {
                entries.iter().all(|(&sub_offset, sub_usage)| {
                    // FIXME(eddyb) maybe this overflow should be propagated up,
                    // as a sign that `usage` is malformed?
                    usage_offset
                        .checked_add(sub_offset)
                        .map_or(false, |combined_offset| {
                            // NOTE(eddyb) the reason this is only applicable to
                            // offset `0` is that *in all other cases*, every
                            // individual `OffsetBase` requires its own type, to
                            // allow performing offsets *in steps* (even if the
                            // offsets could easily be constant-folded, they'd
                            // *have to* be constant-folded *before* analysis,
                            // to ensure there is no need for the intermediaries).
                            if combined_offset == 0 {
                                self.supports_usage_at_offset(0, sub_usage)
                            } else {
                                any_component_supports(combined_offset, sub_usage)
                            }
                        })
                })
            }

            // Finding an array entirely nested in a component was handled above,
            // so here `layout` can only be a matching array (same stride and length).
            QPtrMemUsageKind::DynOffsetBase {
                element: usage_elem,
                stride: usage_stride,
            } => {
                let usage_fixed_len = usage
                    .max_size
                    .map(|size| {
                        if size % usage_stride.get() != 0 {
                            // FIXME(eddyb) maybe this should be propagated up,
                            // as a sign that `usage` is malformed?
                            return Err(());
                        }
                        NonZeroU32::new(size / usage_stride.get()).ok_or(())
                    })
                    .transpose();

                match &self.components {
                    // Dynamic offsetting into non-arrays is not supported, and it'd
                    // only make sense for legalization (or small-length arrays where
                    // selecting elements based on the index may be a practical choice).
                    Components::Scalar | Components::Fields { .. } => false,

                    Components::Elements {
                        stride: layout_stride,
                        elem: layout_elem,
                        fixed_len: layout_fixed_len,
                    } => {
                        // HACK(eddyb) extend the max length implied by `usage`,
                        // such that the array can start at offset `0`.
                        let ext_usage_offset = usage_offset % usage_stride.get();
                        let ext_usage_fixed_len = usage_fixed_len.and_then(|usage_fixed_len| {
                            usage_fixed_len
                                .map(|usage_fixed_len| {
                                    NonZeroU32::new(
                                        // FIXME(eddyb) maybe this overflow should be propagated up,
                                        // as a sign that `usage` is malformed?
                                        (usage_offset / usage_stride.get())
                                            .checked_add(usage_fixed_len.get())
                                            .ok_or(())?,
                                    )
                                    .ok_or(())
                                })
                                .transpose()
                        });

                        // FIXME(eddyb) this could maybe be allowed if there is still
                        // some kind of divisibility relation between the strides.
                        if ext_usage_offset != 0 {
                            return false;
                        }

                        layout_stride == usage_stride
                            && Ok(*layout_fixed_len) == ext_usage_fixed_len
                            && layout_elem.supports_usage_at_offset(0, usage_elem)
                    }
                }
            }
        }
    }
}

struct FuncInferUsageResults {
    param_usages: SmallVec<[Option<Result<QPtrUsage, AnalysisError>>; 2]>,
    usage_or_err_attrs_to_attach: Vec<(Value, Result<QPtrUsage, AnalysisError>)>,
}

#[derive(Clone)]
enum FuncInferUsageState {
    InProgress,
    Complete(Rc<FuncInferUsageResults>),
}

pub struct InferUsage<'a> {
    cx: Rc<Context>,
    layout_cache: LayoutCache<'a>,

    global_var_usages: FxIndexMap<GlobalVar, Option<Result<QPtrUsage, AnalysisError>>>,
    func_states: FxIndexMap<Func, FuncInferUsageState>,
}

impl<'a> InferUsage<'a> {
    pub fn new(cx: Rc<Context>, layout_config: &'a LayoutConfig) -> Self {
        Self {
            cx: cx.clone(),
            layout_cache: LayoutCache::new(cx, layout_config),

            global_var_usages: Default::default(),
            func_states: Default::default(),
        }
    }

    pub fn infer_usage_in_module(mut self, module: &mut Module) {
        for (export_key, &exportee) in &module.exports {
            if let Exportee::Func(func) = exportee {
                self.infer_usage_in_func(module, func);
            }

            // Ensure even unused interface variables get their `qptr.usage`.
            match export_key {
                ExportKey::LinkName(_) => {}
                ExportKey::SpvEntryPoint {
                    imms: _,
                    interface_global_vars,
                } => {
                    for &gv in interface_global_vars {
                        self.global_var_usages.entry(gv).or_insert_with(|| {
                            Some(Ok(match module.global_vars[gv].shape {
                                Some(shapes::GlobalVarShape::Handles { handle, .. }) => {
                                    QPtrUsage::Handles(match handle {
                                        shapes::Handle::Opaque(ty) => shapes::Handle::Opaque(ty),
                                        shapes::Handle::Buffer(..) => shapes::Handle::Buffer(
                                            AddrSpace::Handles,
                                            QPtrMemUsage::UNUSED,
                                        ),
                                    })
                                }
                                _ => QPtrUsage::Memory(QPtrMemUsage::UNUSED),
                            }))
                        });
                    }
                }
            }
        }

        // Analysis over, write all attributes back to the module.
        for (gv, usage) in self.global_var_usages {
            if let Some(usage) = usage {
                let global_var_def = &mut module.global_vars[gv];
                match usage {
                    Ok(usage) => {
                        // FIXME(eddyb) deduplicate attribute manipulation.
                        global_var_def.attrs = self.cx.intern(AttrSetDef {
                            attrs: self.cx[global_var_def.attrs]
                                .attrs
                                .iter()
                                .cloned()
                                .chain([Attr::QPtr(QPtrAttr::Usage(OrdAssertEq(usage)))])
                                .collect(),
                        });
                    }
                    Err(AnalysisError(e)) => {
                        global_var_def.attrs.push_diag(&self.cx, e);
                    }
                }
            }
        }
        for (func, state) in self.func_states {
            match state {
                FuncInferUsageState::InProgress => unreachable!(),
                FuncInferUsageState::Complete(func_results) => {
                    let FuncInferUsageResults {
                        param_usages,
                        usage_or_err_attrs_to_attach,
                    } = Rc::try_unwrap(func_results).ok().unwrap();

                    let func_decl = &mut module.funcs[func];
                    for (param_decl, usage) in func_decl.params.iter_mut().zip(param_usages) {
                        if let Some(usage) = usage {
                            match usage {
                                Ok(usage) => {
                                    // FIXME(eddyb) deduplicate attribute manipulation.
                                    param_decl.attrs = self.cx.intern(AttrSetDef {
                                        attrs: self.cx[param_decl.attrs]
                                            .attrs
                                            .iter()
                                            .cloned()
                                            .chain([Attr::QPtr(QPtrAttr::Usage(OrdAssertEq(
                                                usage,
                                            )))])
                                            .collect(),
                                    });
                                }
                                Err(AnalysisError(e)) => {
                                    param_decl.attrs.push_diag(&self.cx, e);
                                }
                            }
                        }
                    }

                    let func_def_body = match &mut module.funcs[func].def {
                        DeclDef::Present(func_def_body) => func_def_body,
                        DeclDef::Imported(_) => continue,
                    };

                    for (v, usage) in usage_or_err_attrs_to_attach {
                        let attrs = match v {
                            Value::Const(_) => unreachable!(),
                            Value::ControlRegionInput { region, input_idx } => {
                                &mut func_def_body.at_mut(region).def().inputs[input_idx as usize]
                                    .attrs
                            }
                            Value::ControlNodeOutput {
                                control_node,
                                output_idx,
                            } => {
                                &mut func_def_body.at_mut(control_node).def().outputs
                                    [output_idx as usize]
                                    .attrs
                            }
                            Value::DataInstOutput(data_inst) => {
                                &mut func_def_body.at_mut(data_inst).def().attrs
                            }
                        };
                        match usage {
                            Ok(usage) => {
                                // FIXME(eddyb) deduplicate attribute manipulation.
                                *attrs = self.cx.intern(AttrSetDef {
                                    attrs: self.cx[*attrs]
                                        .attrs
                                        .iter()
                                        .cloned()
                                        .chain([Attr::QPtr(QPtrAttr::Usage(OrdAssertEq(usage)))])
                                        .collect(),
                                });
                            }
                            Err(AnalysisError(e)) => {
                                attrs.push_diag(&self.cx, e);
                            }
                        }
                    }
                }
            }
        }
    }

    // HACK(eddyb) `FuncInferUsageState` also serves to indicate recursion errors.
    fn infer_usage_in_func(&mut self, module: &Module, func: Func) -> FuncInferUsageState {
        if let Some(cached) = self.func_states.get(&func).cloned() {
            return cached;
        }

        self.func_states
            .insert(func, FuncInferUsageState::InProgress);

        let completed_state =
            FuncInferUsageState::Complete(Rc::new(self.infer_usage_in_func_uncached(module, func)));

        self.func_states.insert(func, completed_state.clone());
        completed_state
    }
    fn infer_usage_in_func_uncached(
        &mut self,
        module: &Module,
        func: Func,
    ) -> FuncInferUsageResults {
        let cx = self.cx.clone();
        let is_qptr = |ty: Type| matches!(cx[ty].ctor, TypeCtor::QPtr);

        let func_decl = &module.funcs[func];
        let mut param_usages: SmallVec<[_; 2]> =
            (0..func_decl.params.len()).map(|_| None).collect();
        let mut usage_or_err_attrs_to_attach = vec![];

        let func_def_body = match &module.funcs[func].def {
            DeclDef::Present(func_def_body) => func_def_body,
            DeclDef::Imported(_) => {
                for (param, param_usage) in func_decl.params.iter().zip(&mut param_usages) {
                    if is_qptr(param.ty) {
                        *param_usage = Some(Err(AnalysisError(Diag::bug([
                            "pointer param of imported func".into(),
                        ]))));
                    }
                }
                return FuncInferUsageResults {
                    param_usages,
                    usage_or_err_attrs_to_attach,
                };
            }
        };

        let mut all_data_insts = CollectAllDataInsts::default();
        func_def_body.inner_visit_with(&mut all_data_insts);

        let mut data_inst_output_usages = FxHashMap::default();
        for insts in all_data_insts.0.into_iter().rev() {
            for func_at_inst in func_def_body.at(insts).into_iter().rev() {
                let data_inst = func_at_inst.position;
                let data_inst_def = func_at_inst.def();
                let data_inst_form_def = &cx[data_inst_def.form];
                let output_usage = data_inst_output_usages.remove(&data_inst).flatten();

                let mut generate_usage = |this: &mut Self, ptr: Value, new_usage| {
                    let slot = match ptr {
                        Value::Const(ct) => match cx[ct].ctor {
                            ConstCtor::PtrToGlobalVar(gv) => {
                                this.global_var_usages.entry(gv).or_default()
                            }
                            // FIXME(eddyb) may be relevant?
                            _ => unreachable!(),
                        },
                        Value::ControlRegionInput { region, input_idx }
                            if region == func_def_body.body =>
                        {
                            &mut param_usages[input_idx as usize]
                        }
                        // FIXME(eddyb) implement
                        Value::ControlRegionInput { .. } | Value::ControlNodeOutput { .. } => {
                            usage_or_err_attrs_to_attach.push((
                                ptr,
                                Err(AnalysisError(Diag::bug(["unsupported φ".into()]))),
                            ));
                            return;
                        }
                        Value::DataInstOutput(ptr_inst) => {
                            data_inst_output_usages.entry(ptr_inst).or_default()
                        }
                    };
                    *slot = Some(match slot.take() {
                        Some(old) => old.and_then(|old| {
                            UsageMerger {
                                layout_cache: &this.layout_cache,
                            }
                            .merge(old, new_usage?)
                            .into_result()
                        }),
                        None => new_usage,
                    });
                };
                match &data_inst_form_def.kind {
                    &DataInstKind::FuncCall(callee) => {
                        match self.infer_usage_in_func(module, callee) {
                            FuncInferUsageState::Complete(callee_results) => {
                                for (&arg, param_usage) in data_inst_def
                                    .inputs
                                    .iter()
                                    .zip(&callee_results.param_usages)
                                {
                                    if let Some(param_usage) = param_usage {
                                        generate_usage(self, arg, param_usage.clone());
                                    }
                                }
                            }
                            FuncInferUsageState::InProgress => {
                                usage_or_err_attrs_to_attach.push((
                                    Value::DataInstOutput(data_inst),
                                    Err(AnalysisError(Diag::bug([
                                        "unsupported recursive call".into()
                                    ]))),
                                ));
                            }
                        };
                        if data_inst_form_def.output_type.map_or(false, is_qptr) {
                            if let Some(usage) = output_usage {
                                usage_or_err_attrs_to_attach
                                    .push((Value::DataInstOutput(data_inst), usage));
                            }
                        }
                    }

                    DataInstKind::QPtr(QPtrOp::FuncLocalVar(_)) => {
                        if let Some(usage) = output_usage {
                            usage_or_err_attrs_to_attach
                                .push((Value::DataInstOutput(data_inst), usage));
                        }
                    }
                    DataInstKind::QPtr(QPtrOp::HandleArrayIndex) => {
                        generate_usage(
                            self,
                            data_inst_def.inputs[0],
                            output_usage
                                .unwrap_or_else(|| {
                                    Err(AnalysisError(Diag::bug([
                                        "HandleArrayIndex: unknown element".into(),
                                    ])))
                                })
                                .and_then(|usage| match usage {
                                    QPtrUsage::Handles(handle) => Ok(QPtrUsage::Handles(handle)),
                                    QPtrUsage::Memory(_) => Err(AnalysisError(Diag::bug([
                                        "HandleArrayIndex: cannot be used as Memory".into(),
                                    ]))),
                                }),
                        );
                    }
                    DataInstKind::QPtr(QPtrOp::BufferData) => {
                        generate_usage(
                            self,
                            data_inst_def.inputs[0],
                            output_usage
                                .unwrap_or(Ok(QPtrUsage::Memory(QPtrMemUsage::UNUSED)))
                                .and_then(|usage| {
                                    let usage = match usage {
                                        QPtrUsage::Handles(_) => {
                                            return Err(AnalysisError(Diag::bug([
                                                "BufferData: cannot be used as Handles".into(),
                                            ])));
                                        }
                                        QPtrUsage::Memory(usage) => usage,
                                    };
                                    Ok(QPtrUsage::Handles(shapes::Handle::Buffer(
                                        AddrSpace::Handles,
                                        usage,
                                    )))
                                }),
                        );
                    }
                    &DataInstKind::QPtr(QPtrOp::BufferDynLen {
                        fixed_base_size,
                        dyn_unit_stride,
                    }) => {
                        let array_usage = QPtrMemUsage {
                            max_size: None,
                            kind: QPtrMemUsageKind::DynOffsetBase {
                                element: Rc::new(QPtrMemUsage::UNUSED),
                                stride: dyn_unit_stride,
                            },
                        };
                        let buf_data_usage = if fixed_base_size == 0 {
                            array_usage
                        } else {
                            QPtrMemUsage {
                                max_size: None,
                                kind: QPtrMemUsageKind::OffsetBase(Rc::new(
                                    [(fixed_base_size, array_usage)].into(),
                                )),
                            }
                        };
                        generate_usage(
                            self,
                            data_inst_def.inputs[0],
                            Ok(QPtrUsage::Handles(shapes::Handle::Buffer(
                                AddrSpace::Handles,
                                buf_data_usage,
                            ))),
                        );
                    }
                    &DataInstKind::QPtr(QPtrOp::Offset(offset)) => {
                        generate_usage(
                            self,
                            data_inst_def.inputs[0],
                            output_usage
                                .unwrap_or(Ok(QPtrUsage::Memory(QPtrMemUsage::UNUSED)))
                                .and_then(|usage| {
                                    let usage = match usage {
                                        QPtrUsage::Handles(_) => {
                                            return Err(AnalysisError(Diag::bug([format!(
                                                "Offset({offset}): cannot offset Handles"
                                            ).into()])));
                                        }
                                        QPtrUsage::Memory(usage) => usage,
                                    };
                                    let offset = u32::try_from(offset).ok().ok_or_else(|| {
                                        AnalysisError(Diag::bug([format!("Offset({offset}): negative offset").into()]))
                                    })?;

                                    // FIXME(eddyb) these should be normalized
                                    // (e.g. constant-folded) out of existence,
                                    // but while they exist, they should be noops.
                                    if offset == 0 {
                                        return Ok(QPtrUsage::Memory(usage));
                                    }

                                    Ok(QPtrUsage::Memory(QPtrMemUsage {
                                        max_size: usage
                                            .max_size
                                            .map(|max_size| offset.checked_add(max_size).ok_or_else(|| {
                                                AnalysisError(Diag::bug([format!("Offset({offset}): size overflow ({offset}+{max_size})").into()]))
                                            })).transpose()?,
                                        // FIXME(eddyb) allocating `Rc<BTreeMap<_, _>>`
                                        // to represent the one-element case, seems
                                        // quite wasteful when it's likely consumed.
                                        kind: QPtrMemUsageKind::OffsetBase(Rc::new(
                                            [(offset, usage)].into(),
                                        )),
                                    }))
                                }),
                        );
                    }
                    DataInstKind::QPtr(QPtrOp::DynOffset {
                        stride,
                        index_bounds,
                    }) => {
                        generate_usage(
                            self,
                            data_inst_def.inputs[0],
                            output_usage
                                .unwrap_or(Ok(QPtrUsage::Memory(QPtrMemUsage::UNUSED)))
                                .and_then(|usage| {
                                    let usage = match usage {
                                        QPtrUsage::Handles(_) => {
                                            return Err(AnalysisError(Diag::bug(["DynOffset: cannot offset Handles".into()])));
                                        }
                                        QPtrUsage::Memory(usage) => usage,
                                    };
                                    match usage.max_size {
                                        None => {
                                            return Err(AnalysisError(Diag::bug(["DynOffset: unsized element".into()])));
                                        }
                                        // FIXME(eddyb) support this by "folding"
                                        // the usage onto itself (i.e. applying
                                        // `%= stride` on all offsets inside).
                                        Some(max_size) if max_size > stride.get() => {
                                            return Err(AnalysisError(Diag::bug(["DynOffset: element max_size exceeds stride".into()])));
                                        }
                                        Some(_) => {}
                                    }
                                    Ok(QPtrUsage::Memory(QPtrMemUsage {
                                        // FIXME(eddyb) does the `None` case allow
                                        // for negative offsets?
                                        max_size: index_bounds
                                            .as_ref()
                                            .map(|index_bounds| {
                                                if index_bounds.start < 0 || index_bounds.end < 0 {
                                                    return Err(AnalysisError(
                                                        Diag::bug([
                                                            "DynOffset: potentially negative offset"
                                                                .into(),
                                                        ])
                                                    ));
                                                }
                                                let index_bounds_end = u32::try_from(index_bounds.end).unwrap();
                                                index_bounds_end.checked_mul(stride.get()).ok_or_else(|| {
                                                     AnalysisError(Diag::bug([
                                                        format!("DynOffset: size overflow ({index_bounds_end}*{stride})").into(),
                                                    ]))
                                                })
                                            })
                                            .transpose()?,
                                        kind: QPtrMemUsageKind::DynOffsetBase {
                                            element: Rc::new(usage),
                                            stride: *stride,
                                        },
                                    }))
                                }),
                        );
                    }
                    DataInstKind::QPtr(op @ (QPtrOp::Load | QPtrOp::Store)) => {
                        let (op_name, access_type) = match op {
                            QPtrOp::Load => ("Load", data_inst_form_def.output_type.unwrap()),
                            QPtrOp::Store => (
                                "Store",
                                func_at_inst.at(data_inst_def.inputs[1]).type_of(&cx),
                            ),
                            _ => unreachable!(),
                        };
                        generate_usage(
                            self,
                            data_inst_def.inputs[0],
                            self.layout_cache
                                .layout_of(access_type)
                                .map_err(|LayoutError(e)| AnalysisError(e))
                                .and_then(|layout| match layout {
                                    TypeLayout::Handle(shapes::Handle::Opaque(ty)) => {
                                        Ok(QPtrUsage::Handles(shapes::Handle::Opaque(ty)))
                                    }
                                    TypeLayout::Handle(shapes::Handle::Buffer(..)) => {
                                        Err(AnalysisError(Diag::bug([format!(
                                            "{op_name}: cannot access whole Buffer"
                                        )
                                        .into()])))
                                    }
                                    TypeLayout::HandleArray(..) => {
                                        Err(AnalysisError(Diag::bug([format!(
                                            "{op_name}: cannot access whole HandleArray"
                                        )
                                        .into()])))
                                    }
                                    TypeLayout::Concrete(concrete)
                                        if concrete.mem_layout.dyn_unit_stride.is_some() =>
                                    {
                                        Err(AnalysisError(Diag::bug([format!(
                                            "{op_name}: cannot access unsized type"
                                        )
                                        .into()])))
                                    }
                                    TypeLayout::Concrete(concrete) => {
                                        Ok(QPtrUsage::Memory(QPtrMemUsage {
                                            max_size: Some(concrete.mem_layout.fixed_base.size),
                                            kind: QPtrMemUsageKind::DirectAccess(access_type),
                                        }))
                                    }
                                }),
                        );
                    }

                    DataInstKind::SpvInst(_) | DataInstKind::SpvExtInst { .. } => {
                        let mut has_from_spv_ptr_output_attr = false;
                        for attr in &cx[data_inst_def.attrs].attrs {
                            match *attr {
                                Attr::QPtr(QPtrAttr::ToSpvPtrInput { input_idx, pointee }) => {
                                    let ty = pointee.0;
                                    generate_usage(
                                        self,
                                        data_inst_def.inputs[input_idx as usize],
                                        self.layout_cache
                                            .layout_of(ty)
                                            .map_err(|LayoutError(e)| AnalysisError(e))
                                            .and_then(|layout| match layout {
                                                TypeLayout::Handle(handle) => {
                                                    let handle = match handle {
                                                        shapes::Handle::Opaque(ty) => {
                                                            shapes::Handle::Opaque(ty)
                                                        }
                                                        // NOTE(eddyb) this error is important,
                                                        // as the `Block` annotation on the
                                                        // buffer type means the type is *not*
                                                        // usable anywhere inside buffer data,
                                                        // since it would conflict with our
                                                        // own `Block`-annotated wrapper.
                                                        shapes::Handle::Buffer(..) => {
                                                            return Err(AnalysisError(Diag::bug(["ToSpvPtrInput: whole Buffer ambiguous (handle vs buffer data)".into()])
                                                            ));
                                                        }
                                                    };
                                                    Ok(QPtrUsage::Handles(handle))
                                                }
                                                // NOTE(eddyb) because we can't represent
                                                // the original type, in the same way we
                                                // use `QPtrMemUsageKind::StrictlyTyped`
                                                // for non-handles, we can't guarantee
                                                // a generated type that matches the
                                                // desired `pointee` type.
                                                TypeLayout::HandleArray(..) => {
                                                    Err(AnalysisError(Diag::bug(["ToSpvPtrInput: whole handle array unrepresentable".into()])
                                                    ))
                                                }
                                                TypeLayout::Concrete(concrete) => {
                                                    Ok(QPtrUsage::Memory(QPtrMemUsage {
                                                        max_size: if concrete
                                                            .mem_layout
                                                            .dyn_unit_stride
                                                            .is_some()
                                                        {
                                                            None
                                                        } else {
                                                            Some(
                                                                concrete.mem_layout.fixed_base.size,
                                                            )
                                                        },
                                                        kind: QPtrMemUsageKind::StrictlyTyped(ty),
                                                    }))
                                                }
                                            }),
                                    );
                                }
                                Attr::QPtr(QPtrAttr::FromSpvPtrOutput {
                                    addr_space: _,
                                    pointee: _,
                                }) => {
                                    has_from_spv_ptr_output_attr = true;
                                }
                                _ => {}
                            }
                        }

                        if has_from_spv_ptr_output_attr {
                            // FIXME(eddyb) merge with `FromSpvPtrOutput`'s `pointee`.
                            if let Some(usage) = output_usage {
                                usage_or_err_attrs_to_attach
                                    .push((Value::DataInstOutput(data_inst), usage));
                            }
                        }
                    }
                }
            }
        }

        FuncInferUsageResults {
            param_usages,
            usage_or_err_attrs_to_attach,
        }
    }
}

// HACK(eddyb) this is easier than implementing a proper reverse traversal.
#[derive(Default)]
struct CollectAllDataInsts(Vec<EntityList<DataInst>>);

impl Visitor<'_> for CollectAllDataInsts {
    // FIXME(eddyb) this is excessive, maybe different kinds of
    // visitors should exist for module-level and func-level?
    fn visit_attr_set_use(&mut self, _: AttrSet) {}
    fn visit_type_use(&mut self, _: Type) {}
    fn visit_const_use(&mut self, _: Const) {}
    fn visit_data_inst_form_use(&mut self, _: DataInstForm) {}
    fn visit_global_var_use(&mut self, _: GlobalVar) {}
    fn visit_func_use(&mut self, _: Func) {}

    fn visit_control_node_def(&mut self, func_at_control_node: FuncAt<'_, ControlNode>) {
        if let ControlNodeKind::Block { insts } = func_at_control_node.def().kind {
            self.0.push(insts);
        }
        func_at_control_node.inner_visit_with(self);
    }
}
