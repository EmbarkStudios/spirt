//! Constant data efficiently mixing concrete bytes with symbolic values.

use itertools::Itertools;
use smallvec::SmallVec;
use std::collections::BTreeMap;
use std::iter;
use std::num::NonZeroU32;
use std::ops::Range;

/// Constant data "blob" or "chunk", where each byte can be part of:
/// - uninitialized areas (e.g. SPIR-V `OpUndef`)
/// - concrete data (i.e. `u8` values)
/// - symbolic values of type `V` (spanning some number of bytes)
///
/// This is similar to (and inspired by), [`rustc`'s `mir::interpret::Allocation`](
/// https://rustc-dev-guide.rust-lang.org/const-eval/interpret.html#memory),
/// which only has abstract pointers as symbolic values, encoded as "relocations"
/// (i.e. concrete data contains the respective offset for each abstract pointer,
/// whereas here the symbolic values are completely disjoint with concrete data).
pub struct ConstData<V> {
    /// The bit `init[i / 64] & (1 << (i % 64))` is set iff byte offset `i` is
    /// initialized, either with concrete data, or as part of a symbolic value.
    init: Vec<u64>,

    /// Concrete data bytes, with each byte only used when `init` indicates
    /// it is initialized *and* no symbolic value overlaps it. Unused bytes can
    /// have any values in `bytes`, as they're guaranteed to be always ignored.
    data: Vec<u8>,

    /// Non-overlapping set of symbolic `V` values, forming an "overlay" on top
    /// of the concrete data bytes, with `syms[offset] = (size, value)`
    /// indicating bytes `offset..(offset + size)` are occupied by `value`.
    syms: BTreeMap<u32, (NonZeroU32, V)>,

    /// Largest symbolic value size, i.e. `syms.values().map(|(size, _)| size).max()`.
    //
    // FIXME(eddyb) this is only needed to help with scanning overlaps in `syms`,
    // and because there is no inherent limit on the size of symbolic values.
    max_sym_size: NonZeroU32,
}

/// One uniform "slice" of a `ConstData` (*not* mixing value categories).
#[derive(Clone)]
pub enum Part<'a, V> {
    Uninit {
        size: u32,
    },
    Data(&'a [u8]),
    Symbolic {
        size: NonZeroU32,
        /// This is only the full `value` if `slice == 0..size`.
        slice: Range<u32>,
        value: V,
    },
}

/// Error type for write operations, emitted when they would otherwise cause a
/// partial overwrite of a symbolic value, if allowed to take effect.
#[derive(Debug)]
pub struct PartialSymbolicOverlap {
    pub offsets: Range<u32>,
}

// FIXME(eddyb) come up with a nicer abstraction for bitvecs, or use a crate.
fn bitrange_word_chunks(range: Range<u32>) -> (Range<usize>, impl Iterator<Item = Range<u8>>) {
    let words = (range.start / 64)..(range.end.div_ceil(64));
    (
        (words.start as usize)..(words.end as usize),
        words.map(move |i| {
            (((i * 64).clamp(range.start, range.end) % 64) as u8)
                ..((((i + 1) * 64).clamp(range.start, range.end) % 64) as u8)
        }),
    )
}

impl<V: Copy> ConstData<V> {
    pub fn new(size: u32) -> Self {
        let size = size as usize;
        Self {
            init: vec![0; size.div_ceil(64)],
            data: vec![0; size],
            syms: BTreeMap::new(),
            max_sym_size: NonZeroU32::new(1).unwrap(),
        }
    }

    pub fn size(&self) -> u32 {
        self.data.len() as u32
    }

    pub fn read(&self, range: Range<u32>) -> impl Iterator<Item = Part<'_, V>> {
        // HACK(eddyb) trigger bounds-checking panics.
        let _ = &self.data[(range.start as usize)..(range.end as usize)];

        // HACK(eddyb) the range has to be extended backwards, because a partial
        // overlap could exit, i.e. `range.start` being in the middle of a value,
        // but then irrelevant values have to be ignored.
        let mut syms = self
            .syms
            .range((range.start - (self.max_sym_size.get() - 1))..range.end)
            .map(|(&offset, &(size, value))| (offset..(offset + size.get()), value))
            .peekable();
        while let Some((sym_range, _)) = syms.peek() {
            if sym_range.end > range.start {
                break;
            }
            syms.next().unwrap();
        }

        let mut part_start = range.start;
        iter::from_fn(move || {
            if part_start >= range.end {
                return None;
            }
            let next_sym_range = syms.peek().cloned().map_or(range.end..range.end, |(r, _)| r);

            let max_part_end = if next_sym_range.contains(&part_start) {
                next_sym_range.end
            } else {
                next_sym_range.start
            };
            // FIXME(eddyb) come up with a nicer abstraction for bitvecs, or use a crate.
            let (part_is_init, part_size) = {
                let (words, word_bitslices) = bitrange_word_chunks(part_start..max_part_end);
                self.init[words]
                    .iter()
                    .zip_eq(word_bitslices)
                    .flat_map(|(&word, word_bitslice)| {
                        let sliced_word =
                            (word >> word_bitslice.start) & (!0 >> (64 - word_bitslice.end));
                        let first = (sliced_word & 1) != 0;
                        let same_run = if first {
                            sliced_word.trailing_ones()
                        } else {
                            sliced_word.trailing_zeros()
                        };
                        [(first, same_run)]
                            .into_iter()
                            .chain((same_run < word_bitslice.len() as u32).then_some((!first, 0)))
                    })
                    .coalesce(|(a, a_run), (b, b_run)| {
                        if a == b { Ok((a, a_run + b_run)) } else { Err(((a, a_run), (b, b_run))) }
                    })
                    .next()
                    .unwrap()
            };

            let part_end = part_start + part_size;
            let part = if !part_is_init {
                Part::Uninit { size: part_size }
            } else if next_sym_range.contains(&part_start) {
                let (sym_range, value) = syms.next().unwrap();
                // HACK(eddyb) ensure slicing is caused by `range`, *not* `init`.
                assert_eq!(
                    part_start..part_end,
                    sym_range.start.clamp(range.start, range.end)
                        ..sym_range.end.clamp(range.start, range.end)
                );
                Part::Symbolic {
                    size: NonZeroU32::new(sym_range.len() as u32).unwrap(),
                    slice: (part_start - sym_range.start)..(part_end - sym_range.start),
                    value,
                }
            } else {
                Part::Data(&self.data[(part_start as usize)..(part_end as usize)])
            };
            part_start = part_end;
            Some(part)
        })
    }

    /// Helper for `write_bytes` and `write_symbolic`, which only modifies `self`
    /// (removing fully overwritten symbolic values, and setting `init` bits),
    /// when it can guarantee it will return `Ok(())` (i.e. after error checks).
    fn try_init(&mut self, range: Range<u32>) -> Result<(), PartialSymbolicOverlap> {
        // HACK(eddyb) trigger bounds-checking panics.
        let _ = &self.data[(range.start as usize)..(range.end as usize)];

        // HACK(eddyb) the range has to be extended backwards, because a partial
        // overlap could exit, i.e. `range.start` being in the middle of a value,
        // but then irrelevant values have to be ignored.
        let syms_ranges = self
            .syms
            .range((range.start - (self.max_sym_size.get() - 1))..range.end)
            .map(|(&offset, &(size, _))| offset..(offset + size.get()));

        // FIXME(eddyb) this is a bit inefficient but we don't have
        // cursors, so we have to buffer the `BTreeMap` keys here.
        let mut full_overwritten_sym_offsets = SmallVec::<[u32; 16]>::new();
        for sym_range in syms_ranges {
            let overlap = sym_range.start.clamp(range.start, range.end)
                ..sym_range.end.clamp(range.start, range.end);
            if overlap.is_empty() {
                continue;
            }
            if overlap == sym_range {
                full_overwritten_sym_offsets.push(sym_range.start);
            } else {
                return Err(PartialSymbolicOverlap { offsets: overlap });
            }
        }
        for offset in full_overwritten_sym_offsets {
            self.syms.remove(&offset);
        }

        // FIXME(eddyb) come up with a nicer abstraction for bitvecs, or use a crate.
        {
            let (words, word_bitslices) = bitrange_word_chunks(range);
            for (word, word_bitslice) in self.init[words].iter_mut().zip(word_bitslices) {
                *word |= (!0 << word_bitslice.start) & (!0 >> (64 - word_bitslice.end));
            }
        }

        Ok(())
    }

    pub fn write_bytes(&mut self, offset: u32, bytes: &[u8]) -> Result<(), PartialSymbolicOverlap> {
        let range = offset..(offset + bytes.len() as u32);
        self.try_init(range.clone())?;
        self.data[(range.start as usize)..(range.end as usize)].copy_from_slice(bytes);
        Ok(())
    }

    // FIXME(eddyb) should this take an offset range instead?
    pub fn write_symbolic(
        &mut self,
        offset: u32,
        size: NonZeroU32,
        value: V,
    ) -> Result<(), PartialSymbolicOverlap> {
        let range = offset..(offset + size.get());
        self.try_init(range.clone())?;
        self.syms.insert(offset, (size, value));
        Ok(())
    }
}
