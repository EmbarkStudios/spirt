//! Multi-version pretty-printing support (e.g. for comparing the IR between passes).

use crate::print::pretty::{self, TextOp};
use crate::FxIndexMap;
use internal_iterator::{
    FromInternalIterator, InternalIterator, IntoInternalIterator, IteratorExt,
};
use itertools::{Either, Itertools};
use smallvec::SmallVec;
use std::fmt::Write;
use std::{fmt, iter, mem};

#[allow(rustdoc::private_intra_doc_links)]
/// Wrapper for handling the difference between single-version and multi-version
/// output, which aren't expressible in [`pretty::Fragment`].
//
// FIXME(eddyb) introduce a `pretty::Node` variant capable of handling this,
// but that's complicated wrt non-HTML output, if they're to also be 2D tables.
pub enum Versions<PF> {
    Single(PF),
    Multiple {
        // FIXME(eddyb) avoid allocating this if possible.
        version_names: Vec<String>,

        /// Each row consists of *deduplicated* (or "run-length encoded")
        /// versions, with "repeat count"s larger than `1` indicating that
        /// multiple versions (columns) have the exact same content.
        ///
        /// For HTML output, "repeat count"s map to `colspan` attributes.
        //
        // FIXME(eddyb) remove the "repeat count" mechanism.
        per_row_versions_with_repeat_count: Vec<SmallVec<[(PF, usize); 1]>>,
    },
}

impl fmt::Display for Versions<pretty::FragmentPostLayout> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Single(fragment) => fragment.fmt(f),
            Self::Multiple {
                version_names,
                per_row_versions_with_repeat_count,
            } => {
                let mut first = true;

                // HACK(eddyb) this is not the nicest output, but multi-version
                // is intended for HTML input primarily anyway.
                for versions_with_repeat_count in per_row_versions_with_repeat_count {
                    if !first {
                        writeln!(f)?;
                    }
                    first = false;

                    let mut next_version_idx = 0;
                    let mut any_headings = false;
                    for (fragment, repeat_count) in versions_with_repeat_count {
                        // No headings for anything uniform across versions.
                        if (next_version_idx, *repeat_count) != (0, version_names.len()) {
                            any_headings = true;

                            if next_version_idx == 0 {
                                write!(f, "//#IF ")?;
                            } else {
                                write!(f, "//#ELSEIF ")?;
                            }
                            let mut first_name = true;
                            for name in &version_names[next_version_idx..][..*repeat_count] {
                                if !first_name {
                                    write!(f, " | ")?;
                                }
                                first_name = false;

                                write!(f, "`{name}`")?;
                            }
                            writeln!(f)?;
                        }

                        writeln!(f, "{fragment}")?;

                        next_version_idx += repeat_count;
                    }
                    if any_headings {
                        writeln!(f, "//#ENDIF")?;
                    }
                }

                Ok(())
            }
        }
    }
}

impl Versions<pretty::FragmentPostLayout> {
    // FIXME(eddyb) provide a non-allocating version.
    pub fn render_to_html(&self) -> pretty::HtmlSnippet {
        match self {
            Self::Single(fragment) => fragment.render_to_html(),
            Self::Multiple {
                version_names,
                per_row_versions_with_repeat_count,
            } => {
                // HACK(eddyb) using an UUID as a class name in lieu of "scoped <style>".
                const TABLE_CLASS_NAME: &str = "spirt-table-90c2056d-5b38-4644-824a-b4be1c82f14d";

                let mut html = pretty::HtmlSnippet::default();
                html.head_deduplicatable_elements.insert(
                    "
<style>
    SCOPE {
        border-collapse: collapse;
    }
    SCOPE>tbody>tr>*:not(:only-child) {
        border: solid 1px;
    }
    SCOPE>tbody>tr>th {
        /* HACK(eddyb) these are relative to `pretty`'s own HTML styles. */
        font-size: 17px;
        font-weight: 700;

        font-style: italic;
    }
    SCOPE>tbody>tr>td {
        vertical-align: top;
        max-width: MAX_LINE_WIDTHch;
    }
    SCOPE>tbody>tr>td>pre {
        overflow-x: auto;

        /* HACK(eddyb) this shouldn't be needed but `visible` will turn into
           `auto` because `overflow-x` is `auto` (for cursed browser reasons),
           and some table cells are always assumed to need vertical scroll,
           e.g. because they have `<sub>` elements on the last line (which don't
           contribute to the surrounding bounding box, due to `line-height: 0`)
         */
        overflow-y: hidden;
    }
</style>
        "
                    .replace("SCOPE", &format!("table.{TABLE_CLASS_NAME}"))
                    .replace("MAX_LINE_WIDTH", &super::MAX_LINE_WIDTH.to_string()),
                );

                let headings = {
                    let mut h = "<tr>".to_string();
                    for name in version_names {
                        write!(h, "<th><code>{name}</code></th>").unwrap();
                    }
                    h + "</tr>\n"
                };

                html.body = format!("<table class=\"{TABLE_CLASS_NAME}\">\n");
                let mut last_was_uniform = true;
                for versions_with_repeat_count in per_row_versions_with_repeat_count {
                    // FIXME(eddyb) remove the "repeat count" mechanism.
                    let is_uniform = match versions_with_repeat_count[..] {
                        [(_, repeat_count)] => repeat_count == version_names.len(),
                        _ => false,
                    };

                    if last_was_uniform && is_uniform {
                        // Headings unnecessary, they would be between uniform
                        // rows (or at the very start, before an uniform row).
                    } else {
                        // Repeat the headings often, where necessary.
                        html.body += &headings;
                    }
                    last_was_uniform = is_uniform;

                    // Attempt to align as many anchors as possible between the
                    // columns, to improve legibility (see also `AnchorAligner`).
                    let mut anchor_aligner = AnchorAligner::default();
                    for (fragment, _) in versions_with_repeat_count {
                        anchor_aligner
                            .add_column_and_align_anchors(fragment.render_to_text_ops().collect());
                    }

                    html.body += "<tr>\n";
                    if is_uniform {
                        // FIXME(eddyb) avoid duplication with the non-uniform case.
                        let pretty::HtmlSnippet {
                            head_deduplicatable_elements: fragment_head,
                            body: fragment_body,
                        } = anchor_aligner
                            .merged_columns()
                            .next()
                            .unwrap()
                            .lines()
                            .intersperse(&[TextOp::Text("\n")])
                            .flatten()
                            .copied()
                            .into_internal()
                            .collect();

                        html.head_deduplicatable_elements.extend(fragment_head);

                        writeln!(html.body, "<td colspan=\"{}\">", version_names.len()).unwrap();
                        html.body += &fragment_body;
                        html.body += "</td>\n";
                    } else {
                        let mut merged_columns = versions_with_repeat_count
                            .iter()
                            .zip(anchor_aligner.merged_columns())
                            .flat_map(|(&(_, repeat_count), column)| {
                                iter::repeat(column).take(repeat_count)
                            })
                            .peekable();

                        let mut prev_column = None;
                        while let Some(column) = merged_columns.next() {
                            let prev_column = prev_column.replace(column);
                            let next_column = merged_columns.peek().copied();

                            let unchanged_line_style = pretty::Styles {
                                desaturate_and_dim_for_unchanged_multiversion_line: true,
                                ..Default::default()
                            };

                            // NOTE(eddyb) infinite (but limited by `zip` below),
                            // and `Some([])`/`None` distinguishes empty/missing.
                            let prev_lines = prev_column
                                .iter()
                                .flat_map(|prev| prev.lines().map(Some))
                                .chain(iter::repeat(prev_column.map(|_| &[][..])));
                            let next_lines = next_column
                                .iter()
                                .flat_map(|next| next.lines().map(Some))
                                .chain(iter::repeat(next_column.map(|_| &[][..])));

                            let lines = column.lines().zip(prev_lines).zip(next_lines).map(
                                |((line, prev_line), next_line)| {
                                    // FIXME(eddyb) apply a `class` instead of an inline `style`,
                                    // and allow `:hover` to disable the desaturation/dimming.
                                    // FIXME(eddyb) maybe indicate when lines
                                    // were removed (red "hashed" background?).
                                    let diff = |other: Option<_>| {
                                        // Ignore indendation-only changes.
                                        fn strip_indents<'a, 'b>(
                                            mut line: &'b [TextOp<'a>],
                                        ) -> &'b [TextOp<'a>]
                                        {
                                            // HACK(eddyb) also ignore helper anchors,
                                            // which can go before indents.
                                            while let [TextOp::Text(pretty::INDENT), rest @ ..]
                                            | [
                                                TextOp::PushStyles(_),
                                                TextOp::PopStyles(_),
                                                rest @ ..,
                                            ] = line
                                            {
                                                line = rest;
                                            }
                                            line
                                        }
                                        other.map_or(false, |other| {
                                            strip_indents(line) != strip_indents(other)
                                        })
                                    };
                                    let line_style = if !diff(prev_line) && !diff(next_line) {
                                        Some(&unchanged_line_style)
                                    } else {
                                        None
                                    };
                                    line_style
                                        .map(TextOp::PushStyles)
                                        .into_iter()
                                        .chain(line.iter().copied())
                                        .chain(line_style.map(TextOp::PopStyles))
                                },
                            );

                            let pretty::HtmlSnippet {
                                head_deduplicatable_elements: fragment_head,
                                body: fragment_body,
                            } = lines
                                .map(Either::Left)
                                .intersperse(Either::Right([TextOp::Text("\n")].into_iter()))
                                .flatten()
                                .into_internal()
                                .collect();

                            html.head_deduplicatable_elements.extend(fragment_head);

                            html.body += "<td>\n";
                            html.body += &fragment_body;
                            html.body += "</td>\n";
                        }
                    }
                    html.body += "</tr>\n";
                }
                html.body += "</table>";

                html
            }
        }
    }
}

impl<PF> Versions<PF> {
    pub fn map_pretty_fragments<PF2>(self, f: impl Fn(PF) -> PF2) -> Versions<PF2> {
        match self {
            Versions::Single(fragment) => Versions::Single(f(fragment)),
            Versions::Multiple {
                version_names,
                per_row_versions_with_repeat_count,
            } => Versions::Multiple {
                version_names,
                per_row_versions_with_repeat_count: per_row_versions_with_repeat_count
                    .into_iter()
                    .map(|versions_with_repeat_count| {
                        versions_with_repeat_count
                            .into_iter()
                            .map(|(fragment, repeat_count)| (f(fragment), repeat_count))
                            .collect()
                    })
                    .collect(),
            },
        }
    }
}

/// Tool for adjusting pretty-printed columns, so that their anchors line up
/// (by adding empty lines to whichever side "is behind").
#[derive(Default)]
struct AnchorAligner<'a> {
    merged_lines: Vec<AAMergedLine>,

    /// Current ("rightmost") column's anchor definitions (with indices pointing
    /// into `merged_lines`), which the next column will align to.
    //
    // FIXME(eddyb) does this need additional interning?
    anchor_def_to_merged_line_idx: FxIndexMap<&'a String, usize>,

    // FIXME(eddyb) fine-tune this inline size.
    // FIXME(eddyb) maybe don't keep most of this data around anyway?
    original_columns: SmallVec<[AAColumn<'a>; 4]>,
}

/// Abstraction for one "physical" line spanning all columns, after alignment.
struct AAMergedLine {
    // FIXME(eddyb) fine-tune this inline size.
    // FIXME(eddyb) consider using `u32` here?
    per_column_line_lengths: SmallVec<[usize; 4]>,
}

struct AAColumn<'a> {
    /// All `TextOp`s in all lines from this column, concatenated together.
    text_ops: Vec<TextOp<'a>>,

    /// The length, in `TextOp`s (from `text_ops`), of each line.
    //
    // FIXME(eddyb) consider using `u32` here?
    line_lengths: Vec<usize>,
}

impl<'a> AAColumn<'a> {
    /// Reconstruct lines (made of `TextOp`s) from line lengths.
    fn lines(
        &self,
        line_lengths: impl Iterator<Item = usize>,
    ) -> impl Iterator<Item = &[TextOp<'a>]> {
        let mut next_start = 0;
        line_lengths.map(move |len| {
            let start = next_start;
            let end = start + len;
            next_start = end;
            &self.text_ops[start..end]
        })
    }
}

// FIXME(eddyb) is this impl the best way? (maybe it should be a inherent method)
impl<'a> FromInternalIterator<TextOp<'a>> for AAColumn<'a> {
    fn from_iter<T>(text_ops: T) -> Self
    where
        T: IntoInternalIterator<Item = TextOp<'a>>,
    {
        let mut column = AAColumn {
            text_ops: vec![],
            line_lengths: vec![0],
        };
        text_ops.into_internal_iter().for_each(|op| {
            if let TextOp::Text("\n") = op {
                column.line_lengths.push(0);
            } else {
                // FIXME(eddyb) this *happens* to be true,
                // but the `LineOp`/`TextOp` split could be
                // improved to avoid such sanity checks.
                if let TextOp::Text(text) = op {
                    assert!(!text.contains('\n'));
                }
                column.text_ops.push(op);
                *column.line_lengths.last_mut().unwrap() += 1;
            }
        });
        column
    }
}

#[derive(Copy, Clone)]
struct AAMergedColumn<'a, 'b> {
    original_column: &'b AAColumn<'a>,
    column_idx: usize,
    merged_lines: &'b [AAMergedLine],
}

impl<'a, 'b> AAMergedColumn<'a, 'b> {
    fn lines(&self) -> impl Iterator<Item = &'b [TextOp<'a>]> + '_ {
        let column_idx = self.column_idx;
        let line_lengths = self
            .merged_lines
            .iter()
            .map(move |line| line.per_column_line_lengths[column_idx]);
        self.original_column.lines(line_lengths)
    }
}

impl<'a> AnchorAligner<'a> {
    /// Flatten all columns to `TextOp`s (including line separators).
    fn merged_columns(&self) -> impl Iterator<Item = AAMergedColumn<'a, '_>> {
        self.original_columns
            .iter()
            .enumerate()
            .map(|(column_idx, original_column)| {
                let mut merged_lines = &self.merged_lines[..];

                // Trim all trailing lines that are empty in this column.
                while let Some((last, before_last)) = merged_lines.split_last() {
                    if last.per_column_line_lengths[column_idx] > 0 {
                        break;
                    }
                    merged_lines = before_last;
                }

                AAMergedColumn {
                    original_column,
                    column_idx,
                    merged_lines,
                }
            })
    }

    /// Merge `new_column` into the current set of columns, aligning as many
    /// anchors as possible, between it, and the most recent column.
    fn add_column_and_align_anchors(&mut self, new_column: AAColumn<'a>) {
        // NOTE(eddyb) "old" and "new" are used to refer to the two columns being
        // aligned, but "old" maps to the *merged* lines, not its original ones.

        let old_lines = mem::take(&mut self.merged_lines);
        let old_anchor_def_to_line_idx = mem::take(&mut self.anchor_def_to_merged_line_idx);

        // Index all the anchor definitions in the new column.
        let mut new_anchor_def_to_line_idx = FxIndexMap::default();
        for (new_line_idx, new_line_text_ops) in new_column
            .lines(new_column.line_lengths.iter().copied())
            .enumerate()
        {
            for op in new_line_text_ops {
                if let TextOp::PushStyles(styles) = op {
                    if let Some(anchor) = &styles.anchor {
                        if styles.anchor_is_def {
                            new_anchor_def_to_line_idx
                                .entry(anchor)
                                .or_insert(new_line_idx);
                        }
                    }
                }
            }
        }

        // Find all the possible anchor alignments (i.e. anchors defined in both
        // "old" and "new") as pairs of line indices in "old" and "new".
        //
        // HACK(eddyb) the order is given by the "new" line index, implicitly.
        // FIXME(eddyb) fine-tune this inline size.
        let common_anchors: SmallVec<[_; 8]> = new_anchor_def_to_line_idx
            .iter()
            .filter_map(|(anchor, &new_line_idx)| {
                Some((*old_anchor_def_to_line_idx.get(anchor)?, new_line_idx))
            })
            .collect();

        // Fast-path: if all the "old" line indices are already in (increasing)
        // order (i.e. "monotonic"), they can all be used directly for alignment.
        let is_already_monotonic = {
            // FIXME(eddyb) should be `.is_sorted_by_key(|&(old_line_idx, _)| old_line_idx)`
            // but that slice method is still unstable.
            common_anchors.windows(2).all(|w| w[0].0 <= w[1].0)
        };
        let monotonic_common_anchors = if is_already_monotonic {
            common_anchors
        } else {
            // FIXME(eddyb) this could maybe avoid all the unnecessary allocations.
            longest_increasing_subsequence::lis(&common_anchors)
                .into_iter()
                .map(|i| common_anchors[i])
                .collect()
        };

        // Allocate space for the merge of "old" and "new".
        let mut merged_lines = Vec::with_capacity({
            // Cheap conservative estimate, based on the last anchor (i.e. the
            // final position of the last anchor is *at least* `min_before_last`).
            let &(old_last, new_last) = monotonic_common_anchors.last().unwrap_or(&(0, 0));
            let min_before_last = old_last.max(new_last);
            let after_last =
                (old_lines.len() - old_last).max(new_column.line_lengths.len() - new_last);
            (min_before_last + after_last).next_power_of_two()
        });

        // Build the merged lines using (partially) lockstep iteration to pull
        // the relevant data out of either side, and update "new" line indices.
        let mut old_lines = old_lines.into_iter().enumerate().peekable();
        let mut new_lines = new_column
            .line_lengths
            .iter()
            .copied()
            .enumerate()
            .peekable();
        let mut monotonic_common_anchors = monotonic_common_anchors.into_iter().peekable();
        let mut fixup_new_to_merged = new_anchor_def_to_line_idx.values_mut().peekable();
        while old_lines.len() > 0 || new_lines.len() > 0 {
            let old_line_idx = old_lines.peek().map(|&(i, _)| i);
            let new_line_idx = new_lines.peek().map(|&(i, _)| i);
            let mut next_anchor = monotonic_common_anchors.peek().copied();

            // Discard anchor alignments that have been used already, and also
            // any others that cannot be relevant anymore - this can occur when
            // multiple anchors coincide on the same line.
            while let Some((anchor_old, anchor_new)) = next_anchor {
                // NOTE(eddyb) noop anchors (i.e. those describing an alignment
                // between "old" and "new", which has already beeing reached)
                // are not considered "relevant" here, and "misalignments" are
                // preferred instead - the outcome is mostly identical to always
                // eagerly processing noop anchors, except when another anchor
                // is overlapping (in only one of "old" or "new"), as it will
                // only get get processed if the noop one is skipped first.
                let relevant = match (old_line_idx, new_line_idx) {
                    (Some(old), Some(new)) => old < anchor_old || new < anchor_new,
                    _ => false,
                };
                if relevant {
                    break;
                }
                monotonic_common_anchors.next().unwrap();
                next_anchor = monotonic_common_anchors.peek().copied();
            }

            // Figure out which side has to wait, to align an upcoming anchor.
            let (old_at_anchor, new_at_anchor) =
                next_anchor.map_or((false, false), |(anchor_old, anchor_new)| {
                    (
                        old_line_idx.map_or(false, |old| old == anchor_old),
                        new_line_idx.map_or(false, |new| new == anchor_new),
                    )
                });
            let old_line = if old_at_anchor && !new_at_anchor {
                // Pausing "old", waiting for "new".
                None
            } else {
                old_lines.next().map(|(_, old_line)| old_line)
            };
            let new_line_len = if !old_at_anchor && new_at_anchor {
                // Pausing "new", waiting for "old".
                None
            } else {
                new_lines.next().map(|(_, new_line_len)| new_line_len)
            };

            // When the "new" side is advanced, that "sets" the merged line index
            // of the consumed line, which can then be used for fixing up indices.
            if new_line_len.is_some() {
                let new_line_idx = new_line_idx.unwrap();
                let merged_line_idx = merged_lines.len();
                while fixup_new_to_merged.peek().map(|i| **i) == Some(new_line_idx) {
                    *fixup_new_to_merged.next().unwrap() = merged_line_idx;
                }
            }

            let new_line_len = new_line_len.unwrap_or(0);
            let merged_line = match old_line {
                Some(mut line) => {
                    line.per_column_line_lengths.push(new_line_len);
                    line
                }
                None => AAMergedLine {
                    per_column_line_lengths: (0..self.original_columns.len())
                        .map(|_| 0)
                        .chain([new_line_len])
                        .collect(),
                },
            };
            merged_lines.push(merged_line);
        }

        self.merged_lines = merged_lines;
        self.anchor_def_to_merged_line_idx = new_anchor_def_to_line_idx;
        self.original_columns.push(new_column);
    }
}
