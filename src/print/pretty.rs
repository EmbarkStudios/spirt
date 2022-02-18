//! Pretty-printing functionality (such as automatic indentation).

// FIXME(eddyb) stop using `itertools` for methods like `intersperse` when they
// get stabilized on `Iterator` instead.
#![allow(unstable_name_collisions)]
use itertools::Itertools as _;

use smallvec::SmallVec;
use std::borrow::Cow;
use std::iter;

#[derive(Clone)]
pub enum Piece<'a> {
    // FIXME(eddyb) make this more like a "DOM" instead of flatly stateful.
    PushIndent,
    PopIndent,

    Joiner {
        single_line: &'a str,
        multi_line: &'a str,
    },

    Text(Cow<'a, str>),
}

impl<'a> From<&'a str> for Piece<'a> {
    fn from(text: &'a str) -> Self {
        Self::Text(text.into())
    }
}

impl From<String> for Piece<'_> {
    fn from(text: String) -> Self {
        Self::Text(text.into())
    }
}

impl Piece<'_> {
    fn for_single_line(&self) -> &str {
        match self {
            Self::PushIndent | Self::PopIndent => "",
            Self::Text(s) => s,
            Self::Joiner { single_line, .. } => single_line,
        }
    }
    fn for_multi_line(&self) -> &str {
        match self {
            Self::PushIndent | Self::PopIndent => "",
            Self::Text(s) => s,
            Self::Joiner { multi_line, .. } => multi_line,
        }
    }
}

/// Returns a concatenation of `pieces` using `.for_single_line()` if the
/// resulting string can fit on one line, or a multi-line indented version
/// otherwise (`.for_multi_line()` and `{Push,Pop}Indent`-driven indentation).
pub fn concat_pieces<'a>(
    pieces: impl IntoIterator<Item = Piece<'a>>,
    // FIXME(eddyb) fit this into `{Push,Pop}Indent` somehow.
    multi_line_override: Option<bool>,
) -> String {
    let pieces: SmallVec<[_; 16]> = pieces.into_iter().collect();

    // FIXME(eddyb) make max line width configurable.
    let max_line_len = 80;
    let fits_on_single_line = pieces
        .iter()
        .map(|piece| piece.for_single_line())
        .try_fold(0usize, |single_line_len, piece| {
            if piece.contains("\n") {
                return None;
            }
            single_line_len
                .checked_add(piece.len())
                .filter(|&len| len <= max_line_len)
        })
        .is_some();
    let fits_on_single_line = multi_line_override
        .map(|force_multi_line| !force_multi_line)
        .unwrap_or(fits_on_single_line);

    // FIXME(eddyb) make this configurable.
    const INDENT: &str = "  ";

    let mk_reindented_pieces = || {
        /// Operation on a representation that stores lines separately.
        /// Such a representation doesn't exist yet - instead, an iterator
        /// of `LineOp`s is turned into an iterator of `&str`s.
        #[derive(Copy, Clone)]
        enum LineOp<'a> {
            AppendToLine(&'a str),
            StartNewLine { indent_after: u32 },
        }

        let mut indent = 0;
        let mut line_ops = pieces
            .iter()
            .flat_map(move |piece| {
                match piece {
                    Piece::PushIndent => indent += 1,
                    Piece::PopIndent => {
                        assert!(indent > 0);
                        indent -= 1;
                    }
                    _ => {}
                }

                let piece_text = if fits_on_single_line {
                    piece.for_single_line()
                } else {
                    piece.for_multi_line()
                };

                piece_text
                    .split('\n')
                    .map(LineOp::AppendToLine)
                    .intersperse(LineOp::StartNewLine {
                        indent_after: indent,
                    })
            })
            .filter(|op| !matches!(op, LineOp::AppendToLine("")))
            .peekable();

        iter::from_fn(move || {
            let (text, indent_after) = match line_ops.next()? {
                LineOp::AppendToLine(text) => (text, 0),
                LineOp::StartNewLine { indent_after } => {
                    // HACK(eddyb) this is not perfect because we don't have
                    // the entire document ahead of time, but it does avoid
                    // any trailing indentation internal to any one call.
                    let is_starting_empty_line =
                        matches!(line_ops.peek(), Some(LineOp::StartNewLine { .. }));

                    (
                        "\n",
                        if is_starting_empty_line {
                            0
                        } else {
                            indent_after
                        },
                    )
                }
            };
            Some(iter::once(text).chain((0..indent_after).map(|_| INDENT)))
        })
        .flatten()
    };
    let mut combined = String::with_capacity(mk_reindented_pieces().map(|s| s.len()).sum());
    combined.extend(mk_reindented_pieces());
    combined
}

/// Returns `header + " " + contents.join(" ")` if the resulting string can fit
/// on one line, or a multi-line indented version otherwise.
pub fn join_space(header: &str, contents: impl IntoIterator<Item = String>) -> String {
    concat_pieces(
        [header.into(), Piece::PushIndent]
            .into_iter()
            .chain(contents.into_iter().flat_map(|entry| {
                [
                    Piece::Joiner {
                        single_line: " ",
                        multi_line: "\n",
                    },
                    entry.into(),
                ]
            }))
            .chain([Piece::PopIndent]),
        None,
    )
}

// FIXME(eddyb) remove the need for this by replacing `prefix`/`suffix` with
// some `enum` that also determines whether to force the multi-line format.
// Alternatively, `contents` values could indicate whether they have to be
// on their own lines (without including extra `\n` themselves).
pub fn join_comma_sep_with_multiline_override(
    prefix: &str,
    contents: impl IntoIterator<Item = String>,
    suffix: &str,
    multi_line_override: Option<bool>,
) -> String {
    concat_pieces(
        [
            prefix.into(),
            Piece::PushIndent,
            Piece::Joiner {
                single_line: "",
                multi_line: "\n",
            },
        ]
        .into_iter()
        .chain(
            contents
                .into_iter()
                .map(|entry| Piece::Text(entry.into()))
                .intersperse(Piece::Joiner {
                    single_line: ", ",
                    multi_line: ",\n",
                }),
        )
        .chain([
            Piece::PopIndent,
            Piece::Joiner {
                single_line: "",
                multi_line: ",\n",
            },
            suffix.into(),
        ]),
        multi_line_override,
    )
}

/// Returns `prefix + contents.join(", ") + suffix` if the resulting string can
/// fit on one line, or a multi-line indented version otherwise.
pub fn join_comma_sep(
    prefix: &str,
    contents: impl IntoIterator<Item = String>,
    suffix: &str,
) -> String {
    join_comma_sep_with_multiline_override(prefix, contents, suffix, None)
}
