//! Pretty-printing functionality (such as automatic indentation).

// FIXME(eddyb) stop using `itertools` for methods like `intersperse` when they
// get stabilized on `Iterator` instead.
#![allow(unstable_name_collisions)]
use itertools::Itertools as _;

use smallvec::SmallVec;
use std::borrow::Cow;
use std::iter;

/// Part of a pretty document, made up of `Node`s.
#[derive(Clone)]
pub struct Fragment<'a> {
    pub nodes: SmallVec<[Node<'a>; 8]>,
}

#[derive(Clone)]
pub enum Node<'a> {
    // FIXME(eddyb) make this more like a "DOM" instead of flatly stateful.
    PushIndent,
    PopIndent,

    /// Require that nodes before and after this node, are separated by some
    /// whitespace (either by a single space, or by being on different lines).
    ///
    /// This is similar in effect to a `Text(" ")`, except that it doesn't add
    /// leading/trailing spaces when found at the start/end of a line, as the
    /// adjacent `\n` is enough of a "breaking space".
    ///
    /// Conversely, `Text(" ")` can be considered a "non-breaking space" (NBSP).
    BreakingOnlySpace,

    /// Require that nodes before and after this node, go on different lines.
    ///
    /// This is similar in effect to a `Text("\n")`, except that it doesn't
    /// introduce a new `\n` when the previous/next node(s) already end/start
    /// on a new line (whether from `Text("\n")` or another `ForceLineStart`).
    ForceLineSeparation,

    IfMultiLine(&'a Node<'a>),

    Text(Cow<'a, str>),
}

impl<'a> From<&'a str> for Node<'a> {
    fn from(text: &'a str) -> Self {
        Self::Text(text.into())
    }
}

impl From<String> for Node<'_> {
    fn from(text: String) -> Self {
        Self::Text(text.into())
    }
}

impl<'a, T: Into<Node<'a>>> From<T> for Fragment<'a> {
    fn from(x: T) -> Self {
        Self::new([x.into()])
    }
}

impl<'a> Fragment<'a> {
    pub fn new(nodes: impl IntoIterator<Item = Node<'a>>) -> Self {
        Self {
            nodes: nodes.into_iter().collect(),
        }
    }

    /// Flatten the `Fragment` to plain text (indented where necessary).
    pub fn render(self) -> String {
        // FIXME(eddyb) make max line width configurable.
        let max_line_len = 80;
        let fits_on_single_line = self
            .nodes
            .iter()
            .try_fold(0usize, |single_line_len, node| {
                let node_text = match node {
                    Node::PushIndent | Node::PopIndent => "",
                    Node::BreakingOnlySpace => " ",
                    Node::ForceLineSeparation => return None,
                    Node::Text(s) => s,
                    Node::IfMultiLine(_) => "",
                };
                if node_text.contains("\n") {
                    return None;
                }
                single_line_len
                    .checked_add(node_text.len())
                    .filter(|&len| len <= max_line_len)
            })
            .is_some();

        // FIXME(eddyb) make this configurable.
        const INDENT: &str = "  ";

        let mk_reindented_nodes = || {
            /// Operation on a representation that stores lines separately.
            /// Such a representation doesn't exist yet - instead, an iterator
            /// of `LineOp`s is turned into an iterator of `&str`s.
            #[derive(Copy, Clone)]
            enum LineOp<'a> {
                AppendToLine { indent_before: u32, text: &'a str },
                StartNewLine,
                BreakIfWithinLine(Break),
            }
            #[derive(Copy, Clone)]
            enum Break {
                Space,
                NewLine,
            }

            let mut indent = 0;
            let line_ops = self.nodes.iter().flat_map(move |node| {
                let mut node = node;
                if !fits_on_single_line {
                    while let Node::IfMultiLine(multi_line_node) = node {
                        node = multi_line_node;
                    }
                }
                let (node_text, special_op) = match node {
                    Node::PushIndent => {
                        indent += 1;
                        ("", None)
                    }
                    Node::PopIndent => {
                        assert!(indent > 0);
                        indent -= 1;
                        ("", None)
                    }
                    Node::BreakingOnlySpace => ("", Some(LineOp::BreakIfWithinLine(Break::Space))),
                    Node::ForceLineSeparation => {
                        ("", Some(LineOp::BreakIfWithinLine(Break::NewLine)))
                    }
                    Node::IfMultiLine(_) => ("", None),
                    Node::Text(s) => (&s[..], None),
                };

                node_text
                    .split('\n')
                    .map(move |text| LineOp::AppendToLine {
                        indent_before: indent,
                        text,
                    })
                    .intersperse(LineOp::StartNewLine)
                    .chain(special_op)
            });

            // When `on_empty_new_line` is `true`, a new line was started, but
            // lacks text, so the `LineOp::AppendToLine { indent_before, text }`
            // first on that line (with non-empty `text`) needs to materialize
            // `indent_before` levels of indentation (before its `text` content).
            //
            // NOTE(eddyb) indentation is not immediatelly materialized in order
            // to avoid trailing whitespace on otherwise-empty lines.
            let mut on_empty_new_line = true;

            // Deferred `LineOp::BreakIfWithinLine`, which will be materialized
            // only between two consecutive `LineOp::AppendToLine { text, .. }`
            // (with non-empty `text`), that (would) share the same line.
            let mut pending_break_if_within_line = None;

            line_ops
                .filter(|op| {
                    // Do not allow (accidental) side-effects from no-op `op`s.
                    !matches!(op, LineOp::AppendToLine { text: "", .. })
                })
                .flat_map(move |op| {
                    let pre_text = match op {
                        LineOp::AppendToLine { indent_before, .. } => {
                            let (br, need_indent) = match pending_break_if_within_line {
                                Some(Break::Space) => (" ", false),
                                Some(Break::NewLine) => ("\n", true),
                                None => ("", on_empty_new_line),
                            };
                            let indent = if need_indent { indent_before } else { 0 };
                            Some(iter::once(br).chain((0..indent).map(|_| INDENT)))
                        }

                        _ => None,
                    };

                    let text = match op {
                        LineOp::AppendToLine { text, .. } => {
                            on_empty_new_line = false;
                            pending_break_if_within_line = None;

                            text
                        }

                        LineOp::StartNewLine => {
                            on_empty_new_line = true;
                            pending_break_if_within_line = None;

                            "\n"
                        }

                        LineOp::BreakIfWithinLine(br) => {
                            if !on_empty_new_line {
                                // Merge two pending `Break`s if necessary,
                                // preferring newlines over spaces.
                                let br = match (pending_break_if_within_line, br) {
                                    (Some(Break::NewLine), _) | (_, Break::NewLine) => {
                                        Break::NewLine
                                    }
                                    (None | Some(Break::Space), Break::Space) => Break::Space,
                                };

                                pending_break_if_within_line = Some(br);
                            }
                            ""
                        }
                    };

                    pre_text.into_iter().flatten().chain([text])
                })
        };
        let mut combined = String::with_capacity(mk_reindented_nodes().map(|s| s.len()).sum());
        combined.extend(mk_reindented_nodes());
        combined
    }
}

// FIXME(eddyb) encode this as a single `Node` with children.
fn maybe_multi_line_indentable_group<'a>(
    children: impl IntoIterator<Item = Fragment<'a>>,
) -> impl Iterator<Item = Node<'a>> {
    iter::once(Node::PushIndent)
        .chain(children.into_iter().flat_map(|child| {
            iter::once(Node::IfMultiLine(&Node::ForceLineSeparation))
                .chain(child.nodes)
                .chain([Node::IfMultiLine(&Node::ForceLineSeparation)])
        }))
        .chain([Node::PopIndent])
}

/// Constructs the `Fragment` corresponding to one of:
/// * single-line: `header + " " + contents.join(" ")`
/// * multi-line: `header + "\n" + indent(contents).join("\n")`
pub fn join_space(header: &str, contents: impl IntoIterator<Item = String>) -> Fragment<'_> {
    Fragment::new(
        iter::once(header.into()).chain(maybe_multi_line_indentable_group(
            contents
                .into_iter()
                .map(|entry| Fragment::new([Node::BreakingOnlySpace, entry.into()])),
        )),
    )
}

/// Constructs the `Fragment` corresponding to one of:
/// * single-line: `prefix + contents.join(", ") + suffix`
/// * multi-line: `prefix + "\n" + indent(contents).join(",\n") + ",\n" + suffix`
pub fn join_comma_sep<'a>(
    prefix: &'a str,
    contents: impl IntoIterator<Item = impl Into<Fragment<'a>>>,
    suffix: &'a str,
) -> Fragment<'a> {
    let mut children: SmallVec<[_; 8]> = contents.into_iter().map(Into::into).collect();

    if let Some((last_child, non_last_children)) = children.split_last_mut() {
        for non_last_child in non_last_children {
            non_last_child
                .nodes
                .extend([",".into(), Node::BreakingOnlySpace]);
        }

        // Trailing comma is only needed after the very last element.
        last_child
            .nodes
            .push(Node::IfMultiLine(&Node::Text(Cow::Borrowed(","))));
    }

    Fragment::new(
        iter::once(prefix.into())
            .chain(maybe_multi_line_indentable_group(children))
            .chain([suffix.into()]),
    )
}
