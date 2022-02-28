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

    /// Require that nodes before and after this node, go on different lines.
    ///
    /// This is similar in effect to a `Text("\n")`, except that it doesn't
    /// introduce a new `\n` when the previous node(s) had already started
    /// an (empty) new line (e.g. `Text("...\n")` or another `ForceLineStart`).
    ForceLineSeparation,

    Joiner {
        single_line: &'a str,
        multi_line: &'a str,
    },

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

impl Node<'_> {
    fn for_single_line(&self) -> &str {
        match self {
            Self::PushIndent | Self::PopIndent => "",
            Self::ForceLineSeparation => unreachable!(),
            Self::Text(s) => s,
            Self::Joiner { single_line, .. } => single_line,
        }
    }
    fn for_multi_line(&self) -> &str {
        match self {
            Self::PushIndent | Self::PopIndent => "",
            Self::ForceLineSeparation => "\n",
            Self::Text(s) => s,
            Self::Joiner { multi_line, .. } => multi_line,
        }
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
                if let Node::ForceLineSeparation = node {
                    return None;
                }
                let node_text = node.for_single_line();
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
                ForceLineSeparation,
            }

            let mut indent = 0;
            let line_ops = self.nodes.iter().flat_map(move |node| {
                match node {
                    Node::PushIndent => indent += 1,
                    Node::PopIndent => {
                        assert!(indent > 0);
                        indent -= 1;
                    }
                    _ => {}
                }

                let node_text = if fits_on_single_line {
                    node.for_single_line()
                } else {
                    node.for_multi_line()
                };

                node_text
                    .split('\n')
                    .map(move |text| LineOp::AppendToLine {
                        indent_before: indent,
                        text,
                    })
                    .intersperse(if let Node::ForceLineSeparation = node {
                        LineOp::ForceLineSeparation
                    } else {
                        LineOp::StartNewLine
                    })
            });

            // When `on_empty_new_line` is `true`, a new line was started, but
            // lacks text, so the `LineOp::AppendToLine { indent_before, text }`
            // first on that line (with non-empty `text`) needs to materialize
            // `indent_before` levels of indentation (before its `text` content).
            //
            // NOTE(eddyb) indentation is not immediatelly materialized in order
            // to avoid trailing whitespace on otherwise-empty lines.
            let mut on_empty_new_line = true;

            line_ops.flat_map(move |op| {
                let indent_before = match op {
                    LineOp::AppendToLine {
                        indent_before,
                        text,
                    } if on_empty_new_line && text != "" => indent_before,

                    _ => 0,
                };

                let text = match op {
                    LineOp::AppendToLine { text, .. } => text,

                    // NOTE(eddyb) reuse the last `\n` if no text came after it,
                    // to avoid creating unnecessary empty lines.
                    LineOp::ForceLineSeparation if on_empty_new_line => "",

                    LineOp::StartNewLine | LineOp::ForceLineSeparation => "\n",
                };

                if (indent_before, text) != (0, "") {
                    on_empty_new_line =
                        matches!(op, LineOp::StartNewLine | LineOp::ForceLineSeparation);
                }

                (0..indent_before).map(|_| INDENT).chain([text])
            })
        };
        let mut combined = String::with_capacity(mk_reindented_nodes().map(|s| s.len()).sum());
        combined.extend(mk_reindented_nodes());
        combined
    }
}

/// Constructs the `Fragment` corresponding to one of:
/// * single-line: `header + " " + contents.join(" ")`
/// * multi-line: `header + "\n" + indent(contents).join("\n")`
pub fn join_space(header: &str, contents: impl IntoIterator<Item = String>) -> Fragment<'_> {
    Fragment::new(
        [header.into(), Node::PushIndent]
            .into_iter()
            .chain(contents.into_iter().flat_map(|entry| {
                [
                    Node::Joiner {
                        single_line: " ",
                        multi_line: "\n",
                    },
                    entry.into(),
                ]
            }))
            .chain([Node::PopIndent]),
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
    Fragment::new(
        [prefix.into(), Node::PushIndent]
            .into_iter()
            .chain(
                contents
                    .into_iter()
                    .map(|entry| {
                        Fragment::new(
                            iter::once(Node::Joiner {
                                single_line: "",
                                multi_line: "\n",
                            })
                            .chain(entry.into().nodes)
                            .chain([Node::Joiner {
                                single_line: "",
                                multi_line: ",",
                            }]),
                        )
                    })
                    .intersperse(Fragment::new([Node::Joiner {
                        single_line: ", ",
                        multi_line: "",
                    }]))
                    .flat_map(|fragment| fragment.nodes),
            )
            .chain([
                Node::PopIndent,
                // FIXME(eddyb) this causes `prefix + "\n" + suffix` output when
                // `contents` is empty, instead of `prefix + suffix`.
                Node::Joiner {
                    single_line: "",
                    multi_line: "\n",
                },
                suffix.into(),
            ]),
    )
}
