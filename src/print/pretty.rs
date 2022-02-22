//! Pretty-printing functionality (such as automatic indentation).

// FIXME(eddyb) stop using `itertools` for methods like `intersperse` when they
// get stabilized on `Iterator` instead.
#![allow(unstable_name_collisions)]
use itertools::Itertools as _;

use smallvec::SmallVec;
use std::borrow::Cow;
use std::iter;

/// Part of a pretty document, made up of `Node`s.
pub struct Fragment<'a> {
    pub nodes: SmallVec<[Node<'a>; 8]>,
}

#[derive(Clone)]
pub enum Node<'a> {
    // FIXME(eddyb) make this more like a "DOM" instead of flatly stateful.
    PushIndent,
    PopIndent,

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

impl<'a> Fragment<'a> {
    pub fn new(nodes: impl IntoIterator<Item = Node<'a>>) -> Self {
        Self {
            nodes: nodes.into_iter().collect(),
        }
    }

    /// Flatten the `Fragment` to plain text (indented where necessary).
    pub fn render(
        self,
        // FIXME(eddyb) fit this into `{Push,Pop}Indent` somehow.
        multi_line_override: Option<bool>,
    ) -> String {
        // FIXME(eddyb) make max line width configurable.
        let max_line_len = 80;
        let fits_on_single_line = self
            .nodes
            .iter()
            .map(|node| node.for_single_line())
            .try_fold(0usize, |single_line_len, node| {
                if node.contains("\n") {
                    return None;
                }
                single_line_len
                    .checked_add(node.len())
                    .filter(|&len| len <= max_line_len)
            })
            .is_some();
        let fits_on_single_line = multi_line_override
            .map(|force_multi_line| !force_multi_line)
            .unwrap_or(fits_on_single_line);

        // FIXME(eddyb) make this configurable.
        const INDENT: &str = "  ";

        let mk_reindented_nodes = || {
            /// Operation on a representation that stores lines separately.
            /// Such a representation doesn't exist yet - instead, an iterator
            /// of `LineOp`s is turned into an iterator of `&str`s.
            #[derive(Copy, Clone)]
            enum LineOp<'a> {
                AppendToLine(&'a str),
                StartNewLine { indent_after: u32 },
            }

            let mut indent = 0;
            let mut line_ops = self
                .nodes
                .iter()
                .flat_map(move |node| {
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

                    node_text.split('\n').map(LineOp::AppendToLine).intersperse(
                        LineOp::StartNewLine {
                            indent_after: indent,
                        },
                    )
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
    contents: impl IntoIterator<Item = String>,
    suffix: &'a str,
) -> Fragment<'a> {
    Fragment::new(
        [
            prefix.into(),
            Node::PushIndent,
            Node::Joiner {
                single_line: "",
                multi_line: "\n",
            },
        ]
        .into_iter()
        .chain(
            contents
                .into_iter()
                .map(|entry| Node::Text(entry.into()))
                .intersperse(Node::Joiner {
                    single_line: ", ",
                    multi_line: ",\n",
                }),
        )
        .chain([
            Node::PopIndent,
            Node::Joiner {
                single_line: "",
                multi_line: ",\n",
            },
            suffix.into(),
        ]),
    )
}
