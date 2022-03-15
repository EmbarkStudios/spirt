//! Pretty-printing functionality (such as automatic indentation).

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
    Text(Cow<'a, str>),

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

    // FIXME(eddyb) remove this allocation (likely by removing `IfBlockLayout`).
    IfBlockLayout(Box<Node<'a>>),
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
    //
    // FIXME(eddyb) rename this to `layout_and_render` or something, when it's
    // not called all over the place.
    pub fn render(mut self) -> String {
        // FIXME(eddyb) make max line width configurable.
        let max_line_width = 80;

        self.approx_layout(MaxWidths {
            inline: max_line_width,
            block: max_line_width,
        });

        let mut out = String::new();
        self.render_to_line_ops(&mut LineOp::interpret_with(|text| out += text));
        out
    }
}

// Rendering implementation details (including approximate layout).

/// The approximate shape of a `Node`, regarding its 2D placement.
enum ApproxLayout {
    /// Only occupies part of a line, (at most) `worst_width` columns wide.
    ///
    /// `worst_width` can exceed the `inline` field of `MaxWidths`, in which
    /// case the choice of inline vs block is instead made by a surrounding node.
    Inline { worst_width: usize },

    /// Needs to occupy multiple lines.
    Block,
}

impl ApproxLayout {
    fn append(self, other: Self) -> Self {
        match (self, other) {
            (Self::Block, _) | (_, Self::Block) => Self::Block,
            (Self::Inline { worst_width: a }, Self::Inline { worst_width: b }) => Self::Inline {
                worst_width: a.checked_add(b).unwrap(),
            },
        }
    }
}

/// Maximum numbers of columns, available to a `Node`, for both inline layout
/// and block layout (i.e. multi-line with indentation).
///
/// That is, these are the best-case scenarios across all possible choices of
/// inline vs block for all surrounding nodes (up to the root) that admit both
/// cases, and those choices will be made inside-out based on actual widths.
#[derive(Copy, Clone)]
struct MaxWidths {
    inline: usize,
    block: usize,
}

impl Node<'_> {
    /// Determine the `ApproxLayout` of this `Node`, while making any necessary
    /// adjustments, in order to fit within the provided `max_widths`.
    fn approx_layout(&mut self, max_widths: MaxWidths) -> ApproxLayout {
        match self {
            Self::Text(text) => {
                if text.contains('\n') {
                    ApproxLayout::Block
                } else {
                    // FIXME(eddyb) use `unicode-width` crate for accurate column count.
                    let width = text.len();

                    ApproxLayout::Inline { worst_width: width }
                }
            }

            Self::PushIndent | Self::PopIndent => ApproxLayout::Inline { worst_width: 0 },
            Self::BreakingOnlySpace => ApproxLayout::Inline { worst_width: 1 },
            Self::ForceLineSeparation => ApproxLayout::Block,
            Self::IfBlockLayout(block_version) => {
                // Keep the inline `worst_width`, just in case this node is
                // going to be used as part of an inline child of a block.
                // NOTE(eddyb) this is currently only the case for the trailing
                // comma added by `join_comma_sep`.
                let worst_width = match block_version.approx_layout(max_widths) {
                    ApproxLayout::Inline { worst_width } => worst_width,
                    ApproxLayout::Block => 0,
                };
                ApproxLayout::Inline { worst_width }
            }
        }
    }
}

impl Fragment<'_> {
    /// Determine the `ApproxLayout` of this `Fragment`, while making any
    /// necessary adjustments, in order to fit within the provided `max_widths`.
    fn approx_layout(&mut self, max_widths: MaxWidths) -> ApproxLayout {
        let mut layout = ApproxLayout::Inline { worst_width: 0 };
        for child in &mut self.nodes {
            let child_layout = child.approx_layout(MaxWidths {
                inline: match layout {
                    ApproxLayout::Inline { worst_width } => {
                        max_widths.inline.saturating_sub(worst_width)
                    }
                    ApproxLayout::Block => 0,
                },
                block: max_widths.block,
            });
            layout = layout.append(child_layout);
        }

        // HACK(eddyb) this treats the entire `Fragment` as a decision point for
        // inline vs block layout, ideally that should be a `Node` variant.
        if let ApproxLayout::Inline { worst_width } = layout {
            if worst_width > max_widths.inline {
                layout = ApproxLayout::Block;
            }
        }

        self.nodes.retain(|node| match node {
            Node::IfBlockLayout(block_version) => {
                if let ApproxLayout::Inline { .. } = layout {
                    false
                } else {
                    *node = (**block_version).clone();
                    assert!(!matches!(node, Node::IfBlockLayout(_)));
                    true
                }
            }
            _ => true,
        });

        layout
    }
}

/// Line-oriented operation (i.e. as if lines are stored separately).
///
/// However, a representation that stores lines separately doesn't really exist,
/// and instead `LineOp`s are (statefully) transformed into `&str`s on the fly
/// (see `LineOp::interpret_with`).
#[derive(Copy, Clone)]
enum LineOp<'a> {
    PushIndent,
    PopIndent,

    AppendToLine(&'a str),
    StartNewLine,
    BreakIfWithinLine(Break),
}

#[derive(Copy, Clone)]
enum Break {
    Space,
    NewLine,
}

impl Node<'_> {
    /// Flatten the `Fragment` to `LineOp`s, passed to `each_line_op`.
    fn render_to_line_ops(&self, each_line_op: &mut impl FnMut(LineOp<'_>)) {
        match self {
            Self::Text(text) => {
                let mut lines = text.split('\n');
                each_line_op(LineOp::AppendToLine(lines.next().unwrap()));
                for line in lines {
                    each_line_op(LineOp::StartNewLine);
                    each_line_op(LineOp::AppendToLine(line));
                }
            }

            Self::PushIndent => each_line_op(LineOp::PushIndent),
            Self::PopIndent => each_line_op(LineOp::PopIndent),
            Self::BreakingOnlySpace => each_line_op(LineOp::BreakIfWithinLine(Break::Space)),
            Self::ForceLineSeparation => each_line_op(LineOp::BreakIfWithinLine(Break::NewLine)),
            Self::IfBlockLayout(_) => unreachable!(),
        }
    }
}

impl Fragment<'_> {
    /// Flatten the `Fragment` to `LineOp`s, passed to `each_line_op`.
    fn render_to_line_ops(&self, each_line_op: &mut impl FnMut(LineOp<'_>)) {
        for node in &self.nodes {
            node.render_to_line_ops(each_line_op);
        }
    }
}

impl LineOp<'_> {
    /// Expand `LineOp`s passed to the returned `impl FnMut(LineOp<'_>)` closure,
    /// forwarding the expanded `&str` pieces to `each_str_piece`.
    //
    // FIXME(eddyb) this'd be nicer if instead of returning a closure, it could
    // be passed to an `impl for<F: FnMut(LineOp<'_>)> FnOnce(F)` callback.
    fn interpret_with(mut each_str_piece: impl FnMut(&str)) -> impl FnMut(LineOp<'_>) {
        // FIXME(eddyb) make this configurable.
        const INDENT: &str = "  ";

        let mut indent = 0;

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

        move |op| {
            // Do not allow (accidental) side-effects from no-op `op`s.
            if let LineOp::AppendToLine("") = op {
                return;
            }

            if let LineOp::AppendToLine(_) = op {
                let need_indent = match pending_break_if_within_line {
                    Some(br) => {
                        each_str_piece(match br {
                            Break::Space => " ",
                            Break::NewLine => "\n",
                        });
                        matches!(br, Break::NewLine)
                    }
                    None => on_empty_new_line,
                };
                if need_indent {
                    for _ in 0..indent {
                        each_str_piece(INDENT);
                    }
                }
            }

            match op {
                LineOp::PushIndent => {
                    indent += 1;
                }

                LineOp::PopIndent => {
                    assert!(indent > 0);
                    indent -= 1;
                }

                LineOp::AppendToLine(text) => {
                    each_str_piece(text);

                    on_empty_new_line = false;
                    pending_break_if_within_line = None;
                }

                LineOp::StartNewLine => {
                    each_str_piece("\n");

                    on_empty_new_line = true;
                    pending_break_if_within_line = None;
                }

                LineOp::BreakIfWithinLine(br) => {
                    if !on_empty_new_line {
                        // Merge two pending `Break`s if necessary,
                        // preferring newlines over spaces.
                        let br = match (pending_break_if_within_line, br) {
                            (Some(Break::NewLine), _) | (_, Break::NewLine) => Break::NewLine,
                            (None | Some(Break::Space), Break::Space) => Break::Space,
                        };

                        pending_break_if_within_line = Some(br);
                    }
                }
            }
        }
    }
}

// Pretty fragment "constructors".
//
// FIXME(eddyb) should these be methods on `Node`/`Fragment`?

// FIXME(eddyb) encode this as a single `Node` with children.
fn inline_or_block<'a>(
    children: impl IntoIterator<Item = Fragment<'a>>,
) -> impl Iterator<Item = Node<'a>> {
    iter::once(Node::PushIndent)
        .chain(children.into_iter().flat_map(|child| {
            iter::once(Node::IfBlockLayout(Box::new(Node::ForceLineSeparation)))
                .chain(child.nodes)
                .chain([Node::IfBlockLayout(Box::new(Node::ForceLineSeparation))])
        }))
        .chain([Node::PopIndent])
}

/// Constructs the `Fragment` corresponding to one of:
/// * inline layout: `header + " " + contents.join(" ")`
/// * block layout: `header + "\n" + indent(contents).join("\n")`
pub fn join_space(header: &str, contents: impl IntoIterator<Item = String>) -> Fragment<'_> {
    Fragment::new(
        iter::once(header.into()).chain(inline_or_block(
            contents
                .into_iter()
                .map(|entry| Fragment::new([Node::BreakingOnlySpace, entry.into()])),
        )),
    )
}

/// Constructs the `Fragment` corresponding to one of:
/// * inline layout: `prefix + contents.join(", ") + suffix`
/// * block layout: `prefix + "\n" + indent(contents).join(",\n") + ",\n" + suffix`
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
            .push(Node::IfBlockLayout(Box::new(Node::Text(Cow::Borrowed(
                ",",
            )))));
    }

    Fragment::new(
        iter::once(prefix.into())
            .chain(inline_or_block(children))
            .chain([suffix.into()]),
    )
}
