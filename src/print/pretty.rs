//! Pretty-printing functionality (such as automatic indentation).

use smallvec::SmallVec;
use std::borrow::Cow;
use std::{iter, mem};

/// Part of a pretty document, made up of `Node`s.
#[derive(Clone, Default)]
pub struct Fragment {
    pub nodes: SmallVec<[Node; 8]>,
}

#[derive(Clone)]
pub enum Node {
    Text(Cow<'static, str>),

    /// Container for `Fragment`s, using block layout (indented on separate lines).
    IndentedBlock(Vec<Fragment>),

    /// Container for `Fragment`s, either using inline layout (all on one line)
    /// or block layout (indented on separate lines).
    InlineOrIndentedBlock(Vec<Fragment>),

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

    // FIXME(eddyb) replace this with something lower-level than layout.
    IfBlockLayout(&'static str),
}

impl From<&'static str> for Node {
    fn from(text: &'static str) -> Self {
        Self::Text(text.into())
    }
}

impl From<String> for Node {
    fn from(text: String) -> Self {
        Self::Text(text.into())
    }
}

impl<T: Into<Node>> From<T> for Fragment {
    fn from(x: T) -> Self {
        Self {
            nodes: iter::once(x.into()).into_iter().collect(),
        }
    }
}

impl Fragment {
    pub fn new(fragments: impl IntoIterator<Item = impl Into<Self>>) -> Self {
        Self {
            nodes: fragments
                .into_iter()
                .flat_map(|fragment| fragment.into().nodes)
                .collect(),
        }
    }

    /// Perform layout on, and flatten the `Fragment` to plain text.
    pub fn layout_and_render_to_string(mut self) -> String {
        // FIXME(eddyb) make max line width configurable.
        let max_line_width = 100;

        self.approx_layout(MaxWidths {
            inline: max_line_width,
            block: max_line_width,
        });

        let mut out = String::new();
        self.render_to_line_ops(&mut LineOp::interpret_with(|text| out += text), false);
        out
    }
}

// Rendering implementation details (including approximate layout).

/// The approximate shape of a `Node`, regarding its 2D placement.
#[derive(Copy, Clone)]
enum ApproxLayout {
    /// Only occupies part of a line, (at most) `worst_width` columns wide.
    ///
    /// `worst_width` can exceed the `inline` field of `MaxWidths`, in which
    /// case the choice of inline vs block is instead made by a surrounding node.
    Inline { worst_width: usize },

    /// Needs to occupy multiple lines, but may also have the equivalent of
    /// an `Inline` before (`pre_`) and after (`post_`) the multi-line block.
    //
    // FIXME(eddyb) maybe turn `ApproxLayout` into a `struct` instead?
    BlockOrMixed {
        pre_worst_width: usize,
        post_worst_width: usize,
    },
}

impl ApproxLayout {
    fn append(self, other: Self) -> Self {
        match (self, other) {
            (Self::Inline { worst_width: a }, Self::Inline { worst_width: b }) => Self::Inline {
                worst_width: a.saturating_add(b),
            },
            (
                Self::BlockOrMixed {
                    pre_worst_width, ..
                },
                Self::BlockOrMixed {
                    post_worst_width, ..
                },
            ) => Self::BlockOrMixed {
                pre_worst_width,
                post_worst_width,
            },
            (
                Self::BlockOrMixed {
                    pre_worst_width,
                    post_worst_width: post_a,
                },
                Self::Inline {
                    worst_width: post_b,
                },
            ) => Self::BlockOrMixed {
                pre_worst_width,
                post_worst_width: post_a.saturating_add(post_b),
            },
            (
                Self::Inline { worst_width: pre_a },
                Self::BlockOrMixed {
                    pre_worst_width: pre_b,
                    post_worst_width,
                },
            ) => Self::BlockOrMixed {
                pre_worst_width: pre_a.saturating_add(pre_b),
                post_worst_width,
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

// FIXME(eddyb) make this configurable.
const INDENT: &str = "  ";

impl Node {
    /// Determine the "rigid" component of the `ApproxLayout` of this `Node`.
    ///
    /// That is, this accounts for the parts of the `Node` that don't depend on
    /// contextual sizing, i.e. `MaxWidths` (see also `approx_flex_layout`).
    fn approx_rigid_layout(&self) -> ApproxLayout {
        match self {
            Self::Text(text) => {
                if let Some((pre, non_pre)) = text.split_once('\n') {
                    let (_, post) = non_pre.rsplit_once('\n').unwrap_or(("", non_pre));

                    // FIXME(eddyb) use `unicode-width` crate for accurate column count.
                    let pre_width = pre.len();
                    let post_width = post.len();

                    ApproxLayout::BlockOrMixed {
                        pre_worst_width: pre_width,
                        post_worst_width: post_width,
                    }
                } else {
                    // FIXME(eddyb) use `unicode-width` crate for accurate column count.
                    let width = text.len();

                    ApproxLayout::Inline { worst_width: width }
                }
            }

            Self::IndentedBlock(_) => ApproxLayout::BlockOrMixed {
                pre_worst_width: 0,
                post_worst_width: 0,
            },

            Self::BreakingOnlySpace => ApproxLayout::Inline { worst_width: 1 },
            Self::ForceLineSeparation => ApproxLayout::BlockOrMixed {
                pre_worst_width: 0,
                post_worst_width: 0,
            },
            &Self::IfBlockLayout(text) => {
                // Keep the inline `worst_width`, just in case this node is
                // going to be used as part of an inline child of a block.
                // NOTE(eddyb) this is currently only the case for the trailing
                // comma added by `join_comma_sep`.
                let text_layout = Self::Text(text.into()).approx_rigid_layout();
                let worst_width = match text_layout {
                    ApproxLayout::Inline { worst_width } => worst_width,
                    ApproxLayout::BlockOrMixed { .. } => 0,
                };
                ApproxLayout::Inline { worst_width }
            }

            // Layout computed only in `approx_flex_layout`.
            Self::InlineOrIndentedBlock(_) => ApproxLayout::Inline { worst_width: 0 },
        }
    }

    /// Determine the "flexible" component of the `ApproxLayout` of this `Node`,
    /// potentially making adjustments in order to fit within `max_widths`.
    ///
    /// That is, this accounts for the parts of the `Node` that do depend on
    /// contextual sizing, i.e. `MaxWidths` (see also `approx_rigid_layout`).
    fn approx_flex_layout(&mut self, max_widths: MaxWidths) -> ApproxLayout {
        match self {
            Self::IndentedBlock(fragments) => {
                // Apply one more level of indentation to the block layout.
                let indented_block_max_width = max_widths.block.saturating_sub(INDENT.len());

                // Recurse on `fragments`, so they can compute their own layouts.
                for fragment in &mut fragments[..] {
                    fragment.approx_layout(MaxWidths {
                        inline: indented_block_max_width,
                        block: indented_block_max_width,
                    });
                }

                ApproxLayout::BlockOrMixed {
                    pre_worst_width: 0,
                    post_worst_width: 0,
                }
            }

            Self::InlineOrIndentedBlock(fragments) => {
                // Apply one more level of indentation to the block layout.
                let indented_block_max_width = max_widths.block.saturating_sub(INDENT.len());

                // Maximize the inline width available to `fragments`, usually
                // increasing it to the maximum allowed by the block layout.
                // However, block layout is only needed if the extra width is
                // actually used by `fragments` (i.e. staying within the original
                // `max_widths.inline` will keep inline layout).
                let inner_max_widths = MaxWidths {
                    inline: max_widths.inline.max(indented_block_max_width),
                    block: indented_block_max_width,
                };

                let mut layout = ApproxLayout::Inline { worst_width: 0 };
                for fragment in &mut fragments[..] {
                    // Offer the same `inner_max_widths` to each `fragment`.
                    // Worst case, they all remain inline and block layout is
                    // needed, but even then, `inner_max_widths` has limited each
                    // `fragment` to a maximum appropriate for that block layout.
                    layout = layout.append(fragment.approx_layout(inner_max_widths));
                }

                layout = match layout {
                    ApproxLayout::Inline { worst_width } if worst_width <= max_widths.inline => {
                        layout
                    }

                    // Even if `layout` is already `ApproxLayout::BlockOrMixed`,
                    // always reset it to a plain block, with no pre/post widths.
                    _ => ApproxLayout::BlockOrMixed {
                        pre_worst_width: 0,
                        post_worst_width: 0,
                    },
                };

                match layout {
                    ApproxLayout::Inline { .. } => {
                        // Leave `self` as `Node::InlineOrIndentedBlock` and
                        // have that be implied to be in inline layout.
                    }
                    ApproxLayout::BlockOrMixed { .. } => {
                        *self = Self::IndentedBlock(mem::take(fragments));
                    }
                }

                layout
            }

            // Layout computed only in `approx_rigid_layout`.
            Self::Text(_)
            | Self::BreakingOnlySpace
            | Self::ForceLineSeparation
            | Self::IfBlockLayout(_) => ApproxLayout::Inline { worst_width: 0 },
        }
    }
}

impl Fragment {
    /// Determine the `ApproxLayout` of this `Fragment`, potentially making
    /// adjustments in order to fit within `max_widths`.
    fn approx_layout(&mut self, max_widths: MaxWidths) -> ApproxLayout {
        let mut layout = ApproxLayout::Inline { worst_width: 0 };

        let child_max_widths = |layout| MaxWidths {
            inline: match layout {
                ApproxLayout::Inline { worst_width } => {
                    max_widths.inline.saturating_sub(worst_width)
                }
                ApproxLayout::BlockOrMixed {
                    post_worst_width, ..
                } => max_widths.block.saturating_sub(post_worst_width),
            },
            block: max_widths.block,
        };

        // Compute rigid `ApproxLayout`s as long as they remain inline, only
        // going back for flexible ones on block boundaries (and at the end),
        // ensuring that the `MaxWidths` are as contraining as possible.
        let mut next_flex_idx = 0;
        for rigid_idx in 0..self.nodes.len() {
            match self.nodes[rigid_idx].approx_rigid_layout() {
                rigid_layout @ ApproxLayout::Inline { .. } => {
                    layout = layout.append(rigid_layout);
                }
                ApproxLayout::BlockOrMixed {
                    pre_worst_width,
                    post_worst_width,
                } => {
                    // Split the `BlockOrMixed` just before the block, and
                    // process "recent" flexible nodes in between the halves.
                    layout = layout.append(ApproxLayout::Inline {
                        worst_width: pre_worst_width,
                    });
                    // FIXME(eddyb) what happens if the same node has both
                    // rigid and flexible `ApproxLayout`s?
                    while next_flex_idx <= rigid_idx {
                        layout = layout.append(
                            self.nodes[next_flex_idx].approx_flex_layout(child_max_widths(layout)),
                        );
                        next_flex_idx += 1;
                    }
                    layout = layout.append(ApproxLayout::BlockOrMixed {
                        pre_worst_width: 0,
                        post_worst_width,
                    });
                }
            }
        }

        // Process all remaining flexible nodes (i.e. after the last line split).
        for flex_idx in next_flex_idx..self.nodes.len() {
            layout =
                layout.append(self.nodes[flex_idx].approx_flex_layout(child_max_widths(layout)));
        }

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

impl Node {
    /// Flatten the `Fragment` to `LineOp`s, passed to `each_line_op`.
    fn render_to_line_ops(
        &self,
        each_line_op: &mut impl FnMut(LineOp<'_>),
        directly_in_block: bool,
    ) {
        match self {
            Self::Text(text) => {
                let mut lines = text.split('\n');
                each_line_op(LineOp::AppendToLine(lines.next().unwrap()));
                for line in lines {
                    each_line_op(LineOp::StartNewLine);
                    each_line_op(LineOp::AppendToLine(line));
                }
            }

            Self::IndentedBlock(fragments) => {
                each_line_op(LineOp::PushIndent);
                each_line_op(LineOp::BreakIfWithinLine(Break::NewLine));
                for fragment in fragments {
                    fragment.render_to_line_ops(each_line_op, true);
                    each_line_op(LineOp::BreakIfWithinLine(Break::NewLine));
                }
                each_line_op(LineOp::PopIndent);
            }
            // Post-layout, this is only used for the inline layout.
            Self::InlineOrIndentedBlock(fragments) => {
                for fragment in fragments {
                    fragment.render_to_line_ops(each_line_op, false);
                }
            }

            Self::BreakingOnlySpace => each_line_op(LineOp::BreakIfWithinLine(Break::Space)),
            Self::ForceLineSeparation => each_line_op(LineOp::BreakIfWithinLine(Break::NewLine)),
            &Self::IfBlockLayout(text) => {
                if directly_in_block {
                    Self::Text(text.into()).render_to_line_ops(each_line_op, true);
                }
            }
        }
    }
}

impl Fragment {
    /// Flatten the `Fragment` to `LineOp`s, passed to `each_line_op`.
    fn render_to_line_ops(
        &self,
        each_line_op: &mut impl FnMut(LineOp<'_>),
        directly_in_block: bool,
    ) {
        for node in &self.nodes {
            node.render_to_line_ops(each_line_op, directly_in_block);
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

/// Constructs the `Fragment` corresponding to one of:
/// * inline layout: `header + " " + contents.join(" ")`
/// * block layout: `header + "\n" + indent(contents).join("\n")`
pub fn join_space(
    header: impl Into<Node>,
    contents: impl IntoIterator<Item = impl Into<Fragment>>,
) -> Fragment {
    Fragment::new([
        header.into(),
        Node::InlineOrIndentedBlock(
            contents
                .into_iter()
                .map(|entry| {
                    Fragment::new(iter::once(Node::BreakingOnlySpace).chain(entry.into().nodes))
                })
                .collect(),
        ),
    ])
}

/// Constructs the `Fragment` corresponding to one of:
/// * inline layout: `prefix + contents.join(", ") + suffix`
/// * block layout: `prefix + "\n" + indent(contents).join(",\n") + ",\n" + suffix`
pub fn join_comma_sep(
    prefix: impl Into<Node>,
    contents: impl IntoIterator<Item = impl Into<Fragment>>,
    suffix: impl Into<Node>,
) -> Fragment {
    let mut children: Vec<_> = contents.into_iter().map(Into::into).collect();

    if let Some((last_child, non_last_children)) = children.split_last_mut() {
        for non_last_child in non_last_children {
            non_last_child
                .nodes
                .extend([",".into(), Node::BreakingOnlySpace]);
        }

        // Trailing comma is only needed after the very last element.
        last_child.nodes.push(Node::IfBlockLayout(","));
    }

    Fragment::new([
        prefix.into(),
        Node::InlineOrIndentedBlock(children),
        suffix.into(),
    ])
}
