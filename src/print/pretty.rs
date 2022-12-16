//! Pretty-printing functionality (such as automatic indentation).

use indexmap::IndexSet;
use smallvec::SmallVec;
use std::borrow::Cow;
use std::fmt::Write as _;
use std::{fmt, iter, mem};

/// Part of a pretty document, made up of [`Node`]s.
//
// FIXME(eddyb) `Document` might be too long, what about renaming this to `Doc`?
#[derive(Clone, Default, PartialEq)]
pub struct Fragment {
    pub nodes: SmallVec<[Node; 8]>,
}

#[derive(Clone, PartialEq)]
pub enum Node {
    Text(Cow<'static, str>),

    // FIXME(eddyb) should this contain a `Node` instead of being text-only?
    StyledText(Box<(Styles, Cow<'static, str>)>),

    /// Container for [`Fragment`]s, using block layout (indented on separate lines).
    IndentedBlock(Vec<Fragment>),

    /// Container for [`Fragment`]s, either using inline layout (all on one line)
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

#[derive(Clone, Default, PartialEq)]
pub struct Styles {
    pub anchor: Option<String>,
    pub anchor_is_def: bool,

    /// RGB color.
    pub color: Option<[u8; 3]>,

    /// `0.0` is fully transparent, `1.0` is fully opaque.
    //
    // FIXME(eddyb) move this into `color` (which would become RGBA).
    pub color_opacity: Option<f32>,

    /// `0` corresponds to the default, with positive values meaning thicker,
    /// and negative values thinner text, respectively.
    ///
    /// For HTML output, each unit is equivalent to `±100` in CSS `font-weight`.
    pub thickness: Option<i8>,

    pub subscript: bool,
    pub superscript: bool,
}

impl Styles {
    pub fn color(color: [u8; 3]) -> Self {
        Self {
            color: Some(color),
            ..Self::default()
        }
    }

    pub fn apply(self, text: impl Into<Cow<'static, str>>) -> Node {
        Node::StyledText(Box::new((self, text.into())))
    }
}

/// Color palettes built-in for convenience (colors are RGB, as `[u8; 3]`).
pub mod palettes {
    /// Minimalist palette, chosen to work with both light and dark backgrounds.
    pub mod simple {
        pub const DARK_GRAY: [u8; 3] = [0x44, 0x44, 0x44];
        pub const RED: [u8; 3] = [0xcc, 0x55, 0x55];
        pub const GREEN: [u8; 3] = [0x44, 0x99, 0x44];
        pub const BLUE: [u8; 3] = [0x44, 0x66, 0xcc];
        pub const YELLOW: [u8; 3] = [0xcc, 0x99, 0x44];
        pub const MAGENTA: [u8; 3] = [0xcc, 0x44, 0xcc];
        pub const CYAN: [u8; 3] = [0x44, 0x99, 0xcc];
    }
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

    /// Perform layout on the [`Fragment`], limiting lines to `max_line_width`
    /// columns where possible.
    pub fn layout_with_max_line_width(mut self, max_line_width: usize) -> FragmentPostLayout {
        self.approx_layout(MaxWidths {
            inline: max_line_width,
            block: max_line_width,
        });
        FragmentPostLayout(self)
    }
}

// HACK(eddyb) simple wrapper to avoid misuse externally.
pub struct FragmentPostLayout(Fragment);

impl fmt::Display for FragmentPostLayout {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut result = Ok(());
        self.0.render_to_line_ops(
            &mut LineOp::interpret_with(|op| {
                if let TextOp::Text(text) = op {
                    result = result.and_then(|_| f.write_str(text));
                }
            }),
            false,
        );
        result
    }
}

#[derive(Default)]
pub struct HtmlSnippet {
    pub head_deduplicatable_elements: IndexSet<String>,
    pub body: String,
}

impl HtmlSnippet {
    /// Inject (using JavaScript) the ability to use `?dark` to choose a simple
    /// "dark mode" (only different default background and foreground colors),
    /// auto-detection using media queries, and `?light` to force-disable it.
    pub fn with_dark_mode_support(&mut self) -> &mut Self {
        self.head_deduplicatable_elements.insert(
            r#"
<script>
    (function() {
        var params = new URLSearchParams(document.location.search);
        var dark = params.has("dark"), light = params.has("light");
        if(dark || light) {
            if(dark && !light)
                document.documentElement.classList.add("simple-dark-theme");
        } else if(matchMedia("(prefers-color-scheme: dark)").matches) {
            // FIXME(eddyb) also use media queries in CSS directly, to ensure dark mode
            // still works with JS disabled (sadly that likely requires CSS duplication).
            document.location.search += (document.location.search ? "&" : "?") + "dark";
        }
    })();
</script>

<style>
    /* HACK(eddyb) `[data-darkreader-scheme="dark"]` is for detecting Dark Reader,
      as its own automatic detection of websites with built-in dark themes
      (https://github.com/darkreader/darkreader/pull/7995) isn't on by default,
      and the result is jarring when both dark modes combine. */

    html.simple-dark-theme:not([data-darkreader-scheme="dark"]) {
        background: #16181a;
        color: #dbd8d6;

        /* Request browser UI elements to be dark-themed if possible. */
        color-scheme: dark;
    }
</style>
        "#
            .into(),
        );
        self
    }

    /// Combine `head` and `body` into a complete HTML document, which starts
    /// with `<!doctype html>`. Ideal for writing out a whole `.html` file.
    //
    // FIXME(eddyb) provide a non-allocating version.
    pub fn to_html_doc(&self) -> String {
        let mut html = String::new();
        html += "<!doctype html>\n";
        html += "<html>\n";

        html += "<head>\n";
        html += "<meta charset=\"utf-8\">\n";
        for elem in &self.head_deduplicatable_elements {
            html += elem;
            html += "\n";
        }
        html += "</head>\n";

        html += "<body>";
        html += &self.body;
        html += "</body>\n";

        html += "</html>\n";

        html
    }
}

impl FragmentPostLayout {
    /// Flatten the [`Fragment`] to HTML, producing a [`HtmlSnippet`].
    //
    // FIXME(eddyb) provide a non-allocating version.
    pub fn render_to_html(&self) -> HtmlSnippet {
        // HACK(eddyb) using an UUID as a class name in lieu of "scoped <style>".
        const ROOT_CLASS_NAME: &str = "spirt-90c2056d-5b38-4644-824a-b4be1c82f14d";

        // FIXME(eddyb) consider interning styles into CSS classes, to avoid
        // using inline `style="..."` attributes.
        let style_elem = "
<style>
    SCOPE {
        /* HACK(eddyb) reset default margin to something reasonable. */
        margin: 1ch;

        /* HACK(eddyb) avoid unnecessarily small or thin text. */
        font-size: 15px;
        font-weight: 500;
    }
    SCOPE a {
        color: unset;
        font-weight: 900;
    }
    SCOPE a:not(:hover) {
        text-decoration: unset;
    }
</style>
"
        .replace("SCOPE", &format!("pre.{ROOT_CLASS_NAME}"));

        let mut body = format!("<pre class=\"{ROOT_CLASS_NAME}\">");
        self.0.render_to_line_ops(
            &mut LineOp::interpret_with(|op| match op {
                TextOp::PushStyles(styles) | TextOp::PopStyles(styles) => {
                    let mut special_tags = [
                        ("a", styles.anchor.is_some()),
                        ("sub", styles.subscript),
                        ("super", styles.superscript),
                    ]
                    .into_iter()
                    .filter(|&(_, cond)| cond)
                    .map(|(tag, _)| tag);
                    let tag = special_tags.next().unwrap_or("span");
                    if let Some(other_tag) = special_tags.next() {
                        // FIXME(eddyb) support by opening/closing multiple tags.
                        panic!("`<{tag}>` conflicts with `<{other_tag}>`");
                    }

                    body += "<";
                    if let TextOp::PopStyles(_) = op {
                        body += "/";
                    }
                    body += tag;

                    if let TextOp::PushStyles(_) = op {
                        let mut push_attr = |attr, value: &str| {
                            // Quick sanity check.
                            assert!(value.chars().all(|c| !(c == '"' || c == '&')));

                            body.extend([" ", attr, "=\"", value, "\""]);
                        };

                        let Styles {
                            ref anchor,
                            anchor_is_def,
                            color,
                            color_opacity,
                            thickness,
                            subscript: _,
                            superscript: _,
                        } = *styles;

                        if let Some(id) = anchor {
                            if anchor_is_def {
                                push_attr("id", id);
                            }
                            push_attr("href", &format!("#{id}"));
                        }

                        let mut css_style = String::new();

                        if let Some(a) = color_opacity {
                            let [r, g, b] = color.expect("color_opacity without color");
                            write!(css_style, "color:rgba({r},{g},{b},{a});").unwrap();
                        } else if let Some([r, g, b]) = color {
                            write!(css_style, "color:#{r:02x}{g:02x}{b:02x};").unwrap();
                        }
                        if let Some(thickness) = thickness {
                            write!(css_style, "font-weight:{};", 500 + (thickness as i32) * 100)
                                .unwrap();
                        }
                        if !css_style.is_empty() {
                            push_attr("style", &css_style);
                        }
                    }

                    body += ">";
                }
                TextOp::Text(text) => {
                    // Minimal escaping, just enough to produce valid HTML.
                    let escape_from = ['&', '<'];
                    let escape_to = ["&amp;", "&lt;"];
                    for piece in text.split_inclusive(escape_from) {
                        let mut chars = piece.chars();
                        let maybe_needs_escape = chars.next_back();
                        body += chars.as_str();

                        if let Some(maybe_needs_escape) = maybe_needs_escape {
                            match escape_from.iter().position(|&c| maybe_needs_escape == c) {
                                Some(escape_idx) => body += escape_to[escape_idx],
                                None => body.push(maybe_needs_escape),
                            }
                        }
                    }
                }
            }),
            false,
        );
        body += "</pre>";

        HtmlSnippet {
            head_deduplicatable_elements: [style_elem].into_iter().collect(),
            body,
        }
    }
}

// Rendering implementation details (including approximate layout).

/// The approximate shape of a [`Node`], regarding its 2D placement.
#[derive(Copy, Clone)]
enum ApproxLayout {
    /// Only occupies part of a line, (at most) `worst_width` columns wide.
    ///
    /// `worst_width` can exceed the `inline` field of [`MaxWidths`], in which
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

/// Maximum numbers of columns, available to a [`Node`], for both inline layout
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
    /// Determine the "rigid" component of the [`ApproxLayout`] of this [`Node`].
    ///
    /// That is, this accounts for the parts of the [`Node`] that don't depend on
    /// contextual sizing, i.e. [`MaxWidths`] (see also `approx_flex_layout`).
    fn approx_rigid_layout(&self) -> ApproxLayout {
        // HACK(eddyb) workaround for the `Self::StyledText` arm not being able
        // to destructure through the `Box<(_, Cow<str>)>`.
        let text_approx_rigid_layout = |text: &str| {
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
        };

        #[allow(clippy::match_same_arms)]
        match self {
            Self::Text(text) => text_approx_rigid_layout(text),
            Self::StyledText(styles_and_text) => text_approx_rigid_layout(&styles_and_text.1),

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

    /// Determine the "flexible" component of the [`ApproxLayout`] of this [`Node`],
    /// potentially making adjustments in order to fit within `max_widths`.
    ///
    /// That is, this accounts for the parts of the [`Node`] that do depend on
    /// contextual sizing, i.e. [`MaxWidths`] (see also `approx_rigid_layout`).
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
            | Self::StyledText(_)
            | Self::BreakingOnlySpace
            | Self::ForceLineSeparation
            | Self::IfBlockLayout(_) => ApproxLayout::Inline { worst_width: 0 },
        }
    }
}

impl Fragment {
    /// Determine the [`ApproxLayout`] of this [`Fragment`], potentially making
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
/// and instead [`LineOp`]s are (statefully) transformed into [`TextOp`]s on the fly
/// (see [`LineOp::interpret_with`]).
#[derive(Copy, Clone)]
enum LineOp<'a> {
    PushIndent,
    PopIndent,
    PushStyles(&'a Styles),
    PopStyles(&'a Styles),

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
    /// Flatten the [`Node`] to [`LineOp`]s, passed to `each_line_op`.
    fn render_to_line_ops<'a>(
        &'a self,
        each_line_op: &mut impl FnMut(LineOp<'a>),
        directly_in_block: bool,
    ) {
        // HACK(eddyb) workaround for the `Self::StyledText` arm not being able
        // to destructure through the `Box<(_, Cow<str>)>`.
        let mut text_render_to_line_ops = |styles: Option<&'a Styles>, text: &'a str| {
            if let Some(styles) = styles {
                each_line_op(LineOp::PushStyles(styles));
            }
            let mut lines = text.split('\n');
            each_line_op(LineOp::AppendToLine(lines.next().unwrap()));
            for line in lines {
                each_line_op(LineOp::StartNewLine);
                each_line_op(LineOp::AppendToLine(line));
            }
            if let Some(styles) = styles {
                each_line_op(LineOp::PopStyles(styles));
            }
        };
        match self {
            Self::Text(text) => {
                text_render_to_line_ops(None, text);
            }
            Self::StyledText(styles_and_text) => {
                text_render_to_line_ops(Some(&styles_and_text.0), &styles_and_text.1);
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
                    text_render_to_line_ops(None, text);
                }
            }
        }
    }
}

impl Fragment {
    /// Flatten the [`Fragment`] to [`LineOp`]s, passed to `each_line_op`.
    fn render_to_line_ops<'a>(
        &'a self,
        each_line_op: &mut impl FnMut(LineOp<'a>),
        directly_in_block: bool,
    ) {
        for node in &self.nodes {
            node.render_to_line_ops(each_line_op, directly_in_block);
        }
    }
}

/// Text-oriented operation (plain text snippets interleaved with style push/pop).
enum TextOp<'a> {
    PushStyles(&'a Styles),
    PopStyles(&'a Styles),

    Text(&'a str),
}

impl<'a> LineOp<'a> {
    /// Expand [`LineOp`]s passed to the returned `impl FnMut(LineOp<'a>)` closure,
    /// forwarding the expanded [`TextOp`]s to `each_text_op`.
    //
    // FIXME(eddyb) this'd be nicer if instead of returning a closure, it could
    // be passed to an `impl for<F: FnMut(LineOp<'a>)> FnOnce(F)` callback.
    fn interpret_with(mut each_text_op: impl FnMut(TextOp<'a>)) -> impl FnMut(LineOp<'a>) {
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

            if let LineOp::AppendToLine(_) | LineOp::PushStyles(_) = op {
                let need_indent = match pending_break_if_within_line.take() {
                    Some(br) => {
                        each_text_op(TextOp::Text(match br {
                            Break::Space => " ",
                            Break::NewLine => "\n",
                        }));
                        matches!(br, Break::NewLine)
                    }
                    None => on_empty_new_line,
                };
                if need_indent {
                    for _ in 0..indent {
                        each_text_op(TextOp::Text(INDENT));
                    }
                    on_empty_new_line = false;
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

                LineOp::PushStyles(styles) => each_text_op(TextOp::PushStyles(styles)),
                LineOp::PopStyles(styles) => each_text_op(TextOp::PopStyles(styles)),

                LineOp::AppendToLine(text) => each_text_op(TextOp::Text(text)),

                LineOp::StartNewLine => {
                    each_text_op(TextOp::Text("\n"));

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

/// Constructs the [`Fragment`] corresponding to one of:
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

/// Constructs the [`Fragment`] corresponding to one of:
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
