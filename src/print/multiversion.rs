//! Multi-version pretty-printing support (e.g. for comparing the IR between passes).

use crate::print::pretty;
use smallvec::SmallVec;
use std::fmt;
use std::fmt::Write;

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
        min-width: 100%;

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

        /* HACK(eddyb) force local scroll when table isn't wide enough. */
        max-width: 40ch;
    }
    SCOPE>tbody>tr>td>pre {
        overflow-x: auto;
    }
</style>
        "
                    .replace("SCOPE", &format!("table.{TABLE_CLASS_NAME}")),
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

                    html.body += "<tr>\n";
                    for (fragment, repeat_count) in versions_with_repeat_count {
                        writeln!(html.body, "<td colspan=\"{repeat_count}\">").unwrap();

                        let pretty::HtmlSnippet {
                            head_deduplicatable_elements: fragment_head,
                            body: fragment_body,
                        } = fragment.render_to_html();
                        html.head_deduplicatable_elements.extend(fragment_head);
                        html.body += &fragment_body;

                        html.body += "</td>\n";
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
