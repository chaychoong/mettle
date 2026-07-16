//! Caret-and-label diagnostic rendering for parse/lex/resolve errors (mt-013,
//! extended mt-019, STYLE G3). Lives ONLY in this CLI crate (STYLE E3):
//! `als-syntax`'s `LexError`/`ParseError` and `als-types`'s `ResolveError`/
//! `ResolveWarning` carry spans and a `Display` message but never render --
//! this module is the one place that turns a `(source, path, span, label,
//! message)` tuple into a rustc-style caret block:
//!
//! ```text
//! error: syntax error: expected a name
//!   --> path/to/model.als:12:8
//!    |
//! 12 | fact { some }
//!    |        ^^^^
//! ```
//!
//! `mettle check` (mt-019) reuses this same renderer for `warning:`-labeled
//! [`als_types::ResolveWarning`]s (never fatal) and, for the rare case where
//! no source text is recoverable for the offending file (a module-graph load
//! failure whose span points into a file mettle has no table for -- see
//! [`render_spanless`]), a location-free one-liner instead of a caret block.

use std::fmt::Write as _;

use als_syntax::Span;
use als_types::ResolveWarning;

/// A precomputed byte-offset index of line starts, so repeated line/column
/// lookups over one source file don't rescan from the beginning each time.
pub struct LineIndex {
    /// Byte offset of the start of line `i` (0-based). Always has at least
    /// one entry (`0`); gains one more per `\n` in the source, including a
    /// final entry for a trailing empty line when the source ends in `\n`.
    line_starts: Vec<u32>,
}

impl LineIndex {
    #[must_use]
    pub fn new(source: &str) -> Self {
        let mut line_starts = vec![0u32];
        for (i, b) in source.bytes().enumerate() {
            if b == b'\n' {
                // A real `.als` file never approaches `u32::MAX` bytes --
                // the same invariant `als_syntax::lex` already relies on
                // (it panics up front for an oversized source, so a `Span`
                // reaching this renderer is always in range).
                let Ok(start) = u32::try_from(i + 1) else {
                    panic!("source file exceeds u32 byte-offset range: {i} bytes");
                };
                line_starts.push(start);
            }
        }
        Self { line_starts }
    }

    /// 0-based index of the line containing byte offset `offset`. Clamps to
    /// the last line for an offset at (or, defensively, past) EOF, so an
    /// EOF span's one-past-the-end position never panics.
    fn line_of(&self, offset: u32) -> usize {
        match self.line_starts.binary_search(&offset) {
            Ok(i) => i,
            Err(i) => i.saturating_sub(1),
        }
    }

    /// 1-based `(line, column)` for `offset`, counting columns in Unicode
    /// scalar values from the start of that line -- never bytes, so this is
    /// UTF-8-safe and never slices mid-codepoint.
    #[must_use]
    pub fn line_col(&self, source: &str, offset: u32) -> (usize, usize) {
        let line0 = self.line_of(offset);
        let start = self.line_starts[line0];
        let col = source[start as usize..offset as usize].chars().count() + 1;
        (line0 + 1, col)
    }

    /// The text of 0-based line `line0`, excluding its terminating `\n`
    /// (and a trailing `\r`, for CRLF sources).
    fn line_text<'s>(&self, source: &'s str, line0: usize) -> &'s str {
        let start = self.line_starts[line0] as usize;
        let end = self
            .line_starts
            .get(line0 + 1)
            .map_or(source.len(), |&s| s as usize - 1); // -1 drops the '\n'
        let raw = &source[start..end];
        raw.strip_suffix('\r').unwrap_or(raw)
    }
}

/// Renders one caret-and-label diagnostic block (trailing newline
/// included), labeled `error:`. `path` is display-only; `span`/`message`
/// come straight from a [`als_syntax::LexError`]/[`als_syntax::ParseError`]/
/// [`als_types::ResolveError`].
#[must_use]
pub fn render(source: &str, path: &str, span: Span, message: &str) -> String {
    render_label(source, path, span, "error", message)
}

/// Like [`render`], but with the severity label parameterized so `mettle
/// check` (mt-019) can share this one renderer for non-fatal
/// [`ResolveWarning`]s (`label = "warning"`) instead of hardcoding `error:`.
#[must_use]
pub fn render_label(source: &str, path: &str, span: Span, label: &str, message: &str) -> String {
    let index = LineIndex::new(source);
    render_with_index(&index, source, path, span, label, message)
}

fn render_with_index(
    index: &LineIndex,
    source: &str,
    path: &str,
    span: Span,
    label: &str,
    message: &str,
) -> String {
    let (line1, col1) = index.line_col(source, span.start);
    // The last byte actually covered by the (end-exclusive) span, so a span
    // whose `end` lands exactly at the next line's start is attributed to
    // the line it covers, not the empty one after it. An empty span has no
    // covered byte at all and stays put on its start line.
    let last_included = if span.end > span.start {
        span.end - 1
    } else {
        span.start
    };
    let last_line = index.line_col(source, last_included).0;

    let gutter_width = line1.max(last_line).to_string().len();
    let blank_gutter = " ".repeat(gutter_width);

    let line0 = line1 - 1;
    let line_text = index.line_text(source, line0);
    let line_start_byte = index.line_starts[line0] as usize;
    // Safe: `span.start` sits on a char boundary (lexer/parser invariant),
    // and is within this line by construction of `line_col` above.
    let prefix_byte_len = (span.start as usize - line_start_byte).min(line_text.len());
    let prefix = &line_text[..prefix_byte_len];

    // The standard trick for tab-proof caret alignment: the padding line
    // copies the source line's prefix verbatim except every non-tab char
    // becomes a space, so a tab in the padding expands identically to the
    // tab above it under any terminal tab width.
    let caret_pad: String = prefix
        .chars()
        .map(|c| if c == '\t' { '\t' } else { ' ' })
        .collect();

    let spans_one_line = last_line == line1;
    let caret_len = if spans_one_line {
        let end_col = index.line_col(source, span.end).1;
        end_col.saturating_sub(col1).max(1)
    } else {
        // Multi-line span: caret out to the end of the first displayed
        // line only; a trailing note says where the rest of the span is.
        line_text.chars().count().saturating_sub(col1 - 1).max(1)
    };
    let carets = "^".repeat(caret_len);

    let mut out = String::new();
    let _ = writeln!(out, "{label}: {message}");
    let _ = writeln!(out, "{blank_gutter}--> {path}:{line1}:{col1}");
    let _ = writeln!(out, "{blank_gutter} |");
    let _ = writeln!(out, "{line1:>gutter_width$} | {line_text}");
    let _ = writeln!(out, "{blank_gutter} | {caret_pad}{carets}");
    if !spans_one_line {
        let (end_line, end_col) = index.line_col(source, span.end);
        let _ = writeln!(
            out,
            "{blank_gutter} = note: span continues to line {end_line}, column {end_col}"
        );
    }
    out
}

/// Renders a diagnostic with no caret, for the rare case where mettle has
/// no source text to point into: a module-graph load failure (mt-019)
/// whose [`als_syntax::Span`] names a `FileId` that isn't the root and was
/// never returned to the caller (the graph the resolver would have used it
/// against doesn't exist yet -- see `crates/mettle/src/main.rs`'s
/// `render_load_error`). `path`, if known, is shown for context without a
/// line/column (none is trustworthy here). Trailing newline included, like
/// [`render`].
#[must_use]
pub fn render_spanless(label: &str, path: Option<&str>, message: &str) -> String {
    match path {
        Some(path) => format!("{label}: {message}\n  --> {path}\n"),
        None => format!("{label}: {message}\n"),
    }
}

/// The human-facing message for a [`ResolveWarning`] (mt-019). Warnings
/// have no `Display`/`thiserror` impl in `als-types` (they're not errors);
/// this is the CLI-only text mapping, the warning-side counterpart of
/// `ResolveError`'s `#[error(...)]` messages.
#[must_use]
pub fn warning_message(warning: &ResolveWarning) -> String {
    match warning {
        ResolveWarning::UnusedVariable { name, .. } => {
            format!("variable `{name}` is never used")
        }
        ResolveWarning::ClosureRedundant { .. } => {
            "this transitive closure (`^`) is redundant: its domain and range are disjoint"
                .to_owned()
        }
        ResolveWarning::DoesNotContribute { .. } => {
            "this expression does not contribute to the value of the parent".to_owned()
        }
        ResolveWarning::IntAtoms { .. } => "this expression should contain `Int` atoms".to_owned(),
        ResolveWarning::EqRedundant { .. } => {
            "this comparison is redundant: the two sides are always disjoint or always equal"
                .to_owned()
        }
        ResolveWarning::SubsetRedundant { .. } => {
            "this subset test is redundant: a side is always empty, disjoint, or equal".to_owned()
        }
        ResolveWarning::IntersectIrrelevant { .. } => {
            "this intersection (`&`) is always empty; its operands are disjoint".to_owned()
        }
        ResolveWarning::PlusIrrelevant { .. } => {
            "this union is irrelevant: a subexpression does not contribute".to_owned()
        }
        ResolveWarning::MinusIrrelevant { .. } => {
            "this difference (`-`) is irrelevant: the right subexpression is redundant".to_owned()
        }
        ResolveWarning::JoinEmpty { .. } => "this join always yields the empty set".to_owned(),
        ResolveWarning::DomainIrrelevant { .. } => {
            "this domain restriction (`<:`) is always empty".to_owned()
        }
        ResolveWarning::RangeIrrelevant { .. } => {
            "this range restriction (`:>`) is always empty".to_owned()
        }
        ResolveWarning::ArrowIrrelevant { .. } => {
            "this product (`->`) is irrelevant: one side is always empty".to_owned()
        }
        ResolveWarning::RedundantIteBranch { .. } => "this subexpression is redundant".to_owned(),
        ResolveWarning::ImplicitConjunction { .. } => {
            "implicit conjunction between two formulas on the same line".to_owned()
        }
        ResolveWarning::SigStaticVarParent { .. } => {
            "this static sig has a variable parent".to_owned()
        }
        ResolveWarning::SigRedundantVar { .. } => {
            "marking this sig `var` is redundant: its parent is static".to_owned()
        }
        ResolveWarning::FieldStaticVarBound { .. } => {
            "this static field's bound references a variable sig".to_owned()
        }
        ResolveWarning::FieldStaticInVarSig { .. } => {
            "this static field is inside a variable sig".to_owned()
        }
        ResolveWarning::ReturnDisjoint { .. } => {
            "function body's type is disjoint from its declared return type".to_owned()
        }
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::cast_possible_truncation)]
mod tests {
    use super::*;
    use als_syntax::{ArenaId as _, FileId};

    fn span(file: FileId, start: u32, end: u32) -> Span {
        Span::new(file, start, end)
    }

    #[test]
    fn single_line_span_points_at_the_word() {
        let file = FileId::from_index(0);
        let source = "fact { some }\n";
        // "some" starts at byte 7, ends at byte 11.
        let out = render(source, "model.als", span(file, 7, 11), "expected a name");
        assert_eq!(
            out,
            "error: expected a name\n\
             \x20--> model.als:1:8\n\
             \x20\x20|\n\
             1 | fact { some }\n\
             \x20\x20|        ^^^^\n"
        );
    }

    #[test]
    fn empty_span_renders_a_single_caret() {
        let file = FileId::from_index(0);
        let source = "sig {}\n";
        let out = render(source, "m.als", span(file, 4, 4), "expected a name");
        assert!(out.contains("m.als:1:5"));
        // The caret line has exactly one `^`, immediately after the gutter.
        let caret_line = out.lines().nth(4).unwrap();
        assert_eq!(caret_line, "  |     ^");
    }

    #[test]
    fn multi_line_span_shows_first_line_and_a_continuation_note() {
        let file = FileId::from_index(0);
        // A block whose `{` opens on line 1 and never closes before EOF (no
        // trailing newline, so EOF sits at the end of line 2, not a phantom
        // line 3).
        let source = "pred p {\n  some x";
        let start = source.find('{').unwrap() as u32;
        let end = source.len() as u32;
        let out = render(
            source,
            "m.als",
            span(file, start, end),
            "unterminated block",
        );
        let lines: Vec<&str> = out.lines().collect();
        assert_eq!(lines[0], "error: unterminated block");
        assert_eq!(lines[1], " --> m.als:1:8");
        assert_eq!(lines[3], "1 | pred p {");
        // Caret runs from column 8 to the end of line 1's displayed text.
        assert_eq!(lines[4], "  |        ^");
        assert!(lines[5].contains("note: span continues to line 2, column 9"));
    }

    #[test]
    fn tabs_align_caret_via_matching_tab_prefix() {
        let file = FileId::from_index(0);
        // A tab, then "bad" at byte offset 1.
        let source = "\tbad\n";
        let out = render(source, "m.als", span(file, 1, 4), "bad token");
        let lines: Vec<&str> = out.lines().collect();
        // The source line keeps the raw tab; the caret line's padding is a
        // tab too (not spaces), so both expand identically under any tab
        // width and the carets land under "bad" regardless.
        assert_eq!(lines[3], "1 | \tbad");
        assert_eq!(lines[4], "  | \t^^^");
    }

    #[test]
    fn eof_span_points_one_past_the_last_character() {
        let file = FileId::from_index(0);
        let source = "sig Foo"; // no trailing newline
        let end = source.len() as u32;
        let out = render(source, "m.als", span(file, end, end), "expected `{`");
        assert!(out.contains("m.als:1:8"));
        let lines: Vec<&str> = out.lines().collect();
        assert_eq!(lines[3], "1 | sig Foo");
        // Column 8 is one past the 7-character line -- a single caret at
        // the end, never an out-of-bounds slice.
        assert_eq!(lines[4], "  |        ^");
    }

    #[test]
    fn multibyte_line_uses_char_columns_not_byte_offsets() {
        let file = FileId::from_index(0);
        // "café" is 5 bytes (é is 2 bytes) but 4 chars; the bad token
        // "bad" starts right after, at byte offset 6 / char column 5.
        let source = "café bad\n";
        let start = source.find("bad").unwrap() as u32;
        let end = start + 3;
        let out = render(source, "m.als", span(file, start, end), "expected a name");
        assert!(out.contains("m.als:1:6"));
        let lines: Vec<&str> = out.lines().collect();
        assert_eq!(lines[3], "1 | café bad");
        // 5 leading spaces (char columns 1-5 = "café "), then 3 carets.
        assert_eq!(lines[4], "  |      ^^^");
    }

    #[test]
    fn gutter_width_matches_the_widest_printed_line_number() {
        let file = FileId::from_index(0);
        let source = format!("{}bad\n", "\n".repeat(9)); // "bad" starts on line 10
        let start = source.find("bad").unwrap() as u32;
        let out = render(&source, "m.als", span(file, start, start + 3), "oops");
        let lines: Vec<&str> = out.lines().collect();
        // Two-digit gutter: "--> " is indented by 2 spaces, "|" rows by 3.
        assert_eq!(lines[1], "  --> m.als:10:1");
        assert_eq!(lines[2], "   |");
        assert_eq!(lines[3], "10 | bad");
        assert_eq!(lines[4], "   | ^^^");
    }
}
