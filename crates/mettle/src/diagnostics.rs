//! Caret-and-label diagnostic rendering for parse/lex errors (mt-013,
//! STYLE G3). Lives ONLY in this CLI crate (STYLE E3): `als-syntax`'s
//! `LexError`/`ParseError` carry spans and a `Display` message but never
//! render -- this module is the one place that turns a
//! `(source, path, span, message)` tuple into a rustc-style caret block:
//!
//! ```text
//! error: syntax error: expected a name
//!   --> path/to/model.als:12:8
//!    |
//! 12 | fact { some }
//!    |        ^^^^
//! ```

use std::fmt::Write as _;

use als_syntax::Span;

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
/// included). `path` is display-only; `span`/`message` come straight from
/// a [`als_syntax::LexError`]/[`als_syntax::ParseError`].
#[must_use]
pub fn render(source: &str, path: &str, span: Span, message: &str) -> String {
    let index = LineIndex::new(source);
    render_with_index(&index, source, path, span, message)
}

fn render_with_index(
    index: &LineIndex,
    source: &str,
    path: &str,
    span: Span,
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
    let _ = writeln!(out, "error: {message}");
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
