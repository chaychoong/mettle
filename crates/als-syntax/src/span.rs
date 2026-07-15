//! Source locations. Every AST/IR node carries a [`Span`] from day one
//! (STYLE G1) and spans survive desugaring so diagnostics always point at the
//! original source (STYLE G2).

use crate::define_id;

define_id! {
    /// Identifies one source file (an `.als` module) within a compilation.
    ///
    /// The root module and everything reachable via `open` share one `FileId`
    /// space; the source map owning file contents is an `Arena<FileId, _>`
    /// built by the loader (Rung 1).
    pub struct FileId;
}

/// A byte range within a single source file.
///
/// `start`/`end` are byte offsets into the file's UTF-8 text, `start <= end`,
/// end-exclusive. Spans are `Copy` and deliberately small (12 bytes): every
/// node stores one.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct Span {
    /// File this span points into.
    pub file: FileId,
    /// Byte offset of the first covered byte.
    pub start: u32,
    /// Byte offset one past the last covered byte.
    pub end: u32,
}

impl Span {
    /// Creates a span, checking the internal ordering invariant.
    ///
    /// # Panics
    /// Panics if `start > end` — malformed spans are a lexer/parser bug, not
    /// a user error.
    #[must_use]
    pub fn new(file: FileId, start: u32, end: u32) -> Self {
        assert!(start <= end, "span start after end: {start}..{end}");
        Self { file, start, end }
    }

    /// The smallest span covering both `self` and `other`.
    ///
    /// # Panics
    /// Panics if the spans are in different files — merging across files is
    /// an internal invariant violation.
    #[must_use]
    pub fn merge(self, other: Span) -> Self {
        assert!(
            self.file == other.file,
            "span merge across files: {:?} vs {:?}",
            self.file,
            other.file
        );
        Self {
            file: self.file,
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ArenaId;

    #[test]
    fn merge_covers_both() {
        let file = FileId::from_index(0);
        let a = Span::new(file, 4, 9);
        let b = Span::new(file, 12, 20);
        assert_eq!(a.merge(b), Span::new(file, 4, 20));
        assert_eq!(b.merge(a), Span::new(file, 4, 20));
    }

    #[test]
    #[should_panic(expected = "span start after end")]
    fn rejects_inverted_span() {
        let _ = Span::new(FileId::from_index(0), 5, 3);
    }
}
