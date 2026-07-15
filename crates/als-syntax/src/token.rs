//! Token kinds and the spanned [`Token`] produced by [`crate::lexer::lex`].
//!
//! **Payload choice (STYLE N4, documented per mt-010's brief):** [`TokenKind::Ident`]
//! carries no text -- the parser slices it out of the source via the
//! token's [`Span`]. [`TokenKind::Str`] must own a `String` regardless
//! (escapes are unescaped at lex time, so the text no longer matches any
//! source byte range), which already makes `TokenKind` non-`Copy`; giving
//! `Ident` a span-only representation still avoids one `String` allocation
//! for every identifier occurrence -- by far the most common token kind in
//! any real model -- while string literals (rare) pay for their own
//! allocation. The parser and lexer always operate over the same `&str`
//! for one file, so slicing by span is always available where needed.

use crate::span::Span;

/// One lexical token: its kind plus the source range it was read from.
///
/// `span` is required (STYLE G1) even for [`TokenKind::Eof`], whose span is
/// empty and sits at the end of the file.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Token {
    /// What was lexed.
    pub kind: TokenKind,
    /// Where it was written.
    pub span: Span,
}

/// Every token the Alloy 6 lexer can produce (grammar-doc section 1).
///
/// Closed by design (`PORTING_RULES` R1): downstream matches should not
/// need a catch-all arm, so adding a token kind here is a compile-time
/// prompt to update every consumer.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum TokenKind {
    // -- Literals & names (section 1.4, 1.5, 1.6) ---------------------
    /// An identifier; text recovered from the token's span (see module doc).
    Ident,
    /// A number literal (decimal, hex, or binary), value already parsed and
    /// range-checked (always non-negative, section 1.5).
    Number(i32),
    /// A string literal, value already unescaped (section 1.6).
    Str(String),
    /// End of file: exactly one, always last, empty span.
    Eof,

    // -- Operators & punctuation (section 1.2) ------------------------
    /// `!` / `not`.
    Not,
    /// `#`.
    Hash,
    /// `&&` / `and`.
    And,
    /// `&`.
    Ampersand,
    /// `(`.
    LParen,
    /// `)`.
    RParen,
    /// `*`.
    Star,
    /// `++`.
    PlusPlus,
    /// `+`.
    Plus,
    /// `,`.
    Comma,
    /// `<<`.
    Shl,
    /// `=>` / `implies`.
    Implies,
    /// `>>>`.
    Shr,
    /// `>=`.
    Gte,
    /// `@`.
    At,
    /// `^`.
    Caret,
    /// `||` / `or`.
    Or,
    /// `~`.
    Tilde,
    /// `'`, U+2018 `'`, or U+2019 `'` -- three spellings, one token.
    Prime,
    /// `->`.
    Arrow,
    /// `-`.
    Minus,
    /// `.` or `::` -- `::` is an exact synonym.
    Dot,
    /// `/`.
    Slash,
    /// `:>`.
    RangeRestrict,
    /// `:`.
    Colon,
    /// `<=>` / `iff`.
    Iff,
    /// `<=` or `=<`.
    Lte,
    /// `<:`.
    DomRestrict,
    /// `<`.
    Lt,
    /// `=`. There is no `==` token.
    Equals,
    /// `>>`.
    Sha,
    /// `>`.
    Gt,
    /// `[`.
    LBracket,
    /// `]`.
    RBracket,
    /// `{`.
    LBrace,
    /// `}`.
    RBrace,
    /// `|`.
    Bar,
    /// `;`.
    Semi,

    // -- Keywords (section 1.3) ----------------------------------------
    // `and`/`or`/`iff`/`implies`/`not` are alternate spellings of the
    // operator tokens above per the grammar doc, not separate variants.
    /// `abstract`.
    Abstract,
    /// `all`.
    All,
    /// `as`.
    As,
    /// `assert`.
    Assert,
    /// `but`.
    But,
    /// `check`.
    Check,
    /// `disj`.
    Disj,
    /// `else`.
    Else,
    /// `enum`.
    Enum,
    /// `exactly`.
    Exactly,
    /// `expect`.
    Expect,
    /// `extends`.
    Extends,
    /// `fact`.
    Fact,
    /// `for`.
    For,
    /// `fun`.
    Fun,
    /// `iden`.
    Iden,
    /// `in`.
    In,
    /// `int` -- lowercase, the integer-cast keyword. Distinct from
    /// [`TokenKind::Int`] (`Int`, capitalized).
    IntCast,
    /// `Int` -- capitalized, the built-in bitwidth sig reference. Distinct
    /// from [`TokenKind::IntCast`] (`int`, lowercase).
    Int,
    /// `let`.
    Let,
    /// `lone`.
    Lone,
    /// `module`.
    Module,
    /// `none`.
    None,
    /// `no`.
    No,
    /// `one`.
    One,
    /// `open`.
    Open,
    /// `pred`.
    Pred,
    /// `private`.
    Private,
    /// `run`.
    Run,
    /// `seq`.
    Seq,
    /// `set`.
    Set,
    /// `sig`.
    Sig,
    /// `some`.
    Some,
    /// `steps`.
    Steps,
    /// `String` -- the built-in string-atom sig keyword. Distinct from the
    /// identifier `string` (not a keyword) and from
    /// [`TokenKind::Str`] (the string-*literal* token kind).
    StringKw,
    /// `sum`.
    Sum,
    /// `this`.
    This,
    /// `univ`.
    Univ,
    /// `var`.
    Var,
    /// `always`.
    Always,
    /// `after`.
    After,
    /// `before`.
    Before,
    /// `eventually`.
    Eventually,
    /// `historically`.
    Historically,
    /// `once`.
    Once,
    /// `releases`.
    Releases,
    /// `since`.
    Since,
    /// `triggered`.
    Triggered,
    /// `until`.
    Until,
}
