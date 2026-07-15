//! Hand-written lexer for Alloy 6 surface syntax.
//!
//! Implements grammar-doc section 1 exactly; section 2 (the `CompFilter`
//! token-stream rewrites) is out of scope here -- it is a separate cooking
//! pass over this lexer's output (ADR-0007), owned by the parser bead.
//!
//! Errors are values, not a `TokenKind::Error` variant (ADR-0007): [`lex`]
//! fails fast and returns the first [`LexError`] encountered, matching
//! Rung 1's error strategy.

use thiserror::Error;

use crate::span::{FileId, Span};
use crate::token::{Token, TokenKind};

/// Lex-time failures (grammar-doc section 1). Each variant carries the
/// [`Span`] of the offending literal/character -- the malformed token
/// itself, not the token before it (STYLE G3: enough context for a caret
/// render later).
#[derive(Clone, PartialEq, Eq, Debug, Error)]
pub enum LexError {
    /// `/* ...` with no matching `*/` before EOF (section 1.1).
    #[error("unterminated block comment")]
    UnterminatedComment {
        /// Span from the opening `/*` to EOF.
        span: Span,
    },
    /// `"...` with no closing `"` before a raw newline or EOF (section 1.6:
    /// strings are single-line).
    #[error("unterminated string literal")]
    UnterminatedString {
        /// Span from the opening `"` to where the string was cut off.
        span: Span,
    },
    /// `""` -- the empty string is explicitly rejected (section 1.6).
    #[error("empty string literal is not allowed")]
    EmptyString {
        /// Span of the `""` pair.
        span: Span,
    },
    /// A `\` in a string followed by anything other than `\`, `n`, or `"`.
    #[error("invalid escape sequence in string literal")]
    BadEscape {
        /// Span of the string literal containing the bad escape.
        span: Span,
    },
    /// A string literal's closing `"` is immediately followed by an
    /// identifier-start character (section 1.6).
    #[error("string literal immediately followed by an identifier character")]
    StringFollowedByIdent {
        /// Span of the string literal.
        span: Span,
    },
    /// A maximal identifier-continue run starting with a digit is not
    /// exactly one valid number literal (`3x`, `1_000`, `0x123`, `0b12`;
    /// section 1.5) -- never two adjacent tokens.
    #[error("name cannot start with a number")]
    NumberStartsName {
        /// Span of the whole offending run.
        span: Span,
    },
    /// A number literal's value does not fit in a non-negative `i32`
    /// (section 1.5).
    #[error("number literal out of range for a 32-bit integer")]
    NumberOverflow {
        /// Span of the number literal.
        span: Span,
    },
    /// A byte that starts none of the recognized tokens.
    #[error("unrecognized character {ch:?}")]
    StrayChar {
        /// Span of the single offending character.
        span: Span,
        /// The character itself, for the diagnostic message.
        ch: char,
    },
}

impl LexError {
    /// The span every variant carries, regardless of kind -- convenience
    /// for callers that just need "where" (e.g. a caret render) without
    /// matching on the specific failure.
    #[must_use]
    pub fn span(&self) -> Span {
        match self {
            Self::UnterminatedComment { span }
            | Self::UnterminatedString { span }
            | Self::EmptyString { span }
            | Self::BadEscape { span }
            | Self::StringFollowedByIdent { span }
            | Self::NumberStartsName { span }
            | Self::NumberOverflow { span }
            | Self::StrayChar { span, .. } => *span,
        }
    }
}

/// Lexes `source` (one file's text) into a flat token stream, ending with
/// exactly one [`TokenKind::Eof`].
///
/// # Errors
/// Returns the first [`LexError`] encountered; Rung 1 does not attempt
/// error recovery (ADR-0007 section 3).
///
/// # Panics
/// Panics if `source` is larger than `u32::MAX` bytes -- spans are
/// deliberately `u32`-based (STYLE, `span.rs`), and no real `.als` file
/// approaches that size.
pub fn lex(source: &str, file: FileId) -> Result<Vec<Token>, LexError> {
    let mut lexer = Lexer::new(source, file);
    let mut tokens = Vec::new();
    loop {
        lexer.skip_trivia()?;
        let start = lexer.pos();
        let Some(c) = lexer.peek(0) else {
            tokens.push(Token {
                kind: TokenKind::Eof,
                span: Span::new(file, start, start),
            });
            break;
        };
        tokens.push(lexer.lex_token(c, start)?);
    }
    Ok(tokens)
}

/// Cursor over `source`'s characters with fixed byte offsets, so
/// multi-lookahead (needed for `>>>` vs `>>` vs `>`, etc.) is plain
/// indexing rather than a hand-rolled multi-char peek buffer.
struct Lexer<'src> {
    source: &'src str,
    file: FileId,
    chars: Vec<(u32, char)>,
    idx: usize,
    /// Byte offset one past the end of `source` -- the `Eof` position.
    end: u32,
}

impl<'src> Lexer<'src> {
    fn new(source: &'src str, file: FileId) -> Self {
        let mut chars = Vec::new();
        for (byte_offset, c) in source.char_indices() {
            let Ok(offset) = u32::try_from(byte_offset) else {
                panic!(
                    "source file exceeds u32 byte-offset range: {} bytes",
                    source.len()
                );
            };
            chars.push((offset, c));
        }
        let Ok(end) = u32::try_from(source.len()) else {
            panic!(
                "source file exceeds u32 byte-offset range: {} bytes",
                source.len()
            );
        };
        Self {
            source,
            file,
            chars,
            idx: 0,
            end,
        }
    }

    /// The character `ahead` positions past the cursor, if any.
    fn peek(&self, ahead: usize) -> Option<char> {
        self.chars.get(self.idx + ahead).map(|&(_, c)| c)
    }

    /// Consumes and returns the current character, if any.
    fn bump(&mut self) -> Option<char> {
        let c = self.peek(0);
        if c.is_some() {
            self.idx += 1;
        }
        c
    }

    /// If the next character is `c`, consumes it and reports so (the
    /// building block for longest-match operator lexing).
    fn eat(&mut self, c: char) -> bool {
        if self.peek(0) == Some(c) {
            self.bump();
            true
        } else {
            false
        }
    }

    /// Current byte offset (the position of the not-yet-consumed
    /// character, or [`Self::end`] at EOF).
    fn pos(&self) -> u32 {
        self.chars.get(self.idx).map_or(self.end, |&(o, _)| o)
    }

    fn span_from(&self, start: u32) -> Span {
        Span::new(self.file, start, self.pos())
    }

    /// Skips whitespace and comments between tokens (section 1, 1.1). The
    /// only failure reachable here is an unterminated block comment.
    fn skip_trivia(&mut self) -> Result<(), LexError> {
        loop {
            match self.peek(0) {
                Some(' ' | '\t' | '\u{0C}' | '\r' | '\n') => {
                    self.bump();
                }
                Some('/') if self.peek(1) == Some('/') => self.skip_line_comment(),
                Some('-') if self.peek(1) == Some('-') => self.skip_line_comment(),
                Some('/') if self.peek(1) == Some('*') => self.skip_block_comment()?,
                _ => break,
            }
        }
        Ok(())
    }

    fn skip_line_comment(&mut self) {
        while let Some(c) = self.peek(0) {
            if c == '\n' {
                break;
            }
            self.bump();
        }
    }

    /// Non-nesting: terminated by the first `*/` (section 1.1). `/**`
    /// doc-comments need no special casing -- the extra `*` is just part
    /// of the opening delimiter under the same "first `*/` wins" rule.
    fn skip_block_comment(&mut self) -> Result<(), LexError> {
        let start = self.pos();
        self.bump(); // '/'
        self.bump(); // '*'
        loop {
            match self.peek(0) {
                None => {
                    return Err(LexError::UnterminatedComment {
                        span: self.span_from(start),
                    })
                }
                Some('*') if self.peek(1) == Some('/') => {
                    self.bump();
                    self.bump();
                    break;
                }
                Some(_) => {
                    self.bump();
                }
            }
        }
        Ok(())
    }

    /// Dispatches on the already-peeked current character `c` (at byte
    /// offset `start`) to the matching token family.
    fn lex_token(&mut self, c: char, start: u32) -> Result<Token, LexError> {
        if is_ident_start(c) {
            Ok(self.lex_ident(start))
        } else if c.is_ascii_digit() {
            self.lex_number(start)
        } else if c == '"' {
            self.lex_string(start)
        } else {
            self.lex_operator(c, start)
        }
    }

    /// Identifiers (section 1.4): `start-char continue-char*`. Keywords
    /// are recognized after the maximal scan, so `allx` scans as one
    /// identifier and only then fails the keyword match.
    fn lex_ident(&mut self, start: u32) -> Token {
        self.bump(); // the start char, already classified by the caller
        while let Some(c) = self.peek(0) {
            if is_ident_continue(c) {
                self.bump();
            } else {
                break;
            }
        }
        let span = self.span_from(start);
        let text = &self.source[start as usize..span.end as usize];
        let kind = keyword_kind(text).unwrap_or(TokenKind::Ident);
        Token { kind, span }
    }

    /// Number literals (section 1.5, jar-verified behavioral rule): take
    /// the **maximal run of name-follow characters** (ASCII class, see
    /// [`is_ascii_name_follow`]) starting at the digit, then classify the
    /// whole run. There is no backtracking
    /// and never two tokens -- a run that is not exactly one valid literal
    /// is the "name cannot start with a number" error spanning the entire
    /// run (`3x`, `1_000`, `0x123`, `0b12` are all this error).
    fn lex_number(&mut self, start: u32) -> Result<Token, LexError> {
        self.bump(); // the leading digit, already classified by the caller
        while self.peek(0).is_some_and(is_ascii_name_follow) {
            self.bump();
        }
        let span = self.span_from(start);
        let text = &self.source[start as usize..span.end as usize];
        let Some((digits, radix)) = classify_number_run(text) else {
            return Err(LexError::NumberStartsName { span });
        };
        let value = parse_nonnegative_i32(&digits, radix, span)?;
        Ok(Token {
            kind: TokenKind::Number(value),
            span,
        })
    }

    /// String literals (section 1.6): one line, escapes exactly `\\`,
    /// `\n`, `\"`; empty and unterminated strings are errors.
    fn lex_string(&mut self, start: u32) -> Result<Token, LexError> {
        self.bump(); // opening '"'
        let mut value = String::new();
        loop {
            match self.peek(0) {
                None | Some('\n' | '\r') => {
                    return Err(LexError::UnterminatedString {
                        span: self.span_from(start),
                    })
                }
                Some('"') => {
                    self.bump();
                    break;
                }
                Some('\\') => {
                    self.bump();
                    match self.bump() {
                        Some('\\') => value.push('\\'),
                        Some('n') => value.push('\n'),
                        Some('"') => value.push('"'),
                        None => {
                            return Err(LexError::UnterminatedString {
                                span: self.span_from(start),
                            })
                        }
                        Some(_) => {
                            return Err(LexError::BadEscape {
                                span: self.span_from(start),
                            })
                        }
                    }
                }
                Some(c) => {
                    self.bump();
                    value.push(c);
                }
            }
        }

        if value.is_empty() {
            return Err(LexError::EmptyString {
                span: self.span_from(start),
            });
        }
        if self.peek(0).is_some_and(is_ascii_name_follow) {
            return Err(LexError::StringFollowedByIdent {
                span: self.span_from(start),
            });
        }
        Ok(Token {
            kind: TokenKind::Str(value),
            span: self.span_from(start),
        })
    }

    /// Operators and punctuation (section 1.2). Longest match: every
    /// multi-character spelling is checked before falling back to its
    /// single-character prefix.
    ///
    /// One arm per section-1.2 table row; splitting this dispatch further
    /// would only obscure the direct table-to-code correspondence
    /// (STYLE S2 soft-cap exception).
    #[allow(
        clippy::too_many_lines,
        reason = "one match arm per grammar-doc section 1.2 table row (STYLE S2 soft-cap exception); splitting the table would only obscure the 1:1 correspondence"
    )]
    fn lex_operator(&mut self, c: char, start: u32) -> Result<Token, LexError> {
        let kind = match c {
            '!' => {
                self.bump();
                TokenKind::Not
            }
            '#' => {
                self.bump();
                TokenKind::Hash
            }
            '&' => {
                self.bump();
                if self.eat('&') {
                    TokenKind::And
                } else {
                    TokenKind::Ampersand
                }
            }
            '(' => {
                self.bump();
                TokenKind::LParen
            }
            ')' => {
                self.bump();
                TokenKind::RParen
            }
            '*' => {
                self.bump();
                TokenKind::Star
            }
            '+' => {
                self.bump();
                if self.eat('+') {
                    TokenKind::PlusPlus
                } else {
                    TokenKind::Plus
                }
            }
            ',' => {
                self.bump();
                TokenKind::Comma
            }
            '<' => {
                self.bump();
                if self.peek(0) == Some('=') && self.peek(1) == Some('>') {
                    self.bump();
                    self.bump();
                    TokenKind::Iff
                } else if self.eat('=') {
                    TokenKind::Lte
                } else if self.eat(':') {
                    TokenKind::DomRestrict
                } else if self.eat('<') {
                    TokenKind::Shl
                } else {
                    TokenKind::Lt
                }
            }
            '=' => {
                self.bump();
                if self.eat('>') {
                    TokenKind::Implies
                } else if self.eat('<') {
                    TokenKind::Lte
                } else {
                    TokenKind::Equals
                }
            }
            '>' => {
                self.bump();
                if self.peek(0) == Some('>') && self.peek(1) == Some('>') {
                    self.bump();
                    self.bump();
                    TokenKind::Shr
                } else if self.eat('>') {
                    TokenKind::Sha
                } else if self.eat('=') {
                    TokenKind::Gte
                } else {
                    TokenKind::Gt
                }
            }
            '@' => {
                self.bump();
                TokenKind::At
            }
            '^' => {
                self.bump();
                TokenKind::Caret
            }
            '|' => {
                self.bump();
                if self.eat('|') {
                    TokenKind::Or
                } else {
                    TokenKind::Bar
                }
            }
            '~' => {
                self.bump();
                TokenKind::Tilde
            }
            '\'' | '\u{2018}' | '\u{2019}' => {
                self.bump();
                TokenKind::Prime
            }
            '-' => {
                self.bump();
                if self.eat('>') {
                    TokenKind::Arrow
                } else {
                    TokenKind::Minus
                }
            }
            '.' => {
                self.bump();
                TokenKind::Dot
            }
            '/' => {
                self.bump();
                TokenKind::Slash
            }
            ':' => {
                self.bump();
                if self.eat(':') {
                    TokenKind::Dot
                } else if self.eat('>') {
                    TokenKind::RangeRestrict
                } else {
                    TokenKind::Colon
                }
            }
            '[' => {
                self.bump();
                TokenKind::LBracket
            }
            ']' => {
                self.bump();
                TokenKind::RBracket
            }
            '{' => {
                self.bump();
                TokenKind::LBrace
            }
            '}' => {
                self.bump();
                TokenKind::RBrace
            }
            ';' => {
                self.bump();
                TokenKind::Semi
            }
            _ => {
                self.bump();
                return Err(LexError::StrayChar {
                    span: self.span_from(start),
                    ch: c,
                });
            }
        };
        Ok(Token {
            kind,
            span: self.span_from(start),
        })
    }
}

/// Java `isJavaIdentifierStart`, approximated per grammar-doc section 1.4:
/// ASCII letter, `_`, or `$` exactly; any other Unicode letter via
/// `char::is_alphabetic`. (`'` is deliberately excluded -- it is the prime
/// operator in Alloy 6, not an identifier character.)
fn is_ident_start(c: char) -> bool {
    if c.is_ascii() {
        c.is_ascii_alphabetic() || c == '_' || c == '$'
    } else {
        c.is_alphabetic()
    }
}

/// Java `isJavaIdentifierPart` plus the legacy `"` continue-char quirk
/// (section 1.4): `a"b` lexes as one identifier, not `a`, `"b"`-the-start-
/// of-a-string. This is why string literals only ever begin at a token
/// boundary -- a `"` reached while already scanning an identifier is
/// swallowed as a continue-char, never reinterpreted as a string opener.
fn is_ident_continue(c: char) -> bool {
    if c.is_ascii() {
        c.is_ascii_alphanumeric() || c == '_' || c == '$' || c == '"'
    } else {
        c.is_alphanumeric()
    }
}

/// The reference's *name-follow* class, `[$0-9a-zA-Z_"]` -- deliberately
/// ASCII-only, unlike [`is_ident_continue`]. It bounds the maximal run in
/// the number rule (section 1.5) and the string-followed-by-name error
/// (section 1.6): a non-ASCII letter directly after `3` or `"a"` starts a
/// fresh identifier token in the jar, it does not extend the error run.
fn is_ascii_name_follow(c: char) -> bool {
    c.is_ascii_alphanumeric() || matches!(c, '_' | '$' | '"')
}

/// Maps identifier text to its keyword token, if any (section 1.3).
/// `and`/`or`/`iff`/`implies`/`not` map to the symbolic operator tokens
/// (section 1.2) -- alternate spellings, not separate variants. A `match`
/// on the literal text avoids hashing in the lexer (ADR-0007: "no hashing
/// in a numbering path" applies in spirit here too) and lets `rustc`
/// compile it as a comparison table rather than paying `HashMap` overhead
/// per identifier.
fn keyword_kind(text: &str) -> Option<TokenKind> {
    Some(match text {
        "abstract" => TokenKind::Abstract,
        "all" => TokenKind::All,
        "and" => TokenKind::And,
        "as" => TokenKind::As,
        "assert" => TokenKind::Assert,
        "but" => TokenKind::But,
        "check" => TokenKind::Check,
        "disj" => TokenKind::Disj,
        "else" => TokenKind::Else,
        "enum" => TokenKind::Enum,
        "exactly" => TokenKind::Exactly,
        "expect" => TokenKind::Expect,
        "extends" => TokenKind::Extends,
        "fact" => TokenKind::Fact,
        "for" => TokenKind::For,
        "fun" => TokenKind::Fun,
        "iden" => TokenKind::Iden,
        "iff" => TokenKind::Iff,
        "implies" => TokenKind::Implies,
        "in" => TokenKind::In,
        "int" => TokenKind::IntCast,
        "Int" => TokenKind::Int,
        "let" => TokenKind::Let,
        "lone" => TokenKind::Lone,
        "module" => TokenKind::Module,
        "none" => TokenKind::None,
        "no" => TokenKind::No,
        "not" => TokenKind::Not,
        "one" => TokenKind::One,
        "open" => TokenKind::Open,
        "or" => TokenKind::Or,
        "pred" => TokenKind::Pred,
        "private" => TokenKind::Private,
        "run" => TokenKind::Run,
        "seq" => TokenKind::Seq,
        "set" => TokenKind::Set,
        "sig" => TokenKind::Sig,
        "some" => TokenKind::Some,
        "steps" => TokenKind::Steps,
        "String" => TokenKind::StringKw,
        "sum" => TokenKind::Sum,
        "this" => TokenKind::This,
        "univ" => TokenKind::Univ,
        "var" => TokenKind::Var,
        "always" => TokenKind::Always,
        "after" => TokenKind::After,
        "before" => TokenKind::Before,
        "eventually" => TokenKind::Eventually,
        "historically" => TokenKind::Historically,
        "once" => TokenKind::Once,
        "releases" => TokenKind::Releases,
        "since" => TokenKind::Since,
        "triggered" => TokenKind::Triggered,
        "until" => TokenKind::Until,
        _ => return None,
    })
}

/// Classifies a maximal digit-led identifier-continue run as one number
/// literal (section 1.5), returning `(digits-with-separators-stripped,
/// radix)`, or `None` when the run is not exactly one valid literal:
///
/// - all ASCII decimal digits => decimal (**no** underscores -- the jar
///   rejects `1_000`);
/// - `0x` + `_`s and full pairs of hex digits, consuming the entire rest
///   of the run => hex (`0x12`, `0x_12`, `0x_ff_01`; `0x1`/`0x123`/`0x1_2`
///   fail the pairing rule);
/// - `0b` + `[01_]+` with at least one real digit, consuming the entire
///   rest of the run => binary (`0b1_0`; `0b12` has a stray `2`).
fn classify_number_run(text: &str) -> Option<(String, u32)> {
    if text.bytes().all(|b| b.is_ascii_digit()) {
        return Some((text.to_owned(), 10));
    }
    if let Some(rest) = text.strip_prefix("0x") {
        return classify_hex_run(rest).map(|digits| (digits, 16));
    }
    if let Some(rest) = text.strip_prefix("0b") {
        return classify_binary_run(rest).map(|digits| (digits, 2));
    }
    None
}

/// The hex tail: each group is `_` or a **pair** of hex digits; the whole
/// tail must be consumed and at least one pair must be present.
fn classify_hex_run(rest: &str) -> Option<String> {
    let mut digits = String::new();
    let bytes = rest.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'_' => i += 1,
            hi if hi.is_ascii_hexdigit() => {
                let lo = *bytes.get(i + 1)?;
                if !lo.is_ascii_hexdigit() {
                    return None;
                }
                digits.push(char::from(hi));
                digits.push(char::from(lo));
                i += 2;
            }
            _ => return None,
        }
    }
    (!digits.is_empty()).then_some(digits)
}

/// The binary tail: `[01_]` only, whole tail consumed, at least one digit.
fn classify_binary_run(rest: &str) -> Option<String> {
    let mut digits = String::new();
    for c in rest.chars() {
        match c {
            '_' => {}
            '0' | '1' => digits.push(c),
            _ => return None,
        }
    }
    (!digits.is_empty()).then_some(digits)
}

/// Parses `digits` (underscores already stripped by the caller) as a
/// non-negative literal, mapping any failure to
/// [`LexError::NumberOverflow`] carrying `span` (the full literal, from
/// the caller's [`Lexer::span_from`]). The only way `u32::from_str_radix`
/// fails on an all-valid-digit string is magnitude, and the follow-up
/// `i32` range check catches values that fit `u32` but not a non-negative
/// `i32` (section 1.5).
fn parse_nonnegative_i32(digits: &str, radix: u32, span: Span) -> Result<i32, LexError> {
    let overflow = || LexError::NumberOverflow { span };
    let raw = u32::from_str_radix(digits, radix).map_err(|_| overflow())?;
    i32::try_from(raw).map_err(|_| overflow())
}

// File exceeds the ~500-line soft cap (STYLE S2): the implementation above
// is ~500 lines on its own, and colocated unit tests (STYLE U1) covering
// every operator spelling, all ~90 token kinds' keyword/identifier
// boundaries, and every error variant add real bulk that shouldn't be
// pulled into a separate file it would then be disconnected from.
#[cfg(test)]
mod tests {
    use super::*;
    use crate::ArenaId;

    fn file() -> FileId {
        FileId::from_index(0)
    }

    fn lex_ok(source: &str) -> Vec<Token> {
        let Ok(tokens) = lex(source, file()) else {
            panic!("expected {source:?} to lex cleanly");
        };
        tokens
    }

    fn kinds(source: &str) -> Vec<TokenKind> {
        lex_ok(source).into_iter().map(|t| t.kind).collect()
    }

    fn lex_err(source: &str) -> LexError {
        match lex(source, file()) {
            Ok(tokens) => panic!("expected {source:?} to fail lexing, got {tokens:?}"),
            Err(e) => e,
        }
    }

    // -- Operators: longest match & every spelling -----------------------

    #[test]
    fn every_operator_spelling() {
        let cases: &[(&str, TokenKind)] = &[
            ("!", TokenKind::Not),
            ("#", TokenKind::Hash),
            ("&&", TokenKind::And),
            ("&", TokenKind::Ampersand),
            ("(", TokenKind::LParen),
            (")", TokenKind::RParen),
            ("*", TokenKind::Star),
            ("++", TokenKind::PlusPlus),
            ("+", TokenKind::Plus),
            (",", TokenKind::Comma),
            ("<<", TokenKind::Shl),
            ("=>", TokenKind::Implies),
            (">>>", TokenKind::Shr),
            (">=", TokenKind::Gte),
            ("@", TokenKind::At),
            ("^", TokenKind::Caret),
            ("||", TokenKind::Or),
            ("~", TokenKind::Tilde),
            ("->", TokenKind::Arrow),
            ("-", TokenKind::Minus),
            (".", TokenKind::Dot),
            ("::", TokenKind::Dot),
            ("/", TokenKind::Slash),
            (":>", TokenKind::RangeRestrict),
            (":", TokenKind::Colon),
            ("<=>", TokenKind::Iff),
            ("<=", TokenKind::Lte),
            ("=<", TokenKind::Lte),
            ("<:", TokenKind::DomRestrict),
            ("<", TokenKind::Lt),
            ("=", TokenKind::Equals),
            (">>", TokenKind::Sha),
            (">", TokenKind::Gt),
            ("[", TokenKind::LBracket),
            ("]", TokenKind::RBracket),
            ("{", TokenKind::LBrace),
            ("}", TokenKind::RBrace),
            ("|", TokenKind::Bar),
            (";", TokenKind::Semi),
        ];
        for (src, expected) in cases {
            let mut ks = kinds(src);
            assert_eq!(ks.pop(), Some(TokenKind::Eof), "source: {src:?}");
            assert_eq!(ks, vec![expected.clone()], "source: {src:?}");
        }
    }

    #[test]
    fn all_three_prime_spellings() {
        for src in ["'", "\u{2018}", "\u{2019}"] {
            let ks = kinds(src);
            assert_eq!(
                ks,
                vec![TokenKind::Prime, TokenKind::Eof],
                "source: {src:?}"
            );
        }
    }

    #[test]
    fn longest_match_shift_family() {
        assert_eq!(kinds(">"), vec![TokenKind::Gt, TokenKind::Eof]);
        assert_eq!(kinds(">>"), vec![TokenKind::Sha, TokenKind::Eof]);
        assert_eq!(kinds(">>>"), vec![TokenKind::Shr, TokenKind::Eof]);
        assert_eq!(
            kinds(">>>>"),
            vec![TokenKind::Shr, TokenKind::Gt, TokenKind::Eof]
        );
    }

    #[test]
    fn longest_match_lte_family() {
        assert_eq!(kinds("<"), vec![TokenKind::Lt, TokenKind::Eof]);
        assert_eq!(kinds("<="), vec![TokenKind::Lte, TokenKind::Eof]);
        assert_eq!(kinds("<=>"), vec![TokenKind::Iff, TokenKind::Eof]);
    }

    #[test]
    fn longest_match_plus_family() {
        assert_eq!(kinds("+"), vec![TokenKind::Plus, TokenKind::Eof]);
        assert_eq!(kinds("++"), vec![TokenKind::PlusPlus, TokenKind::Eof]);
        assert_eq!(
            kinds("+++"),
            vec![TokenKind::PlusPlus, TokenKind::Plus, TokenKind::Eof]
        );
    }

    #[test]
    fn longest_match_arrow_vs_minus() {
        assert_eq!(kinds("-"), vec![TokenKind::Minus, TokenKind::Eof]);
        assert_eq!(kinds("->"), vec![TokenKind::Arrow, TokenKind::Eof]);
    }

    #[test]
    fn no_double_equals_token() {
        // Section 1.2: there is no `==`; it lexes as two `Equals`.
        assert_eq!(
            kinds("=="),
            vec![TokenKind::Equals, TokenKind::Equals, TokenKind::Eof]
        );
    }

    // -- Keywords vs identifiers ------------------------------------------

    #[test]
    fn keyword_prefix_is_still_an_identifier() {
        assert_eq!(kinds("allx"), vec![TokenKind::Ident, TokenKind::Eof]);
    }

    #[test]
    fn int_and_capital_int_are_distinct_tokens() {
        assert_eq!(kinds("int"), vec![TokenKind::IntCast, TokenKind::Eof]);
        assert_eq!(kinds("Int"), vec![TokenKind::Int, TokenKind::Eof]);
    }

    #[test]
    fn string_keyword_vs_string_identifier() {
        assert_eq!(kinds("String"), vec![TokenKind::StringKw, TokenKind::Eof]);
        assert_eq!(kinds("string"), vec![TokenKind::Ident, TokenKind::Eof]);
    }

    #[test]
    fn keyword_alternate_spellings_map_to_operator_tokens() {
        assert_eq!(kinds("and"), vec![TokenKind::And, TokenKind::Eof]);
        assert_eq!(kinds("or"), vec![TokenKind::Or, TokenKind::Eof]);
        assert_eq!(kinds("iff"), vec![TokenKind::Iff, TokenKind::Eof]);
        assert_eq!(kinds("implies"), vec![TokenKind::Implies, TokenKind::Eof]);
        assert_eq!(kinds("not"), vec![TokenKind::Not, TokenKind::Eof]);
    }

    // -- Identifiers with legacy quirks ------------------------------------

    #[test]
    fn identifier_swallows_interior_quote() {
        assert_eq!(kinds("a\"b"), vec![TokenKind::Ident, TokenKind::Eof]);
    }

    #[test]
    fn identifier_with_dollar_and_underscore() {
        assert_eq!(kinds("_foo$bar_1"), vec![TokenKind::Ident, TokenKind::Eof]);
    }

    #[test]
    fn identifier_may_start_with_dollar() {
        assert_eq!(kinds("$x"), vec![TokenKind::Ident, TokenKind::Eof]);
    }

    // -- Comments -----------------------------------------------------------

    #[test]
    fn line_comments_both_spellings() {
        assert_eq!(
            kinds("// hi\n1"),
            vec![TokenKind::Number(1), TokenKind::Eof]
        );
        assert_eq!(
            kinds("-- hi\n1"),
            vec![TokenKind::Number(1), TokenKind::Eof]
        );
    }

    #[test]
    fn block_comment_non_nesting() {
        // Non-nesting: the FIRST `*/` (right after "nested") terminates
        // the comment. What's left, "  */ 1", then relexes as ordinary
        // tokens: `*`, `/`, `1` -- proving the inner `/*` did not open a
        // second nesting level.
        assert_eq!(
            kinds("/* /* nested */ */ 1"),
            vec![
                TokenKind::Star,
                TokenKind::Slash,
                TokenKind::Number(1),
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn doc_block_comment() {
        assert_eq!(
            kinds("/** doc */ 1"),
            vec![TokenKind::Number(1), TokenKind::Eof]
        );
    }

    #[test]
    fn unterminated_block_comment_errors() {
        assert!(matches!(
            lex_err("/* never closes"),
            LexError::UnterminatedComment { .. }
        ));
    }

    // -- Numbers (six jar verdicts of section 1.5 verified 2026-07-15) ---

    #[test]
    fn plain_decimal() {
        assert_eq!(kinds("1000"), vec![TokenKind::Number(1000), TokenKind::Eof]);
        assert_eq!(kinds("0"), vec![TokenKind::Number(0), TokenKind::Eof]);
    }

    #[test]
    fn decimal_rejects_underscores() {
        // Jar-verified: `1_000` is "Name cannot start with a number",
        // NOT a separator-friendly decimal.
        assert!(matches!(
            lex_err("1_000"),
            LexError::NumberStartsName { .. }
        ));
    }

    #[test]
    fn hex_pair_rule_accepts() {
        // Jar-verified: `0x12` and `0x_12` accepted.
        assert_eq!(kinds("0x12"), vec![TokenKind::Number(0x12), TokenKind::Eof]);
        assert_eq!(
            kinds("0x_12"),
            vec![TokenKind::Number(0x12), TokenKind::Eof]
        );
        assert_eq!(
            kinds("0x_ff_01"),
            vec![TokenKind::Number(0xff01), TokenKind::Eof]
        );
    }

    #[test]
    fn hex_pair_rule_rejects_odd_or_split_digits() {
        // Jar-verified: `0x123` rejected (and `0x1`, `0x1_2` with it) --
        // the whole run is ONE error, never `0x12` + `3` as two tokens.
        assert!(matches!(lex_err("0x1"), LexError::NumberStartsName { .. }));
        assert!(matches!(
            lex_err("0x123"),
            LexError::NumberStartsName { .. }
        ));
        assert!(matches!(
            lex_err("0x1_2"),
            LexError::NumberStartsName { .. }
        ));
    }

    #[test]
    fn binary_literal_accepts_underscores() {
        // Jar-verified: `0b1_0` accepted.
        assert_eq!(
            kinds("0b1_0"),
            vec![TokenKind::Number(0b10), TokenKind::Eof]
        );
        assert_eq!(
            kinds("0b1_01"),
            vec![TokenKind::Number(0b101), TokenKind::Eof]
        );
    }

    #[test]
    fn binary_rejects_non_binary_digit() {
        // Jar-verified: `0b12` rejected.
        assert!(matches!(lex_err("0b12"), LexError::NumberStartsName { .. }));
    }

    #[test]
    fn number_immediately_followed_by_ident_char_errors() {
        assert!(matches!(lex_err("3x"), LexError::NumberStartsName { .. }));
    }

    #[test]
    fn number_error_spans_the_whole_run() {
        // The offending byte range is the maximal identifier-continue
        // run, not just its numeric prefix.
        let LexError::NumberStartsName { span } = lex_err("3xy_z") else {
            panic!("expected NumberStartsName");
        };
        assert_eq!((span.start, span.end), (0, 5));
        let LexError::NumberStartsName { span } = lex_err("0x123") else {
            panic!("expected NumberStartsName");
        };
        assert_eq!((span.start, span.end), (0, 5));
    }

    #[test]
    fn i32_overflow_errors() {
        assert!(matches!(
            lex_err("99999999999999"),
            LexError::NumberOverflow { .. }
        ));
        // Fits u32 but not a non-negative i32.
        assert!(matches!(
            lex_err("0xff_ff_ff_ff"),
            LexError::NumberOverflow { .. }
        ));
    }

    // -- Strings ----------------------------------------------------------

    #[test]
    fn string_escapes() {
        assert_eq!(
            kinds(r#""a\\b\nc\"d""#),
            vec![TokenKind::Str("a\\b\nc\"d".to_owned()), TokenKind::Eof]
        );
    }

    #[test]
    fn empty_string_errors() {
        assert!(matches!(lex_err("\"\""), LexError::EmptyString { .. }));
    }

    #[test]
    fn unterminated_string_errors() {
        assert!(matches!(
            lex_err("\"never closes"),
            LexError::UnterminatedString { .. }
        ));
    }

    #[test]
    fn multi_line_string_errors() {
        assert!(matches!(
            lex_err("\"line one\nline two\""),
            LexError::UnterminatedString { .. }
        ));
    }

    #[test]
    fn string_followed_by_ident_char_errors() {
        assert!(matches!(
            lex_err("\"foo\"bar"),
            LexError::StringFollowedByIdent { .. }
        ));
    }

    /// Jar-verified: the follow class includes digits and `"` (section 1.6),
    /// so `"ab"9` and `"a""b"` are single errors, not two tokens.
    #[test]
    fn string_followed_by_digit_or_quote_errors() {
        assert!(matches!(
            lex_err("\"ab\"9"),
            LexError::StringFollowedByIdent { .. }
        ));
        assert!(matches!(
            lex_err("\"a\"\"b\""),
            LexError::StringFollowedByIdent { .. }
        ));
    }

    /// The follow classes are ASCII-only (sections 1.5-1.6): a non-ASCII
    /// letter directly after a number or a closed string starts a fresh
    /// identifier token instead of extending an error run.
    #[test]
    fn non_ascii_letter_ends_number_and_string_runs() {
        assert_eq!(
            kinds("3é"),
            vec![TokenKind::Number(3), TokenKind::Ident, TokenKind::Eof]
        );
        let tokens = lex_ok("\"a\"é");
        assert_eq!(tokens[0].kind, TokenKind::Str("a".to_owned()));
        assert_eq!(tokens[1].kind, TokenKind::Ident);
    }

    #[test]
    fn bad_escape_errors() {
        assert!(matches!(lex_err(r#""a\tb""#), LexError::BadEscape { .. }));
    }

    // -- Spans --------------------------------------------------------------

    #[test]
    fn span_byte_offsets() {
        let tokens = lex_ok("sig Foo {}");
        assert_eq!(tokens[0].kind, TokenKind::Sig);
        assert_eq!((tokens[0].span.start, tokens[0].span.end), (0, 3));
        assert_eq!(tokens[1].kind, TokenKind::Ident);
        assert_eq!((tokens[1].span.start, tokens[1].span.end), (4, 7));
        assert_eq!(tokens[2].kind, TokenKind::LBrace);
        assert_eq!((tokens[2].span.start, tokens[2].span.end), (8, 9));
        assert_eq!(tokens[3].kind, TokenKind::RBrace);
        assert_eq!((tokens[3].span.start, tokens[3].span.end), (9, 10));
        let eof = &tokens[4];
        assert_eq!(eof.kind, TokenKind::Eof);
        assert_eq!((eof.span.start, eof.span.end), (10, 10));
    }

    #[test]
    fn empty_source_is_just_eof() {
        let tokens = lex_ok("");
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].kind, TokenKind::Eof);
        assert_eq!((tokens[0].span.start, tokens[0].span.end), (0, 0));
    }

    #[test]
    fn stray_character_errors() {
        assert!(matches!(lex_err("`"), LexError::StrayChar { ch: '`', .. }));
    }

    #[test]
    fn lex_error_span_accessor_matches_variant() {
        let LexError::NumberStartsName { span } = lex_err("3x") else {
            panic!("expected NumberStartsName");
        };
        assert_eq!(lex_err("3x").span(), span);
    }
}
