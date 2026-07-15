//! Token-stream cooking: the reference's `CompFilter` rewrites (grammar-doc
//! section 2), implemented as a separate, unit-testable pass over the raw
//! [`lex`](crate::lexer::lex) output.
//!
//! **Output type choice.** Cooking returns a `Vec<Token>` of the *same*
//! [`Token`] type, using the cooked-only [`TokenKind`] variants documented in
//! `token.rs`. A second token type would force the parser to convert ~90
//! pass-through kinds and would duplicate the whole keyword set; reusing
//! `TokenKind` keeps the parser consuming one type, and lets an F3-folded
//! negative literal reuse [`TokenKind::Number`] verbatim. The invariant that
//! the cooked-only kinds never appear in `lex()` output is stated at their
//! definition and upheld here (only this module produces them).
//!
//! The four rewrites run in the reference's pipeline order (F1 → F2 → F3 →
//! F4); each is a self-contained pass so the ordering is explicit and each
//! is independently testable. Behavior — not structure — mirrors the filter.

use crate::ast::{Mult, Quant};
use crate::span::Span;
use crate::token::{Token, TokenKind};

/// Applies the four token-stream rewrites in pipeline order and returns the
/// cooked stream the parser consumes. `source` is needed because F2 must read
/// identifier text (`pred/totalOrder`, `fun/add`, …) that [`TokenKind::Ident`]
/// stores only as a span.
#[must_use]
pub fn cook(tokens: &[Token], source: &str) -> Vec<Token> {
    let f1 = reorder_command_labels(tokens);
    let f2 = merge_tokens(&f1, source);
    let f3 = fold_negative_literals(&f2);
    disambiguate_quantifiers(f3)
}

/// Reads the identifier text a span points at (F2 name merges).
fn ident_text(source: &str, span: Span) -> &str {
    &source[span.start as usize..span.end as usize]
}

/// F1 — command label reorder. `ID : (run|check) (ID|{)` becomes
/// `(run|check) ID (ID|{)`, dropping the colon, so a labeled command parses
/// as the unlabeled grammar with the label as the command's `Name`.
fn reorder_command_labels(tokens: &[Token]) -> Vec<Token> {
    let mut out = Vec::with_capacity(tokens.len());
    let mut i = 0;
    while i < tokens.len() {
        if is_command_label(tokens, i) {
            // Emit run/check (i+2) then the label ID (i), drop the colon
            // (i+1); the target (i+3) is left to be processed normally.
            out.push(tokens[i + 2].clone());
            out.push(tokens[i].clone());
            i += 3;
        } else {
            out.push(tokens[i].clone());
            i += 1;
        }
    }
    out
}

/// Whether position `i` begins the `ID : (run|check) (ID|{)` pattern.
fn is_command_label(tokens: &[Token], i: usize) -> bool {
    let kind = |k: usize| tokens.get(k).map(|t| &t.kind);
    matches!(kind(i), Some(TokenKind::Ident))
        && matches!(kind(i + 1), Some(TokenKind::Colon))
        && matches!(kind(i + 2), Some(TokenKind::Run | TokenKind::Check))
        && matches!(kind(i + 3), Some(TokenKind::Ident | TokenKind::LBrace))
}

/// F2 — global merges: negated comparisons, `pred/totalOrder`, `fun/*`
/// operators/constants, and multiplicity-annotated arrows. Applied over the
/// whole stream exactly as the reference filter's phase-2 scanner.
fn merge_tokens(tokens: &[Token], source: &str) -> Vec<Token> {
    let mut out = Vec::with_capacity(tokens.len());
    let mut i = 0;
    while i < tokens.len() {
        let consumed = try_merge(tokens, i, source, &mut out);
        i += consumed;
    }
    out
}

/// Attempts a single F2 merge starting at `i`, pushing the result and
/// returning how many input tokens it consumed (always ≥ 1).
fn try_merge(tokens: &[Token], i: usize, source: &str, out: &mut Vec<Token>) -> usize {
    let kind = |k: usize| tokens.get(k).map(|t| &t.kind);
    match &tokens[i].kind {
        TokenKind::Not => merge_not(tokens, i, out),
        TokenKind::Pred if matches!(kind(i + 1), Some(TokenKind::Slash)) => {
            merge_pred(tokens, i, source, out)
        }
        TokenKind::Fun if matches!(kind(i + 1), Some(TokenKind::Slash)) => {
            merge_fun(tokens, i, source, out)
        }
        TokenKind::One | TokenKind::Lone | TokenKind::Some | TokenKind::Set => {
            merge_left_arrow(tokens, i, out)
        }
        TokenKind::Arrow => merge_bare_arrow(tokens, i, out),
        _ => {
            out.push(tokens[i].clone());
            1
        }
    }
}

/// `! <cmp>` / `not <cmp>` → one negated-comparison token.
fn merge_not(tokens: &[Token], i: usize, out: &mut Vec<Token>) -> usize {
    let negated = tokens.get(i + 1).and_then(|t| match t.kind {
        TokenKind::In => Some(TokenKind::NotIn),
        TokenKind::Equals => Some(TokenKind::NotEquals),
        TokenKind::Lt => Some(TokenKind::NotLt),
        TokenKind::Lte => Some(TokenKind::NotLte),
        TokenKind::Gt => Some(TokenKind::NotGt),
        TokenKind::Gte => Some(TokenKind::NotGte),
        _ => None,
    });
    if let Some(kind) = negated {
        out.push(merged(&tokens[i], &tokens[i + 1], kind));
        2
    } else {
        out.push(tokens[i].clone());
        1
    }
}

/// `pred / totalOrder` → the builtin-name token.
fn merge_pred(tokens: &[Token], i: usize, source: &str, out: &mut Vec<Token>) -> usize {
    if let Some(z) = tokens.get(i + 2) {
        if z.kind == TokenKind::Ident && ident_text(source, z.span) == "totalOrder" {
            out.push(merged(&tokens[i], z, TokenKind::TotalOrder));
            return 3;
        }
    }
    out.push(tokens[i].clone());
    1
}

/// `fun / (add|sub|mul|div|rem|min|max|next)` → the operator/constant token.
fn merge_fun(tokens: &[Token], i: usize, source: &str, out: &mut Vec<Token>) -> usize {
    if let Some(z) = tokens.get(i + 2) {
        if z.kind == TokenKind::Ident {
            let cooked = match ident_text(source, z.span) {
                "add" => Some(TokenKind::FunAdd),
                "sub" => Some(TokenKind::FunSub),
                "mul" => Some(TokenKind::FunMul),
                "div" => Some(TokenKind::FunDiv),
                "rem" => Some(TokenKind::FunRem),
                "min" => Some(TokenKind::FunMin),
                "max" => Some(TokenKind::FunMax),
                "next" => Some(TokenKind::FunNext),
                _ => None,
            };
            if let Some(kind) = cooked {
                out.push(merged(&tokens[i], z, kind));
                return 3;
            }
        }
    }
    out.push(tokens[i].clone());
    1
}

/// `m -> [n]` where `m ∈ {one, lone, some, set}` → one annotated-arrow token
/// (`set` side is unannotated). Falls through if no `->` follows.
fn merge_left_arrow(tokens: &[Token], i: usize, out: &mut Vec<Token>) -> usize {
    if !matches!(tokens.get(i + 1).map(|t| &t.kind), Some(TokenKind::Arrow)) {
        out.push(tokens[i].clone());
        return 1;
    }
    let lhs = arrow_side(&tokens[i].kind);
    let (rhs, extra) = arrow_trailing(tokens.get(i + 2).map(|t| &t.kind));
    let last = i + 1 + extra;
    out.push(arrow_token(&tokens[i], &tokens[last], lhs, rhs));
    2 + extra
}

/// Bare `->` possibly followed by a right multiplicity.
fn merge_bare_arrow(tokens: &[Token], i: usize, out: &mut Vec<Token>) -> usize {
    let (rhs, extra) = arrow_trailing(tokens.get(i + 1).map(|t| &t.kind));
    // `-> some|one|lone` becomes an annotated arrow; `->` alone stays a plain
    // Arrow; `-> set` (extra == 1, no mult) is collapsed to a plain Arrow.
    if rhs.is_some() {
        out.push(arrow_token(&tokens[i], &tokens[i + extra], None, rhs));
    } else if extra == 1 {
        out.push(merged(&tokens[i], &tokens[i + 1], TokenKind::Arrow));
    } else {
        out.push(tokens[i].clone());
    }
    1 + extra
}

/// The multiplicity a left-arrow keyword contributes (`set` = unannotated).
fn arrow_side(kind: &TokenKind) -> Option<Mult> {
    match kind {
        TokenKind::One => Some(Mult::One),
        TokenKind::Lone => Some(Mult::Lone),
        TokenKind::Some => Some(Mult::Some),
        // `set` and everything else → unannotated.
        _ => None,
    }
}

/// Interprets the token after an `->`: `some|one|lone` annotate (consumed);
/// `set` is consumed but unannotated; anything else is left in place.
/// Returns `(multiplicity, tokens_consumed_after_the_arrow)`.
fn arrow_trailing(next: Option<&TokenKind>) -> (Option<Mult>, usize) {
    match next {
        Some(TokenKind::One) => (Some(Mult::One), 1),
        Some(TokenKind::Lone) => (Some(Mult::Lone), 1),
        Some(TokenKind::Some) => (Some(Mult::Some), 1),
        Some(TokenKind::Set) => (None, 1),
        _ => (None, 0),
    }
}

/// Builds a merged arrow spanning `first..=last`. A doubly-unannotated arrow
/// (both sides `set`/absent) collapses to a plain [`TokenKind::Arrow`], exactly
/// as the reference filter merges `set -> set` back to `ARROW`.
fn arrow_token(first: &Token, last: &Token, lhs: Option<Mult>, rhs: Option<Mult>) -> Token {
    let kind = if lhs.is_none() && rhs.is_none() {
        TokenKind::Arrow
    } else {
        TokenKind::ArrowMult { lhs, rhs }
    };
    Token {
        kind,
        span: first.span.merge(last.span),
    }
}

/// Clones `a` with its span extended over `b` and its kind replaced — the
/// reference filter's `merge`.
fn merged(a: &Token, b: &Token, kind: TokenKind) -> Token {
    Token {
        kind,
        span: a.span.merge(b.span),
    }
}

/// F3 — unary-minus fold. `- <number>` becomes a negative
/// [`TokenKind::Number`] unless the previous emitted token can end an
/// expression (grammar-doc section 2, F3), in which case the `-` is binary.
fn fold_negative_literals(tokens: &[Token]) -> Vec<Token> {
    let mut out: Vec<Token> = Vec::with_capacity(tokens.len());
    let mut i = 0;
    while i < tokens.len() {
        let prev_ends_expr = out.last().is_some_and(|t| ends_expression(&t.kind));
        if !prev_ends_expr && tokens[i].kind == TokenKind::Minus {
            if let Some(Token {
                kind: TokenKind::Number(n),
                span,
            }) = tokens.get(i + 1)
            {
                out.push(Token {
                    kind: TokenKind::Number(-n),
                    span: tokens[i].span.merge(*span),
                });
                i += 2;
                continue;
            }
        }
        out.push(tokens[i].clone());
        i += 1;
    }
    out
}

/// Whether a token can end an expression, blocking an F3 minus-fold after it
/// (the reference filter's phase-3 `last` set).
fn ends_expression(kind: &TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::RParen
            | TokenKind::RBracket
            | TokenKind::RBrace
            | TokenKind::Disj
            | TokenKind::TotalOrder
            | TokenKind::IntCast
            | TokenKind::Sum
            | TokenKind::Ident
            | TokenKind::Number(_)
            | TokenKind::Str(_)
            | TokenKind::Iden
            | TokenKind::This
            | TokenKind::FunMin
            | TokenKind::FunMax
            | TokenKind::FunNext
            | TokenKind::Univ
            | TokenKind::Int
            | TokenKind::None
    )
}

/// F4 — quantifier disambiguation. `all no some lone one sum` become
/// [`TokenKind::Quantifier`] iff the previous token is neither `:` nor `disj`
/// and the lookahead matches `[private] [disj] ID (, ID)* :`.
fn disambiguate_quantifiers(mut tokens: Vec<Token>) -> Vec<Token> {
    for i in 0..tokens.len() {
        let Some(quant) = quant_candidate(&tokens[i].kind) else {
            continue;
        };
        let prev_blocks = i
            .checked_sub(1)
            .is_some_and(|p| matches!(tokens[p].kind, TokenKind::Colon | TokenKind::Disj));
        if !prev_blocks && has_decl_lookahead(&tokens, i) {
            tokens[i].kind = TokenKind::Quantifier(quant);
        }
    }
    tokens
}

/// The quantifier a raw keyword would denote, if it is a candidate.
fn quant_candidate(kind: &TokenKind) -> Option<Quant> {
    match kind {
        TokenKind::All => Some(Quant::All),
        TokenKind::No => Some(Quant::No),
        TokenKind::Some => Some(Quant::Some),
        TokenKind::Lone => Some(Quant::Lone),
        TokenKind::One => Some(Quant::One),
        TokenKind::Sum => Some(Quant::Sum),
        _ => None,
    }
}

/// Whether `[private] [disj] ID (, ID)* :` follows the token at `i` — the
/// reference filter's phase-1 decl lookahead, requiring the `:` to arrive
/// right after an identifier (not after a trailing comma).
fn has_decl_lookahead(tokens: &[Token], i: usize) -> bool {
    let kind = |k: usize| tokens.get(k).map(|t| &t.kind);
    let mut j = i + 1;
    if matches!(kind(j), Some(TokenKind::Private)) {
        j += 1;
    }
    if matches!(kind(j), Some(TokenKind::Disj)) {
        j += 1;
    }
    if !matches!(kind(j), Some(TokenKind::Ident)) {
        return false;
    }
    loop {
        // Invariant: token at j is an identifier.
        j += 1;
        match kind(j) {
            Some(TokenKind::Comma) => {
                j += 1;
                if !matches!(kind(j), Some(TokenKind::Ident)) {
                    return false;
                }
            }
            Some(TokenKind::Colon) => return true,
            _ => return false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::lex;
    use crate::span::FileId;
    use crate::ArenaId;

    fn cooked(source: &str) -> Vec<TokenKind> {
        let Ok(raw) = lex(source, FileId::from_index(0)) else {
            panic!("expected {source:?} to lex");
        };
        cook(&raw, source).into_iter().map(|t| t.kind).collect()
    }

    // -- F1: command labels ------------------------------------------------

    #[test]
    fn f1_reorders_labeled_run_name() {
        assert_eq!(
            cooked("c: run p"),
            vec![
                TokenKind::Run,
                TokenKind::Ident,
                TokenKind::Ident,
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn f1_reorders_labeled_check_block() {
        assert_eq!(
            cooked("c: check {"),
            vec![
                TokenKind::Check,
                TokenKind::Ident,
                TokenKind::LBrace,
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn f1_leaves_unlabeled_and_field_colons_alone() {
        // A `:` not before run/check (here a field decl) is untouched.
        assert_eq!(
            cooked("x : A"),
            vec![
                TokenKind::Ident,
                TokenKind::Colon,
                TokenKind::Ident,
                TokenKind::Eof
            ]
        );
    }

    // -- F2: merges --------------------------------------------------------

    #[test]
    fn f2_negated_comparisons() {
        assert_eq!(cooked("a !in b")[1], TokenKind::NotIn);
        assert_eq!(cooked("a not = b")[1], TokenKind::NotEquals);
        assert_eq!(cooked("a !< b")[1], TokenKind::NotLt);
        assert_eq!(cooked("a !=< b")[1], TokenKind::NotLte);
        assert_eq!(cooked("a !> b")[1], TokenKind::NotGt);
        assert_eq!(cooked("a !>= b")[1], TokenKind::NotGte);
        // A lone `!` (not before a comparison) stays.
        assert_eq!(cooked("!a")[0], TokenKind::Not);
    }

    #[test]
    fn f2_pred_and_fun_names() {
        assert_eq!(cooked("pred/totalOrder[a]")[0], TokenKind::TotalOrder);
        assert_eq!(cooked("a fun/add b")[1], TokenKind::FunAdd);
        assert_eq!(cooked("fun/min")[0], TokenKind::FunMin);
        // `pred / other` is not a builtin merge.
        assert_eq!(cooked("pred/other")[0], TokenKind::Pred);
    }

    #[test]
    fn f2_arrow_multiplicities() {
        let mult = |s: &str| cooked(s)[1].clone();
        assert_eq!(mult("A -> B"), TokenKind::Arrow, "plain arrow stays Arrow");
        assert_eq!(
            mult("A some -> one B"),
            TokenKind::ArrowMult {
                lhs: Some(Mult::Some),
                rhs: Some(Mult::One)
            }
        );
        assert_eq!(
            mult("A -> lone B"),
            TokenKind::ArrowMult {
                lhs: None,
                rhs: Some(Mult::Lone)
            }
        );
        assert_eq!(
            mult("A lone -> B"),
            TokenKind::ArrowMult {
                lhs: Some(Mult::Lone),
                rhs: None
            }
        );
        // `set` sides collapse to unannotated: `set -> set` == plain arrow.
        assert_eq!(mult("A set -> set B"), TokenKind::Arrow);
    }

    // -- F3: negative literals --------------------------------------------

    #[test]
    fn f3_folds_after_operator() {
        // `x = -1`: `=` cannot end an expression, so `-1` folds.
        assert_eq!(
            cooked("x = -1"),
            vec![
                TokenKind::Ident,
                TokenKind::Equals,
                TokenKind::Number(-1),
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn f3_no_fold_after_expression_end() {
        // `n - 1`: an identifier ends an expression, so `-` stays binary.
        assert_eq!(
            cooked("n - 1"),
            vec![
                TokenKind::Ident,
                TokenKind::Minus,
                TokenKind::Number(1),
                TokenKind::Eof
            ]
        );
        // Same after `)`.
        assert_eq!(cooked(") - 1")[1], TokenKind::Minus);
    }

    #[test]
    fn f3_folds_at_start() {
        assert_eq!(cooked("-1")[0], TokenKind::Number(-1));
    }

    // -- F4: quantifier vs multiplicity -----------------------------------

    #[test]
    fn f4_quantifier_when_decl_follows() {
        assert_eq!(cooked("some x: A")[0], TokenKind::Quantifier(Quant::Some));
        assert_eq!(
            cooked("all disj x, y: A")[0],
            TokenKind::Quantifier(Quant::All)
        );
        assert_eq!(cooked("sum p: A")[0], TokenKind::Quantifier(Quant::Sum));
    }

    #[test]
    fn f4_not_quantifier_as_test_or_mult() {
        // `some x` (no `:`) is a non-emptiness test, stays raw.
        assert_eq!(cooked("some x")[0], TokenKind::Some);
        // After `:`, `one` is a multiplicity marker, never a quantifier.
        assert_eq!(cooked("y: one A")[2], TokenKind::One);
        // After `disj`, blocked as well.
        assert_eq!(cooked("disj one")[1], TokenKind::One);
    }
}
