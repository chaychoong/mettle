//! Hand-written recursive-descent + precedence-climbing parser for Alloy 6
//! (ADR-0007). Paragraphs, declarations, and scopes are recursive descent;
//! expressions use a Pratt core over the 21-level precedence table
//! (grammar-doc section 3). Input is the cooked token stream ([`cook`]).
//!
//! Error strategy is fail-fast (ADR-0007 section 3): the first syntax error
//! stops the parse and returns a typed [`ParseError`] carrying a span and the
//! production context. Parse-time semantic checks the reference performs in
//! grammar actions (scope-on-`univ`, growing-int scope, defined-disjoint
//! fields, `$` in declared names, …) are reproduced here with equivalent
//! precision.

use thiserror::Error;

use crate::ast::{
    Ast, BinOp, CmdDecl, CmdKind, CmdTarget, CmpOp, Const, Decl, DeclId, EnumDecl, Expect, Expr,
    ExprId, ExprKind, FactDecl, FunDecl, Ident, LetBinding, MacroDecl, ModuleHeader, ModuleParam,
    Mult, Open, Para, ParaName, PredDecl, QualName, Scope, ScopeEnd, ScopeTarget, SigDecl, SigMult,
    SigParent, SigQual, TypeScope, UnOp,
};
use crate::lexer::{lex, LexError};
use crate::span::{FileId, Span};
use crate::token::{Token, TokenKind};

/// Parse-time failures (grammar-doc section 4). Each variant carries the span
/// of the offending construct and enough context for a caret render (STYLE
/// E1/G3). Lexical failures are wrapped from [`LexError`].
#[derive(Clone, PartialEq, Eq, Debug, Error)]
pub enum ParseError {
    /// A lexical error surfaced before parsing could proceed.
    #[error(transparent)]
    Lex(#[from] LexError),
    /// The token stream did not match the grammar at this point; `expected`
    /// names what the parser was looking for.
    #[error("syntax error: expected {expected}")]
    Expected {
        /// What the grammar allows here.
        expected: &'static str,
        /// Where the unexpected token is.
        span: Span,
    },
    /// `for N univ` — scoping the universe (grammar action).
    #[error("you cannot set a scope on univ")]
    ScopeOnUniv {
        /// Span of the offending scope entry.
        span: Span,
    },
    /// `for N none` — scoping the empty set.
    #[error("you cannot set a scope on none")]
    ScopeOnNone {
        /// Span of the offending scope entry.
        span: Span,
    },
    /// A range/`..` scope on `Int`/`int`/`seq`, whose size must be exact.
    #[error("cannot specify a growing scope for \"{target}\"")]
    GrowingScope {
        /// The target keyword.
        target: &'static str,
        /// Span of the offending entry.
        span: Span,
    },
    /// `exactly` on `Int`/`int`/`seq`, where exactness is already implied.
    #[error("the exactly keyword is redundant for \"{target}\"")]
    ExactlyRedundant {
        /// The target keyword.
        target: &'static str,
        /// Span of the offending entry.
        span: Span,
    },
    /// `disj a, b = e` — a defined field cannot also be disjoint.
    #[error("defined fields cannot be disjoint")]
    DefinedFieldDisjoint {
        /// Span of the `disj` marker.
        span: Span,
    },
    /// A declared name containing `$` (reserved for skolem names).
    #[error("the name cannot contain the '$' symbol")]
    DollarInName {
        /// Span of the offending name.
        span: Span,
    },
    /// The same `sig` qualifier written twice.
    #[error("the same qualifier cannot be specified more than once for the same sig")]
    DuplicateSigQual {
        /// Span of the duplicate qualifier.
        span: Span,
    },
    /// A `let` variable name containing `/` (it must be unqualified).
    #[error("let variable name cannot contain '/'")]
    LetNameSlash {
        /// Span of the offending name.
        span: Span,
    },
    /// A declared name that is qualified where only a bare identifier fits.
    #[error("declared name cannot be qualified")]
    QualifiedDeclName {
        /// Span of the offending name.
        span: Span,
    },
    /// `enum E {}` — an enum must declare at least one variant.
    #[error("enum body cannot be empty")]
    EmptyEnum {
        /// Span of the enum paragraph.
        span: Span,
    },
    /// A `module` header not at the top of the file.
    #[error("module header must appear before any other paragraph")]
    ModuleHeaderNotFirst {
        /// Span of the misplaced header.
        span: Span,
    },
    /// A scope bound outside the non-negative `u32` range.
    #[error("scope bound must be a non-negative integer")]
    BadScopeNumber {
        /// Span of the offending number.
        span: Span,
    },
}

impl ParseError {
    /// The span every variant carries (or [`Span`]-free lex errors delegate).
    #[must_use]
    pub fn span(&self) -> Span {
        match self {
            Self::Lex(e) => e.span(),
            Self::Expected { span, .. }
            | Self::ScopeOnUniv { span }
            | Self::ScopeOnNone { span }
            | Self::GrowingScope { span, .. }
            | Self::ExactlyRedundant { span, .. }
            | Self::DefinedFieldDisjoint { span }
            | Self::DollarInName { span }
            | Self::DuplicateSigQual { span }
            | Self::LetNameSlash { span }
            | Self::QualifiedDeclName { span }
            | Self::EmptyEnum { span }
            | Self::ModuleHeaderNotFirst { span }
            | Self::BadScopeNumber { span } => *span,
        }
    }
}

/// Parses one `.als` module: lex → cook → parse.
///
/// # Errors
/// Returns the first [`ParseError`] (lexical or syntactic) encountered.
pub fn parse(source: &str, file: FileId) -> Result<Ast, ParseError> {
    let raw = lex(source, file)?;
    let tokens = crate::cook::cook(&raw, source);
    Parser::new(tokens, source).parse_file()
}

/// Parses an already-cooked token stream (the lower-level entry point). The
/// stream must end with [`TokenKind::Eof`] and be cooked ([`cook`]).
///
/// # Errors
/// Returns the first [`ParseError`] encountered.
pub fn parse_tokens(tokens: Vec<Token>, source: &str) -> Result<Ast, ParseError> {
    Parser::new(tokens, source).parse_file()
}

/// Recursive-descent + Pratt parser over a cooked token slice.
struct Parser<'src> {
    tokens: Vec<Token>,
    source: &'src str,
    pos: usize,
    ast: Ast,
}

// -- Precedence table (grammar-doc section 3) -----------------------------
//
// Pratt binding powers: `parse_operand(min_bp)` consumes an infix operator
// only while its left binding power is `>= min_bp`, then recurses at the
// operator's right binding power. Left-assoc tiers use `l < r`; right-assoc
// use `l > r`. Prefix operators bind their operand at a fixed right power so
// that, e.g., `!` (looser than comparisons) grabs `a = b` while `#` (tighter
// than `+`) does not grab `... + b`.
//
// The numbers themselves live in one place, `crate::prec`, shared verbatim
// with the pretty-printer (mt-012) so parser precedence and printer parens
// can never drift.

use crate::prec::{arrow_bp, binary_bp, cmp_bp, BP_NOT, BP_NUMUNOP, BP_TEST, TIER_TEST};

/// One infix operator classified for the Pratt loop.
#[derive(Copy, Clone)]
enum Infix {
    /// A plain [`ExprKind::Binary`] operator.
    Bin(BinOp),
    /// A [`ExprKind::Compare`], possibly negated.
    Cmp(CmpOp, bool),
    /// An [`ExprKind::Arrow`] with optional multiplicities.
    Arrow(Option<Mult>, Option<Mult>),
    /// `=>`/`implies`, which may take an `else` branch.
    Implies,
}

/// Binding powers + classification for an infix operator, or `None` if the
/// token does not continue an expression. The numbers come from
/// [`crate::prec`] (keyed on the resulting operator), the same table the
/// pretty-printer reads.
fn classify_infix(kind: &TokenKind) -> Option<(u8, u8, Infix)> {
    let infix = match kind {
        TokenKind::Or => Infix::Bin(BinOp::Or),
        TokenKind::Iff => Infix::Bin(BinOp::Iff),
        TokenKind::Implies => Infix::Implies,
        TokenKind::And => Infix::Bin(BinOp::And),
        TokenKind::Until => Infix::Bin(BinOp::Until),
        TokenKind::Releases => Infix::Bin(BinOp::Releases),
        TokenKind::Since => Infix::Bin(BinOp::Since),
        TokenKind::Triggered => Infix::Bin(BinOp::Triggered),
        TokenKind::Equals => Infix::Cmp(CmpOp::Eq, false),
        TokenKind::NotEquals => Infix::Cmp(CmpOp::Eq, true),
        TokenKind::In => Infix::Cmp(CmpOp::In, false),
        TokenKind::NotIn => Infix::Cmp(CmpOp::In, true),
        TokenKind::Lt => Infix::Cmp(CmpOp::Lt, false),
        TokenKind::NotLt => Infix::Cmp(CmpOp::Lt, true),
        TokenKind::Gt => Infix::Cmp(CmpOp::Gt, false),
        TokenKind::NotGt => Infix::Cmp(CmpOp::Gt, true),
        TokenKind::Lte => Infix::Cmp(CmpOp::Le, false),
        TokenKind::NotLte => Infix::Cmp(CmpOp::Le, true),
        TokenKind::Gte => Infix::Cmp(CmpOp::Ge, false),
        TokenKind::NotGte => Infix::Cmp(CmpOp::Ge, true),
        TokenKind::Shl => Infix::Bin(BinOp::Shl),
        TokenKind::Sha => Infix::Bin(BinOp::Sha),
        TokenKind::Shr => Infix::Bin(BinOp::Shr),
        TokenKind::Plus => Infix::Bin(BinOp::Union),
        TokenKind::Minus => Infix::Bin(BinOp::Diff),
        TokenKind::FunAdd => Infix::Bin(BinOp::IntAdd),
        TokenKind::FunSub => Infix::Bin(BinOp::IntSub),
        TokenKind::FunMul => Infix::Bin(BinOp::IntMul),
        TokenKind::FunDiv => Infix::Bin(BinOp::IntDiv),
        TokenKind::FunRem => Infix::Bin(BinOp::IntRem),
        TokenKind::PlusPlus => Infix::Bin(BinOp::Override),
        TokenKind::Ampersand => Infix::Bin(BinOp::Intersect),
        TokenKind::Arrow => Infix::Arrow(None, None),
        TokenKind::ArrowMult { lhs, rhs } => Infix::Arrow(*lhs, *rhs),
        TokenKind::DomRestrict => Infix::Bin(BinOp::DomRestrict),
        TokenKind::RangeRestrict => Infix::Bin(BinOp::RanRestrict),
        _ => return None,
    };
    let (lbp, rbp) = match infix {
        Infix::Bin(op) => binary_bp(op),
        Infix::Cmp(op, _) => cmp_bp(op),
        Infix::Arrow(lhs, rhs) => arrow_bp(lhs, rhs),
        // `=>` is right-associative with the dangling-else right power.
        Infix::Implies => binary_bp(BinOp::Implies),
    };
    Some((lbp, rbp, infix))
}

impl<'src> Parser<'src> {
    fn new(tokens: Vec<Token>, source: &'src str) -> Self {
        Self {
            tokens,
            source,
            pos: 0,
            ast: Ast::default(),
        }
    }

    // -- Cursor primitives ------------------------------------------------

    fn cur(&self) -> &TokenKind {
        &self.tokens[self.pos].kind
    }

    fn cur_span(&self) -> Span {
        self.tokens[self.pos].span
    }

    fn peek(&self, ahead: usize) -> Option<&TokenKind> {
        self.tokens.get(self.pos + ahead).map(|t| &t.kind)
    }

    fn at(&self, kind: &TokenKind) -> bool {
        self.cur() == kind
    }

    fn bump(&mut self) -> Token {
        let tok = self.tokens[self.pos].clone();
        if !matches!(tok.kind, TokenKind::Eof) {
            self.pos += 1;
        }
        tok
    }

    fn eat(&mut self, kind: &TokenKind) -> bool {
        if self.at(kind) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn expect(&mut self, kind: &TokenKind, expected: &'static str) -> Result<Token, ParseError> {
        if self.at(kind) {
            Ok(self.bump())
        } else {
            Err(self.expected(expected))
        }
    }

    fn expect_ident(&mut self, expected: &'static str) -> Result<Token, ParseError> {
        if matches!(self.cur(), TokenKind::Ident) {
            Ok(self.bump())
        } else {
            Err(self.expected(expected))
        }
    }

    fn expected(&self, expected: &'static str) -> ParseError {
        ParseError::Expected {
            expected,
            span: self.cur_span(),
        }
    }

    // -- Arena / span helpers ---------------------------------------------

    fn alloc(&mut self, kind: ExprKind, span: Span) -> ExprId {
        self.ast.exprs.alloc(Expr { kind, span })
    }

    fn espan(&self, id: ExprId) -> Span {
        self.ast.exprs[id].span
    }

    fn ident_of(&self, tok: &Token) -> Ident {
        Ident {
            text: self.source[tok.span.start as usize..tok.span.end as usize].to_owned(),
            span: tok.span,
        }
    }

    /// A synthesized single-segment name (keyword/cooked builtins whose text
    /// is not a verbatim source slice, e.g. `pred/totalOrder`, `fun/min`).
    fn synth_name(&mut self, text: &str, span: Span) -> ExprId {
        let name = QualName {
            segments: vec![Ident {
                text: text.to_owned(),
                span,
            }],
            span,
        };
        self.alloc(ExprKind::Name(name), span)
    }

    // -- File / paragraphs ------------------------------------------------

    fn parse_file(mut self) -> Result<Ast, ParseError> {
        loop {
            match self.cur() {
                TokenKind::Eof => break,
                TokenKind::Module => self.parse_module_header()?,
                TokenKind::Open => self.parse_open(false)?,
                TokenKind::Fact => self.parse_fact()?,
                TokenKind::Assert => self.parse_assert()?,
                TokenKind::Enum => self.parse_enum(false)?,
                TokenKind::Pred => self.parse_pred(false)?,
                TokenKind::Fun => self.parse_fun(false)?,
                TokenKind::Let => self.parse_macro(false)?,
                TokenKind::Run | TokenKind::Check => self.parse_commands()?,
                TokenKind::Private => self.parse_private_paragraph()?,
                TokenKind::Abstract
                | TokenKind::Var
                | TokenKind::Lone
                | TokenKind::One
                | TokenKind::Some
                | TokenKind::Sig => self.parse_sig()?,
                _ => return Err(self.expected("a paragraph (sig, fact, pred, run, …)")),
            }
        }
        Ok(self.ast)
    }

    /// Dispatch for a paragraph led by `private` (a shared qualifier for
    /// `open`, `enum`, `pred`, `fun`, `let`, and `sig`).
    fn parse_private_paragraph(&mut self) -> Result<(), ParseError> {
        match self.peek(1) {
            Some(TokenKind::Open) => self.parse_open(true),
            Some(TokenKind::Enum) => self.parse_enum(true),
            Some(TokenKind::Pred) => self.parse_pred(true),
            Some(TokenKind::Fun) => self.parse_fun(true),
            Some(TokenKind::Let) => self.parse_macro(true),
            // `private` is otherwise a sig qualifier.
            _ => self.parse_sig(),
        }
    }

    fn push_para(&mut self, para: Para) {
        let id = self.ast.paras.alloc(para);
        self.ast.paragraphs.push(id);
    }

    /// `module qualname [params]`. Must precede every other paragraph.
    fn parse_module_header(&mut self) -> Result<(), ParseError> {
        let kw = self.bump();
        if self.ast.header.is_some() || !self.ast.paragraphs.is_empty() {
            return Err(ParseError::ModuleHeaderNotFirst { span: kw.span });
        }
        let name = self.parse_qual_name()?;
        Self::check_no_dollar(&name)?;
        let mut params = Vec::new();
        let mut end = name.span;
        if self.eat(&TokenKind::LBracket) {
            loop {
                let is_exact = self.eat(&TokenKind::Exactly);
                let pname = self.parse_qual_name()?;
                Self::check_no_dollar(&pname)?;
                params.push(ModuleParam {
                    name: pname,
                    is_exact,
                });
                if !self.eat(&TokenKind::Comma) {
                    break;
                }
            }
            end = self.expect(&TokenKind::RBracket, "`]`")?.span;
        }
        self.ast.header = Some(ModuleHeader {
            name,
            params,
            span: kw.span.merge(end),
        });
        Ok(())
    }

    /// `[private] open qualname [ sigrefs ] [as alias]`.
    fn parse_open(&mut self, is_private: bool) -> Result<(), ParseError> {
        let start = self.cur_span();
        if is_private {
            self.bump(); // private
        }
        self.bump(); // open
        let module = self.parse_qual_name()?;
        Self::check_no_dollar(&module)?;
        let mut args = Vec::new();
        let mut end = module.span;
        if self.eat(&TokenKind::LBracket) {
            if !self.at(&TokenKind::RBracket) {
                args.push(self.parse_sigref()?);
                while self.eat(&TokenKind::Comma) {
                    args.push(self.parse_sigref()?);
                }
            }
            end = self.expect(&TokenKind::RBracket, "`]`")?.span;
        }
        let mut alias = None;
        if self.eat(&TokenKind::As) {
            let tok = self.expect_ident("an alias name")?;
            end = tok.span;
            alias = Some(self.ident_of(&tok));
        }
        self.push_para_open(Open {
            module,
            args,
            alias,
            is_private,
            span: start.merge(end),
        });
        Ok(())
    }

    fn push_para_open(&mut self, open: Open) {
        self.ast.opens.push(open);
    }

    /// `enum Name { A, B, C }` — `private` is accepted and dropped (the AST
    /// has no visibility on enums).
    fn parse_enum(&mut self, is_private: bool) -> Result<(), ParseError> {
        let start = self.cur_span();
        if is_private {
            self.bump();
        }
        self.bump(); // enum
        let name = self.parse_decl_ident()?;
        self.expect(&TokenKind::LBrace, "`{`")?;
        let mut variants = Vec::new();
        if !self.at(&TokenKind::RBrace) {
            variants.push(self.parse_decl_ident()?);
            while self.eat(&TokenKind::Comma) {
                variants.push(self.parse_decl_ident()?);
            }
        }
        let end = self.expect(&TokenKind::RBrace, "`}`")?.span;
        let span = start.merge(end);
        if variants.is_empty() {
            return Err(ParseError::EmptyEnum { span });
        }
        self.push_para(Para::Enum(EnumDecl {
            name,
            variants,
            span,
        }));
        Ok(())
    }

    /// `fact [name|"str"] { body }`.
    fn parse_fact(&mut self) -> Result<(), ParseError> {
        let kw = self.bump();
        let name = self.parse_para_name()?;
        let body = self.parse_block()?;
        let span = kw.span.merge(self.espan(body));
        self.push_para(Para::Fact(FactDecl { name, body, span }));
        Ok(())
    }

    /// `assert [name|"str"] { body }`.
    fn parse_assert(&mut self) -> Result<(), ParseError> {
        let kw = self.bump();
        let name = self.parse_para_name()?;
        let body = self.parse_block()?;
        let span = kw.span.merge(self.espan(body));
        self.push_para(Para::Assert(crate::ast::AssertDecl { name, body, span }));
        Ok(())
    }

    /// The optional identifier-or-string name of a fact/assert.
    fn parse_para_name(&mut self) -> Result<Option<ParaName>, ParseError> {
        match self.cur() {
            TokenKind::LBrace => Ok(None),
            TokenKind::Str(value) => {
                let value = value.clone();
                let span = self.cur_span();
                self.bump();
                Ok(Some(ParaName::Str { value, span }))
            }
            _ => Ok(Some(ParaName::Ident(self.parse_decl_ident()?))),
        }
    }

    /// `[private] pred [Receiver.]name [params] { body }`.
    fn parse_pred(&mut self, is_private: bool) -> Result<(), ParseError> {
        let start = self.cur_span();
        if is_private {
            self.bump();
        }
        self.bump(); // pred
        let (receiver, name) = self.parse_receiver_name()?;
        let params = self.parse_param_decls()?;
        let body = self.parse_block()?;
        let span = start.merge(self.espan(body));
        self.push_para(Para::Pred(PredDecl {
            name,
            receiver,
            params,
            body,
            is_private,
            span,
        }));
        Ok(())
    }

    /// `[private] fun [Receiver.]name [params] : result { body }`.
    fn parse_fun(&mut self, is_private: bool) -> Result<(), ParseError> {
        let start = self.cur_span();
        if is_private {
            self.bump();
        }
        self.bump(); // fun
        let (receiver, name) = self.parse_receiver_name()?;
        let params = self.parse_param_decls()?;
        self.expect(&TokenKind::Colon, "`:` and a result type")?;
        let returns = self.parse_expr()?;
        let returns = self.apply_mult(returns);
        let body = self.parse_block()?;
        let span = start.merge(self.espan(body));
        self.push_para(Para::Fun(FunDecl {
            name,
            receiver,
            params,
            returns,
            body,
            is_private,
            span,
        }));
        Ok(())
    }

    /// Optional `Receiver.` then the pred/fun name (an identifier). The
    /// receiver is a sig reference, so it may be a builtin (`fun String.cat`).
    fn parse_receiver_name(&mut self) -> Result<(Option<QualName>, Ident), ParseError> {
        let first = self.parse_sigref()?;
        if self.eat(&TokenKind::Dot) {
            let name = self.parse_decl_ident()?;
            Ok((Some(first), name))
        } else {
            Ok((None, Self::qual_to_ident(first)?))
        }
    }

    /// `( decls )` / `[ decls ]` / nothing.
    fn parse_param_decls(&mut self) -> Result<Vec<DeclId>, ParseError> {
        if self.eat(&TokenKind::LParen) {
            let decls = self.parse_decl_seq(&TokenKind::RParen)?;
            self.expect(&TokenKind::RParen, "`)`")?;
            Ok(decls)
        } else if self.eat(&TokenKind::LBracket) {
            let decls = self.parse_decl_seq(&TokenKind::RBracket)?;
            self.expect(&TokenKind::RBracket, "`]`")?;
            Ok(decls)
        } else {
            Ok(Vec::new())
        }
    }

    /// `[private] let name [params] (= expr | { block })`.
    fn parse_macro(&mut self, is_private: bool) -> Result<(), ParseError> {
        let start = self.cur_span();
        if is_private {
            self.bump();
        }
        self.bump(); // let
        let name = self.parse_decl_ident()?;
        let params = self.parse_macro_params()?;
        let body = if self.eat(&TokenKind::Equals) {
            self.parse_expr()?
        } else if self.at(&TokenKind::LBrace) {
            self.parse_block()?
        } else {
            return Err(self.expected("`=` or `{` (a macro body)"));
        };
        let span = start.merge(self.espan(body));
        self.push_para(Para::Macro(MacroDecl {
            name,
            params,
            body,
            is_private,
            span,
        }));
        Ok(())
    }

    /// `( names )` / `[ names ]` / nothing — plain macro parameter names.
    fn parse_macro_params(&mut self) -> Result<Vec<Ident>, ParseError> {
        let close = if self.eat(&TokenKind::LParen) {
            TokenKind::RParen
        } else if self.eat(&TokenKind::LBracket) {
            TokenKind::RBracket
        } else {
            return Ok(Vec::new());
        };
        let mut names = Vec::new();
        if !self.at(&close) {
            names.push(self.parse_decl_ident()?);
            while self.eat(&TokenKind::Comma) {
                names.push(self.parse_decl_ident()?);
            }
        }
        self.expect(&close, "`)` or `]`")?;
        Ok(names)
    }

    // -- Sigs -------------------------------------------------------------

    /// `[quals] sig A, B [extends P | in Ps | = Ps] { fields } [appended fact]`.
    fn parse_sig(&mut self) -> Result<(), ParseError> {
        let start = self.cur_span();
        let qual = self.parse_sig_quals()?;
        self.expect(&TokenKind::Sig, "`sig`")?;
        let mut names = vec![self.parse_decl_ident()?];
        while self.eat(&TokenKind::Comma) {
            names.push(self.parse_decl_ident()?);
        }
        let parent = self.parse_sig_parent()?;
        self.expect(&TokenKind::LBrace, "`{`")?;
        let fields = self.parse_decl_seq(&TokenKind::RBrace)?;
        let mut end = self.expect(&TokenKind::RBrace, "`}`")?.span;
        let fact = if self.at(&TokenKind::LBrace) {
            let block = self.parse_block()?;
            end = self.espan(block);
            Some(block)
        } else {
            None
        };
        self.push_para(Para::Sig(SigDecl {
            qual,
            names,
            parent,
            fields,
            fact,
            span: start.merge(end),
        }));
        Ok(())
    }

    /// Zero or more `sig` qualifiers in any order, each at most once.
    fn parse_sig_quals(&mut self) -> Result<SigQual, ParseError> {
        let mut qual = SigQual::default();
        loop {
            let span = self.cur_span();
            match self.cur() {
                TokenKind::Abstract => set_flag(&mut qual.is_abstract, span)?,
                TokenKind::Var => set_flag(&mut qual.is_var, span)?,
                TokenKind::Private => set_flag(&mut qual.is_private, span)?,
                TokenKind::Lone => set_mult(&mut qual.mult, SigMult::Lone, span)?,
                TokenKind::One => set_mult(&mut qual.mult, SigMult::One, span)?,
                TokenKind::Some => set_mult(&mut qual.mult, SigMult::Some, span)?,
                _ => break,
            }
            self.bump();
        }
        Ok(qual)
    }

    /// `extends P` / `in P + …` / `= P + …` / nothing.
    fn parse_sig_parent(&mut self) -> Result<SigParent, ParseError> {
        if self.eat(&TokenKind::Extends) {
            Ok(SigParent::Extends(self.parse_sigref()?))
        } else if self.eat(&TokenKind::In) {
            Ok(SigParent::In(self.parse_sigref_union()?))
        } else if self.eat(&TokenKind::Equals) {
            Ok(SigParent::Eq(self.parse_sigref_union()?))
        } else {
            Ok(SigParent::None)
        }
    }

    /// `SigRef (+ SigRef)*`.
    fn parse_sigref_union(&mut self) -> Result<Vec<QualName>, ParseError> {
        let mut refs = vec![self.parse_sigref()?];
        while self.eat(&TokenKind::Plus) {
            refs.push(self.parse_sigref()?);
        }
        Ok(refs)
    }

    // -- Declarations -----------------------------------------------------

    /// Field/param decl list with the reference's empty-slot tolerance
    /// (leading/trailing/double commas skipped), terminated by `close`.
    fn parse_decl_seq(&mut self, close: &TokenKind) -> Result<Vec<DeclId>, ParseError> {
        let mut decls = Vec::new();
        loop {
            while self.eat(&TokenKind::Comma) {}
            if self.at(close) {
                break;
            }
            decls.push(self.parse_decl(true)?);
            if !self.at(&TokenKind::Comma) && !self.at(close) {
                return Err(self.expected("`,` or a closing delimiter"));
            }
        }
        Ok(decls)
    }

    /// A comma-separated binding list for quantifiers (`Declp`, allows `=`)
    /// or comprehensions (`Declz`, `allow_defined = false`), ending at the
    /// body (`|`/`{`) or `}`.
    fn parse_binding_seq(&mut self, allow_defined: bool) -> Result<Vec<DeclId>, ParseError> {
        let mut decls = vec![self.parse_decl(allow_defined)?];
        while self.eat(&TokenKind::Comma) {
            decls.push(self.parse_decl(allow_defined)?);
        }
        Ok(decls)
    }

    /// One declaration: `[var] [private] [disj] names : [disj] bound` or a
    /// defined `names = expr` (fields only). Multiplicity conversion (the
    /// reference's `mult()`) is applied to the `:` bound.
    fn parse_decl(&mut self, allow_defined: bool) -> Result<DeclId, ParseError> {
        let start = self.cur_span();
        let is_var = self.eat(&TokenKind::Var);
        let is_private = self.eat(&TokenKind::Private);
        let disj_span = self.at(&TokenKind::Disj).then(|| self.cur_span());
        let is_disj = disj_span.is_some();
        if is_disj {
            self.bump();
        }
        let names = self.parse_decl_names()?;
        let (bound, is_bound_disj) = if self.at(&TokenKind::Equals) {
            self.parse_defined_bound(allow_defined, is_disj, disj_span)?
        } else if self.eat(&TokenKind::Colon) {
            let is_bound_disj = self.eat(&TokenKind::Disj);
            let bound = self.parse_expr()?;
            (self.apply_mult(bound), is_bound_disj)
        } else {
            return Err(self.expected("`:` or `=` in a declaration"));
        };
        let span = start.merge(self.espan(bound));
        Ok(self.ast.decls.alloc(Decl {
            is_disj,
            is_bound_disj,
            is_var,
            is_private,
            names,
            bound,
            span,
        }))
    }

    /// The `= expr` (defined) bound: rejects `disj` on either side and, for
    /// comprehensions, rejects the defined form entirely.
    fn parse_defined_bound(
        &mut self,
        allow_defined: bool,
        is_disj: bool,
        disj_span: Option<Span>,
    ) -> Result<(ExprId, bool), ParseError> {
        if !allow_defined {
            return Err(self.expected("`:` (defined declarations are not allowed here)"));
        }
        if let Some(span) = disj_span {
            if is_disj {
                return Err(ParseError::DefinedFieldDisjoint { span });
            }
        }
        self.bump(); // =
        if self.at(&TokenKind::Disj) {
            return Err(ParseError::DefinedFieldDisjoint {
                span: self.cur_span(),
            });
        }
        let value = self.parse_expr()?;
        let span = self.espan(value);
        let bound = self.alloc(
            ExprKind::Unary {
                op: UnOp::ExactlyOf,
                expr: value,
            },
            span,
        );
        Ok((bound, false))
    }

    /// The greedy `ID (, ID)*` name list of a single declaration (stops at
    /// `:`/`=`; a comma not followed by an identifier belongs to the
    /// enclosing decl list).
    fn parse_decl_names(&mut self) -> Result<Vec<Ident>, ParseError> {
        let mut names = vec![self.parse_decl_ident()?];
        while self.at(&TokenKind::Comma) && matches!(self.peek(1), Some(TokenKind::Ident)) {
            self.bump();
            names.push(self.parse_decl_ident()?);
        }
        Ok(names)
    }

    /// A single declared identifier, rejecting `$` (grammar action `nod`).
    fn parse_decl_ident(&mut self) -> Result<Ident, ParseError> {
        let tok = self.expect_ident("a name")?;
        let id = self.ident_of(&tok);
        if id.text.contains('$') {
            return Err(ParseError::DollarInName { span: id.span });
        }
        Ok(id)
    }

    // -- Commands & scopes ------------------------------------------------

    /// One `run`/`check` paragraph plus any `=> run …` follow-up chain.
    fn parse_commands(&mut self) -> Result<(), ParseError> {
        let cmd = self.parse_command(false)?;
        self.push_para(Para::Cmd(cmd));
        while self.at(&TokenKind::Implies)
            && matches!(self.peek(1), Some(TokenKind::Run | TokenKind::Check))
        {
            self.bump(); // =>
            let cmd = self.parse_command(true)?;
            self.push_para(Para::Cmd(cmd));
        }
        Ok(())
    }

    fn parse_command(&mut self, is_followup: bool) -> Result<CmdDecl, ParseError> {
        let kw = self.bump();
        let kind = match kw.kind {
            TokenKind::Run => CmdKind::Run,
            // Only `run`/`check` reach here (checked by the caller).
            _ => CmdKind::Check,
        };
        let (label, target) = self.parse_command_target()?;
        let scope = self.parse_scope()?;
        let (expect, end) = self.parse_expect(scope.as_ref().map_or(kw.span, |s| s.span))?;
        let span = kw.span.merge(end);
        Ok(CmdDecl {
            label,
            kind,
            target,
            scope,
            expect,
            is_followup,
            span,
        })
    }

    /// The optional `label` and the `{ block }` or `name` target.
    fn parse_command_target(&mut self) -> Result<(Option<Ident>, CmdTarget), ParseError> {
        if self.at(&TokenKind::LBrace) {
            let block = self.parse_block()?;
            return Ok((None, CmdTarget::Block(block)));
        }
        let first = self.parse_qual_name()?;
        if self.at(&TokenKind::LBrace) {
            let label = Self::qual_to_ident(first)?;
            let block = self.parse_block()?;
            Ok((Some(label), CmdTarget::Block(block)))
        } else if self.starts_name() {
            let label = Self::qual_to_ident(first)?;
            let target = self.parse_qual_name()?;
            Ok((Some(label), CmdTarget::Name(target)))
        } else {
            Ok((None, CmdTarget::Name(first)))
        }
    }

    /// `expect N`, if present; returns the annotation and the running end
    /// span. The reference accepts any integer here — only 0 and 1 assert a
    /// verdict, anything else is carried as [`Expect::Other`].
    fn parse_expect(&mut self, prev_end: Span) -> Result<(Option<Expect>, Span), ParseError> {
        if !self.at(&TokenKind::Expect) {
            return Ok((None, prev_end));
        }
        self.bump();
        let tok = self.bump();
        let TokenKind::Number(n) = tok.kind else {
            return Err(ParseError::Expected {
                expected: "a number after `expect`",
                span: tok.span,
            });
        };
        let expect = match n {
            0 => Expect::Unsat,
            1 => Expect::Sat,
            other => Expect::Other(other),
        };
        Ok((Some(expect), tok.span))
    }

    /// `for N` / `for N but ts,+` / `for ts,+`, or nothing.
    fn parse_scope(&mut self) -> Result<Option<Scope>, ParseError> {
        if !self.at(&TokenKind::For) {
            return Ok(None);
        }
        let for_tok = self.bump();
        let first = self.parse_type_number()?;
        let mut entries = Vec::new();
        let default;
        let mut end;
        if self.starts_scope_target() {
            let entry = self.finish_typescope(first)?;
            end = entry.span;
            entries.push(entry);
            while self.eat(&TokenKind::Comma) {
                let tn = self.parse_type_number()?;
                let entry = self.finish_typescope(tn)?;
                end = entry.span;
                entries.push(entry);
            }
            default = None;
        } else if self.at(&TokenKind::But) {
            if !first.is_plain() {
                return Err(ParseError::Expected {
                    expected: "a plain numeric default scope before `but`",
                    span: first.span,
                });
            }
            self.bump(); // but
            loop {
                let tn = self.parse_type_number()?;
                let entry = self.finish_typescope(tn)?;
                end = entry.span;
                entries.push(entry);
                if !self.eat(&TokenKind::Comma) {
                    break;
                }
            }
            default = Some(first.start);
        } else {
            if !first.is_plain() {
                return Err(self.expected("a scope target"));
            }
            default = Some(first.start);
            end = first.span;
        }
        Ok(Some(Scope {
            default,
            entries,
            span: for_tok.span.merge(end),
        }))
    }

    /// `[exactly] N [.. [M]] [: I]` — the numeric part of a scope entry.
    fn parse_type_number(&mut self) -> Result<RawScope, ParseError> {
        let start = self.cur_span();
        let is_exact = self.eat(&TokenKind::Exactly);
        let (num_start, mut end) = self.expect_scope_number()?;
        let mut scope_end = ScopeEnd::Same;
        if self.at(&TokenKind::Dot) && matches!(self.peek(1), Some(TokenKind::Dot)) {
            self.bump();
            self.bump();
            if matches!(self.cur(), TokenKind::Number(_)) {
                let (m, m_end) = self.expect_scope_number()?;
                end = m_end;
                scope_end = ScopeEnd::Bounded(m);
            } else {
                scope_end = ScopeEnd::Unbounded;
            }
        }
        let mut increment = None;
        if self.eat(&TokenKind::Colon) {
            let (i, i_end) = self.expect_scope_number()?;
            end = i_end;
            increment = Some(i);
            // `N : I` (no range) means unbounded growth from N (grammar
            // `NUMBER COLON NUMBER` sets the ending scope to +∞).
            if matches!(scope_end, ScopeEnd::Same) {
                scope_end = ScopeEnd::Unbounded;
            }
        }
        Ok(RawScope {
            is_exact,
            start: num_start,
            end: scope_end,
            increment,
            span: start.merge(end),
        })
    }

    /// Reads a non-negative `u32` scope bound; returns `(value, span)`.
    fn expect_scope_number(&mut self) -> Result<(u32, Span), ParseError> {
        let span = self.cur_span();
        let TokenKind::Number(n) = *self.cur() else {
            return Err(self.expected("a scope number"));
        };
        let Ok(value) = u32::try_from(n) else {
            return Err(ParseError::BadScopeNumber { span });
        };
        self.bump();
        Ok((value, span))
    }

    /// Attaches a target to a parsed [`RawScope`], applying the grammar's
    /// per-target parse checks.
    fn finish_typescope(&mut self, raw: RawScope) -> Result<TypeScope, ParseError> {
        let tspan = self.cur_span();
        let span = raw.span.merge(tspan);
        match self.cur() {
            TokenKind::Univ => Err(ParseError::ScopeOnUniv { span }),
            TokenKind::None => Err(ParseError::ScopeOnNone { span }),
            TokenKind::Int | TokenKind::IntCast => self.exact_only_scope(raw, "Int", span),
            TokenKind::Seq if !matches!(self.peek(1), Some(TokenKind::Slash)) => {
                self.exact_only_scope(raw, "seq", span)
            }
            TokenKind::StringKw => Ok(self.ranged_scope(raw, ScopeTarget::Str, span)),
            TokenKind::Steps => Ok(self.ranged_scope(raw, ScopeTarget::Steps, span)),
            TokenKind::Ident | TokenKind::This | TokenKind::Seq => {
                let name = self.parse_qual_name()?;
                let span = raw.span.merge(name.span);
                Ok(Self::sig_scope(raw, ScopeTarget::Sig(name), span))
            }
            _ => Err(self.expected("a scope target")),
        }
    }

    /// A scope on `Int`/`int`/`seq`, which must be exact and non-growing.
    fn exact_only_scope(
        &mut self,
        raw: RawScope,
        target: &'static str,
        span: Span,
    ) -> Result<TypeScope, ParseError> {
        if raw.is_growing() {
            return Err(ParseError::GrowingScope { target, span });
        }
        if raw.effective_exact() {
            return Err(ParseError::ExactlyRedundant { target, span });
        }
        self.bump(); // the target keyword
        let scope_target = if target == "seq" {
            ScopeTarget::Seq
        } else {
            ScopeTarget::Int
        };
        Ok(TypeScope {
            is_exact: false,
            start: raw.start,
            end: ScopeEnd::Same,
            increment: None,
            target: scope_target,
            span,
        })
    }

    /// A ranged scope on a keyword target (`String`/`steps`).
    fn ranged_scope(&mut self, raw: RawScope, target: ScopeTarget, span: Span) -> TypeScope {
        self.bump(); // the keyword
        TypeScope {
            is_exact: raw.effective_exact(),
            start: raw.start,
            end: raw.end,
            increment: raw.increment,
            target,
            span,
        }
    }

    /// A ranged scope on a signature reference (target already consumed).
    fn sig_scope(raw: RawScope, target: ScopeTarget, span: Span) -> TypeScope {
        TypeScope {
            is_exact: raw.effective_exact(),
            start: raw.start,
            end: raw.end,
            increment: raw.increment,
            target,
            span,
        }
    }

    /// Whether the current token can begin a scope target.
    fn starts_scope_target(&self) -> bool {
        matches!(
            self.cur(),
            TokenKind::Ident
                | TokenKind::This
                | TokenKind::Univ
                | TokenKind::None
                | TokenKind::Int
                | TokenKind::IntCast
                | TokenKind::Seq
                | TokenKind::StringKw
                | TokenKind::Steps
        )
    }

    // -- Expressions (Pratt core) -----------------------------------------

    /// A full expression, including the weakest-precedence `;` sequencing
    /// (right-assoc), kept as a [`BinOp::Seq`] node.
    fn parse_expr(&mut self) -> Result<ExprId, ParseError> {
        let lhs = self.parse_expr_no_seq()?;
        if self.at(&TokenKind::Semi) {
            self.bump();
            let rhs = self.parse_expr()?;
            let span = self.espan(lhs).merge(self.espan(rhs));
            Ok(self.alloc(
                ExprKind::Binary {
                    op: BinOp::Seq,
                    lhs,
                    rhs,
                },
                span,
            ))
        } else {
            Ok(lhs)
        }
    }

    fn parse_expr_no_seq(&mut self) -> Result<ExprId, ParseError> {
        self.parse_operand(0)
    }

    /// The precedence-climbing core. A binder (`let`/quantifier) may open any
    /// operand and then consumes maximally right (grammar-doc section 3.1);
    /// binders are exempt from the prefix tier gate below.
    fn parse_operand(&mut self, min_bp: u8) -> Result<ExprId, ParseError> {
        if self.starts_binder() {
            return self.parse_binder();
        }
        let mut lhs = self.parse_prefix(min_bp)?;
        while let Some((lbp, rbp, infix)) = classify_infix(self.cur()) {
            if lbp < min_bp {
                break;
            }
            self.bump();
            lhs = self.build_infix(infix, lhs, rbp)?;
        }
        Ok(lhs)
    }

    /// Builds one infix application whose operator was just consumed.
    fn build_infix(&mut self, infix: Infix, lhs: ExprId, rbp: u8) -> Result<ExprId, ParseError> {
        match infix {
            Infix::Implies => self.build_implies(lhs, rbp),
            Infix::Arrow(lhs_mult, rhs_mult) => {
                let rhs = self.parse_operand(rbp)?;
                let span = self.espan(lhs).merge(self.espan(rhs));
                Ok(self.alloc(
                    ExprKind::Arrow {
                        lhs,
                        lhs_mult,
                        rhs_mult,
                        rhs,
                    },
                    span,
                ))
            }
            Infix::Cmp(op, negated) => {
                let mut rhs = self.parse_operand(rbp)?;
                if matches!(op, CmpOp::In) {
                    rhs = self.apply_mult(rhs);
                }
                let span = self.espan(lhs).merge(self.espan(rhs));
                Ok(self.alloc(
                    ExprKind::Compare {
                        op,
                        negated,
                        lhs,
                        rhs,
                    },
                    span,
                ))
            }
            Infix::Bin(op) => {
                let rhs = self.parse_operand(rbp)?;
                let span = self.espan(lhs).merge(self.espan(rhs));
                Ok(self.alloc(ExprKind::Binary { op, lhs, rhs }, span))
            }
        }
    }

    /// `a => b` or `a => b else c` (dangling `else` binds to the nearest
    /// unmatched `=>`, right-assoc).
    fn build_implies(&mut self, cond: ExprId, rbp: u8) -> Result<ExprId, ParseError> {
        let then_branch = self.parse_operand(rbp)?;
        if self.eat(&TokenKind::Else) {
            let else_branch = self.parse_operand(rbp)?;
            let span = self.espan(cond).merge(self.espan(else_branch));
            Ok(self.alloc(
                ExprKind::IfThenElse {
                    cond,
                    then_branch,
                    else_branch,
                },
                span,
            ))
        } else {
            let span = self.espan(cond).merge(self.espan(then_branch));
            Ok(self.alloc(
                ExprKind::Binary {
                    op: BinOp::Implies,
                    lhs: cond,
                    rhs: then_branch,
                },
                span,
            ))
        }
    }

    /// Prefix operators that sit at specific precedence tiers (`!`, temporal
    /// unaries, the set tests, `# sum int`), falling through to the
    /// tightest tier (dot/bracket/closure/atom).
    ///
    /// Each prefix carries a *tier*: the loosest operand slot it may open
    /// (jar-verified 2026-07-15: `a & !b`, `a + no b`, `x in one A`,
    /// `a ++ #b`, `no no a` all rejected; `a && !b`, `! no a`,
    /// `a until !b`, `a fun/mul #b` accepted). A prefix whose tier is below
    /// the demanded `min_bp` cannot start this operand — exactly the
    /// reference's production stratification, where e.g. `!` produces a
    /// `UnaryExpr` and so cannot appear where a `ShiftExpr` is required.
    fn parse_prefix(&mut self, min_bp: u8) -> Result<ExprId, ParseError> {
        let start = self.cur_span();
        let (op, tier, rbp) = match self.cur() {
            TokenKind::Not => (UnOp::Not, BP_NOT, BP_NOT),
            TokenKind::Always => (UnOp::Always, BP_NOT, BP_NOT),
            TokenKind::Eventually => (UnOp::Eventually, BP_NOT, BP_NOT),
            TokenKind::After => (UnOp::After, BP_NOT, BP_NOT),
            TokenKind::Before => (UnOp::Before, BP_NOT, BP_NOT),
            TokenKind::Historically => (UnOp::Historically, BP_NOT, BP_NOT),
            TokenKind::Once => (UnOp::Once, BP_NOT, BP_NOT),
            TokenKind::No => (UnOp::No, TIER_TEST, BP_TEST),
            TokenKind::Some => (UnOp::Some, TIER_TEST, BP_TEST),
            TokenKind::Lone => (UnOp::Lone, TIER_TEST, BP_TEST),
            TokenKind::One => (UnOp::One, TIER_TEST, BP_TEST),
            TokenKind::Set => (UnOp::SetOf, TIER_TEST, BP_TEST),
            TokenKind::Seq if !matches!(self.peek(1), Some(TokenKind::Slash)) => {
                (UnOp::SeqOf, TIER_TEST, BP_TEST)
            }
            TokenKind::Hash => (UnOp::Card, BP_NUMUNOP, BP_NUMUNOP),
            TokenKind::IntCast if !matches!(self.peek(1), Some(TokenKind::LBracket)) => {
                (UnOp::IntOf, BP_NUMUNOP, BP_NUMUNOP)
            }
            TokenKind::Sum if !matches!(self.peek(1), Some(TokenKind::LBracket)) => {
                (UnOp::SumOf, BP_NUMUNOP, BP_NUMUNOP)
            }
            _ => return self.parse_postfix(),
        };
        if tier < min_bp {
            return Err(
                self.expected("an operand (this prefix operator binds too loosely to appear here)")
            );
        }
        self.bump();
        let operand = self.parse_operand(rbp)?;
        let span = start.merge(self.espan(operand));
        Ok(self.alloc(ExprKind::Unary { op, expr: operand }, span))
    }

    /// Dot join and box join, left-associative and interleaved (tier 19).
    fn parse_postfix(&mut self) -> Result<ExprId, ParseError> {
        let mut lhs = self.parse_unop()?;
        loop {
            match self.cur() {
                TokenKind::LBracket => lhs = self.parse_box_join(lhs)?,
                TokenKind::Dot => {
                    self.bump();
                    let rhs = self.parse_dot_rhs()?;
                    let span = self.espan(lhs).merge(self.espan(rhs));
                    lhs = self.alloc(
                        ExprKind::Binary {
                            op: BinOp::Join,
                            lhs,
                            rhs,
                        },
                        span,
                    );
                }
                _ => break,
            }
        }
        Ok(lhs)
    }

    /// `target[a, b, …]`; `target[]` is just `target` (grammar's empty
    /// argument fold).
    fn parse_box_join(&mut self, target: ExprId) -> Result<ExprId, ParseError> {
        self.bump(); // [
        let args = self.parse_expr_list(&TokenKind::RBracket)?;
        let close = self.expect(&TokenKind::RBracket, "`]`")?;
        if args.is_empty() {
            Ok(target)
        } else {
            let span = self.espan(target).merge(close.span);
            Ok(self.alloc(ExprKind::BoxJoin { target, args }, span))
        }
    }

    /// The right operand of `.`: a builtin keyword name, a binder, or a
    /// tier-20 term (`a.~r`, `a.b'`).
    fn parse_dot_rhs(&mut self) -> Result<ExprId, ParseError> {
        let span = self.cur_span();
        match self.cur() {
            TokenKind::Disj => Ok(self.synth_after_bump("disj", span)),
            TokenKind::TotalOrder => Ok(self.synth_after_bump("pred/totalOrder", span)),
            TokenKind::IntCast => Ok(self.synth_after_bump("int", span)),
            TokenKind::Sum => Ok(self.synth_after_bump("sum", span)),
            _ if self.starts_binder() => self.parse_binder(),
            _ => self.parse_unop(),
        }
    }

    fn synth_after_bump(&mut self, text: &str, span: Span) -> ExprId {
        self.bump();
        self.synth_name(text, span)
    }

    /// Prefix closure operators `~ ^ *` (bind tighter than dot) with postfix
    /// `'` applied afterwards, so `~a'` ≡ `(~a)'`.
    fn parse_unop(&mut self) -> Result<ExprId, ParseError> {
        let mut e = self.parse_closure()?;
        while self.at(&TokenKind::Prime) {
            let prime = self.bump();
            let span = self.espan(e).merge(prime.span);
            e = self.alloc(
                ExprKind::Unary {
                    op: UnOp::Prime,
                    expr: e,
                },
                span,
            );
        }
        Ok(e)
    }

    fn parse_closure(&mut self) -> Result<ExprId, ParseError> {
        let start = self.cur_span();
        let op = match self.cur() {
            TokenKind::Tilde => UnOp::Transpose,
            TokenKind::Caret => UnOp::Closure,
            TokenKind::Star => UnOp::ReflexiveClosure,
            _ => return self.parse_atom(),
        };
        self.bump();
        let inner = self.parse_closure()?;
        let span = start.merge(self.espan(inner));
        Ok(self.alloc(ExprKind::Unary { op, expr: inner }, span))
    }

    /// Atoms (grammar-doc section 4.6).
    fn parse_atom(&mut self) -> Result<ExprId, ParseError> {
        let span = self.cur_span();
        match self.cur() {
            TokenKind::Number(n) => {
                let n = *n;
                self.bump();
                Ok(self.alloc(ExprKind::Num(n), span))
            }
            TokenKind::Str(s) => {
                let s = s.clone();
                self.bump();
                Ok(self.alloc(ExprKind::Str(s), span))
            }
            TokenKind::Iden => Ok(self.const_after_bump(Const::Iden, span)),
            TokenKind::Univ => Ok(self.const_after_bump(Const::Univ, span)),
            TokenKind::None => Ok(self.const_after_bump(Const::None, span)),
            TokenKind::This if !matches!(self.peek(1), Some(TokenKind::Slash)) => {
                self.bump();
                Ok(self.alloc(ExprKind::This, span))
            }
            TokenKind::Int => Ok(self.synth_after_bump("Int", span)),
            TokenKind::StringKw => Ok(self.synth_after_bump("String", span)),
            TokenKind::Steps => Ok(self.synth_after_bump("steps", span)),
            TokenKind::FunMin => Ok(self.synth_after_bump("fun/min", span)),
            TokenKind::FunMax => Ok(self.synth_after_bump("fun/max", span)),
            TokenKind::FunNext => Ok(self.synth_after_bump("fun/next", span)),
            TokenKind::Disj => Ok(self.synth_after_bump("disj", span)),
            TokenKind::TotalOrder => Ok(self.synth_after_bump("pred/totalOrder", span)),
            TokenKind::IntCast => Ok(self.synth_after_bump("int", span)),
            TokenKind::Sum => Ok(self.synth_after_bump("sum", span)),
            TokenKind::Seq => self.seq_atom(span),
            TokenKind::At => {
                self.bump();
                let name = self.parse_qual_name()?;
                let full = span.merge(name.span);
                Ok(self.alloc(ExprKind::AtName(name), full))
            }
            TokenKind::LParen => {
                self.bump();
                let inner = self.parse_expr()?;
                self.expect(&TokenKind::RParen, "`)`")?;
                Ok(inner)
            }
            TokenKind::LBrace => {
                if self.is_comprehension_head() {
                    self.parse_comprehension()
                } else {
                    self.parse_block()
                }
            }
            TokenKind::This | TokenKind::Ident => self.name_atom(),
            _ => Err(self.expected("an expression")),
        }
    }

    fn const_after_bump(&mut self, c: Const, span: Span) -> ExprId {
        self.bump();
        self.alloc(ExprKind::Const(c), span)
    }

    fn name_atom(&mut self) -> Result<ExprId, ParseError> {
        let name = self.parse_qual_name()?;
        let span = name.span;
        Ok(self.alloc(ExprKind::Name(name), span))
    }

    /// `seq/Int` (builtin) or a `seq/…` qualified name.
    fn seq_atom(&mut self, span: Span) -> Result<ExprId, ParseError> {
        if matches!(self.peek(1), Some(TokenKind::Slash))
            && matches!(self.peek(2), Some(TokenKind::Int))
        {
            let seq = self.bump();
            self.bump(); // /
            let int = self.bump();
            let full = seq.span.merge(int.span);
            let name = QualName {
                segments: vec![self.ident_of(&seq), self.ident_of(&int)],
                span: full,
            };
            Ok(self.alloc(ExprKind::Name(name), full))
        } else if matches!(self.peek(1), Some(TokenKind::Slash)) {
            self.name_atom()
        } else {
            Err(ParseError::Expected {
                expected: "an expression (`seq` needs `/`)",
                span,
            })
        }
    }

    /// A comprehension `{ decls [| body] }` (body defaults to `true`).
    fn parse_comprehension(&mut self) -> Result<ExprId, ParseError> {
        let open = self.bump(); // {
        let decls = self.parse_binding_seq(false)?;
        let body = if self.at(&TokenKind::Bar) || self.at(&TokenKind::LBrace) {
            self.parse_quant_body()?
        } else {
            self.alloc(ExprKind::Block(Vec::new()), self.cur_span())
        };
        let close = self.expect(&TokenKind::RBrace, "`}`")?;
        Ok(self.alloc(
            ExprKind::Comprehension { decls, body },
            open.span.merge(close.span),
        ))
    }

    // -- Binders ----------------------------------------------------------

    fn starts_binder(&self) -> bool {
        matches!(self.cur(), TokenKind::Let | TokenKind::Quantifier(_))
    }

    fn parse_binder(&mut self) -> Result<ExprId, ParseError> {
        match self.cur() {
            TokenKind::Let => {
                let kw = self.bump();
                self.parse_let(kw.span)
            }
            TokenKind::Quantifier(q) => {
                let quant = *q;
                let kw = self.bump();
                let decls = self.parse_binding_seq(true)?;
                let body = self.parse_quant_body()?;
                let span = kw.span.merge(self.espan(body));
                Ok(self.alloc(ExprKind::Quant { quant, decls, body }, span))
            }
            // `starts_binder` guarantees one of the above.
            _ => Err(self.expected("a quantifier or `let`")),
        }
    }

    fn parse_let(&mut self, kw_span: Span) -> Result<ExprId, ParseError> {
        let mut bindings = Vec::new();
        loop {
            let name = self.parse_let_name()?;
            self.expect(&TokenKind::Equals, "`=` in a let binding")?;
            let value = self.parse_expr()?;
            let span = name.span.merge(self.espan(value));
            bindings.push(LetBinding { name, value, span });
            if !self.eat(&TokenKind::Comma) {
                break;
            }
        }
        let body = self.parse_quant_body()?;
        let span = kw_span.merge(self.espan(body));
        Ok(self.alloc(ExprKind::Let { bindings, body }, span))
    }

    /// A `let`-bound name: an unqualified identifier without `$`.
    fn parse_let_name(&mut self) -> Result<Ident, ParseError> {
        let id = self.parse_decl_ident()?;
        if self.at(&TokenKind::Slash) {
            return Err(ParseError::LetNameSlash { span: id.span });
        }
        Ok(id)
    }

    /// A binder/comprehension body: `| expr [; expr]` or a `{ block }`.
    fn parse_quant_body(&mut self) -> Result<ExprId, ParseError> {
        if self.eat(&TokenKind::Bar) {
            let e = self.parse_expr_no_seq()?;
            if self.at(&TokenKind::Semi) {
                self.bump();
                let rest = self.parse_expr()?;
                let span = self.espan(e).merge(self.espan(rest));
                Ok(self.alloc(
                    ExprKind::Binary {
                        op: BinOp::Seq,
                        lhs: e,
                        rhs: rest,
                    },
                    span,
                ))
            } else {
                Ok(e)
            }
        } else if self.at(&TokenKind::LBrace) {
            self.parse_block()
        } else {
            Err(self.expected("`|` or `{` (a quantifier body)"))
        }
    }

    // -- Blocks & lists ---------------------------------------------------

    /// `{ formula* }` — a conjunction; `{}` is `true`. A block-level `;`
    /// puts the conjunction of the WHOLE remaining block under the
    /// sequencing's rhs (the reference's `SuperP ::= Expr TRCSEQ SuperP`):
    /// `{ a ; b c }` is `Block([Seq(a, Block([b, c]))])` — once `Seq`
    /// desugars to `lhs && after rhs`, everything after the `;` must sit
    /// under the `after`.
    fn parse_block(&mut self) -> Result<ExprId, ParseError> {
        let open = self.expect(&TokenKind::LBrace, "`{`")?;
        let forms = self.parse_block_forms()?;
        let close = self.expect(&TokenKind::RBrace, "`}`")?;
        Ok(self.alloc(ExprKind::Block(forms), open.span.merge(close.span)))
    }

    /// The formulas of one block body, up to (not consuming) the closing
    /// `}`. On a `;`, the rest of the block is folded into the `Seq`'s rhs
    /// and the loop ends (the tail consumed everything).
    fn parse_block_forms(&mut self) -> Result<Vec<ExprId>, ParseError> {
        let mut forms = Vec::new();
        while !self.at(&TokenKind::RBrace) && !self.at(&TokenKind::Eof) {
            let e = self.parse_expr_no_seq()?;
            if !self.at(&TokenKind::Semi) {
                forms.push(e);
                continue;
            }
            self.bump(); // ;
            let rest = self.parse_block_tail()?;
            let span = self.espan(e).merge(self.espan(rest));
            forms.push(self.alloc(
                ExprKind::Binary {
                    op: BinOp::Seq,
                    lhs: e,
                    rhs: rest,
                },
                span,
            ));
            break;
        }
        Ok(forms)
    }

    /// The remainder of a block after a `;`: a single formula stays itself
    /// (further `;`s nest right via the recursion), several conjoin as a
    /// [`ExprKind::Block`], none is an error (the reference requires a
    /// formula after `;`).
    fn parse_block_tail(&mut self) -> Result<ExprId, ParseError> {
        let forms = self.parse_block_forms()?;
        match forms.as_slice() {
            [] => Err(self.expected("a formula after `;`")),
            [single] => Ok(*single),
            [first, .., last] => {
                let span = self.espan(*first).merge(self.espan(*last));
                Ok(self.alloc(ExprKind::Block(forms), span))
            }
        }
    }

    /// A comma-separated expression list until `close` (no empty slots).
    fn parse_expr_list(&mut self, close: &TokenKind) -> Result<Vec<ExprId>, ParseError> {
        if self.at(close) {
            return Ok(Vec::new());
        }
        let mut exprs = vec![self.parse_expr()?];
        while self.eat(&TokenKind::Comma) {
            exprs.push(self.parse_expr()?);
        }
        Ok(exprs)
    }

    // -- Names ------------------------------------------------------------

    /// `[this/ | seq/] ID (/ ID)*` (grammar-doc section 4.1).
    fn parse_qual_name(&mut self) -> Result<QualName, ParseError> {
        let start = self.cur_span();
        let mut segments = Vec::new();
        match self.cur() {
            TokenKind::This | TokenKind::Seq => {
                let prefix = self.bump();
                segments.push(self.ident_of(&prefix));
                self.expect(&TokenKind::Slash, "`/` after `this`/`seq`")?;
            }
            _ => {}
        }
        let first = self.expect_ident("a name")?;
        segments.push(self.ident_of(&first));
        let mut end = first.span;
        while self.at(&TokenKind::Slash) && matches!(self.peek(1), Some(TokenKind::Ident)) {
            self.bump();
            let seg = self.bump();
            end = seg.span;
            segments.push(self.ident_of(&seg));
        }
        Ok(QualName {
            segments,
            span: start.merge(end),
        })
    }

    /// A signature reference: a qualified name or a builtin keyword sig.
    fn parse_sigref(&mut self) -> Result<QualName, ParseError> {
        let span = self.cur_span();
        match self.cur() {
            TokenKind::Univ => Ok(self.keyword_name("univ", span)),
            TokenKind::StringKw => Ok(self.keyword_name("String", span)),
            TokenKind::Steps => Ok(self.keyword_name("steps", span)),
            TokenKind::Int => Ok(self.keyword_name("Int", span)),
            TokenKind::None => Ok(self.keyword_name("none", span)),
            TokenKind::Seq
                if matches!(self.peek(1), Some(TokenKind::Slash))
                    && matches!(self.peek(2), Some(TokenKind::Int)) =>
            {
                let seq = self.bump();
                self.bump(); // /
                let int = self.bump();
                let full = seq.span.merge(int.span);
                Ok(QualName {
                    segments: vec![self.ident_of(&seq), self.ident_of(&int)],
                    span: full,
                })
            }
            _ => self.parse_qual_name(),
        }
    }

    fn keyword_name(&mut self, text: &str, span: Span) -> QualName {
        self.bump();
        QualName {
            segments: vec![Ident {
                text: text.to_owned(),
                span,
            }],
            span,
        }
    }

    /// Whether the current token can begin a `Name` (used for the command
    /// `label target` form).
    fn starts_name(&self) -> bool {
        matches!(
            self.cur(),
            TokenKind::Ident | TokenKind::This | TokenKind::Seq
        )
    }

    fn qual_to_ident(name: QualName) -> Result<Ident, ParseError> {
        let mut segments = name.segments;
        if segments.len() == 1 {
            Ok(segments.remove(0))
        } else {
            Err(ParseError::QualifiedDeclName { span: name.span })
        }
    }

    fn check_no_dollar(name: &QualName) -> Result<(), ParseError> {
        for seg in &name.segments {
            if seg.text.contains('$') {
                return Err(ParseError::DollarInName { span: seg.span });
            }
        }
        Ok(())
    }

    // -- Multiplicity conversion ------------------------------------------

    /// The reference's `mult()`: a top-level unary `some`/`lone`/`one` in a
    /// bound position becomes the `*Of` multiplicity marker.
    fn apply_mult(&mut self, id: ExprId) -> ExprId {
        if let ExprKind::Unary { op, .. } = &mut self.ast.exprs[id].kind {
            *op = match *op {
                UnOp::Some => UnOp::SomeOf,
                UnOp::Lone => UnOp::LoneOf,
                UnOp::One => UnOp::OneOf,
                other => other,
            };
        }
        id
    }

    // -- Comprehension-vs-block lookahead ---------------------------------

    /// Whether the `{` at the cursor opens a comprehension: `[var] [private]
    /// [disj] ID (, ID)* :`.
    fn is_comprehension_head(&self) -> bool {
        let kind = |k: usize| self.peek(k);
        let mut j = 1;
        if matches!(kind(j), Some(TokenKind::Var)) {
            j += 1;
        }
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
}

/// The numeric part of a scope entry before its target is known.
#[derive(Copy, Clone)]
struct RawScope {
    is_exact: bool,
    start: u32,
    end: ScopeEnd,
    increment: Option<u32>,
    span: Span,
}

impl RawScope {
    /// No `exactly`, no range, no increment — the plain `for N` default form.
    fn is_plain(&self) -> bool {
        !self.is_exact && matches!(self.end, ScopeEnd::Same) && self.increment.is_none()
    }

    /// Whether the range grows past its start (blocks `Int`/`seq` scopes).
    fn is_growing(&self) -> bool {
        match self.end {
            ScopeEnd::Same => false,
            ScopeEnd::Bounded(m) => m > self.start,
            ScopeEnd::Unbounded => true,
        }
    }

    /// Exact if `exactly` was written or the range is `N..N`.
    fn effective_exact(&self) -> bool {
        self.is_exact || matches!(self.end, ScopeEnd::Bounded(m) if m == self.start)
    }
}

/// Sets a boolean qualifier, erroring if it was already set.
fn set_flag(flag: &mut bool, span: Span) -> Result<(), ParseError> {
    if *flag {
        return Err(ParseError::DuplicateSigQual { span });
    }
    *flag = true;
    Ok(())
}

/// Sets the sig multiplicity, erroring if one was already set.
fn set_mult(slot: &mut Option<SigMult>, mult: SigMult, span: Span) -> Result<(), ParseError> {
    if slot.is_some() {
        return Err(ParseError::DuplicateSigQual { span });
    }
    *slot = Some(mult);
    Ok(())
}

#[cfg(test)]
mod tests;
