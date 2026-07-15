//! Pretty-printer for the arena AST: turns a parsed module back into valid
//! Alloy 6 surface syntax that re-lexes, re-cooks (F1–F4), and re-parses to a
//! structurally identical AST. It is the strongest cheap oracle we have on the
//! parser before solving lands (`tests/corpus_roundtrip.rs`).
//!
//! Two public surfaces:
//! - [`Ast::pretty`] → a [`Pretty`] wrapper implementing [`fmt::Display`]
//!   (`PORTING_RULES` R9d). The library never prints to stdout/stderr (STYLE
//!   E3); `Display` returning source text is data, not a diagnostic.
//! - [`dump`] → a span-free, arena-index-free structural tree of the whole
//!   AST. Two ASTs are structurally equal iff their dumps are byte-equal, and
//!   a mismatch diffs readably. This is the round-trip equality witness.
//!
//! **Minimal, precedence-aware parenthesization.** The printer emits a paren
//! only where omitting it would change the parse. Each node maps to a
//! left/right binding power drawn from `crate::prec` — the *same* table the
//! parser's Pratt loop uses — so a child is parenthesized exactly when its
//! exposed edge binds looser than the slot the parent will re-parse it into.
//! Binders (`let`/quantifier) and the `;` sequencing tier are handled by a
//! "tail position" flag (`rightmost`): a binder is bare only when nothing in
//! the enclosing expression follows it, else it is wrapped. The dangling-else
//! of `implies` gets one dedicated guard. Because the parser stratifies loose
//! prefixes out of tight operand slots (grammar §3.0), the same edge test also
//! re-parenthesizes a prefix placed where its tier is unreachable.
//!
//! This file exceeds the ~500-line soft cap (STYLE S2): the printer is one
//! cohesive responsibility (AST → surface text) plus the `dump` witness and
//! their colocated snapshot tests, which would only be obscured by a split.

use std::fmt::{self, Write};

use crate::ast::{
    Ast, BinOp, CmdKind, CmdTarget, CmpOp, Const, Decl, DeclId, Expect, ExprId, ExprKind, FactDecl,
    FunDecl, MacroDecl, ModuleHeader, Mult, Open, Para, ParaId, ParaName, PredDecl, QualName,
    Quant, Scope, ScopeEnd, ScopeTarget, SigDecl, SigMult, SigParent, TypeScope, UnOp,
};
use crate::prec::{
    arrow_bp, binary_bp, child_binder_budget, cmp_bp, BinderOperator, ARROW_BP, BINDER_BUDGET_HOP,
    BINDER_BUDGET_NONE, BINDER_BUDGET_TOP, BP_ATOM, BP_IMPLIES_R, BP_NOT, BP_NUMUNOP,
    BP_PRIME_CLOSURE, BP_TEST, CMP_BP, JOIN_BP, TIER_TEST,
};

/// A binding power no operator reaches; an atom's exposed edges use it, so an
/// atom never triggers parentheses.
const INF: u8 = BP_ATOM;

/// A borrowing [`fmt::Display`] view over an [`Ast`] that renders it as valid
/// Alloy 6 source (see the module docs).
///
/// Deliberately not `Copy`: it is passed by `&self` through the recursive
/// writers, so a `Copy` handle would only invite `trivially_copy_pass_by_ref`.
#[derive(Debug)]
pub struct Pretty<'a> {
    ast: &'a Ast,
}

impl Ast {
    /// Borrows this module as a [`Display`](fmt::Display)-able source rendering.
    #[must_use]
    pub fn pretty(&self) -> Pretty<'_> {
        Pretty { ast: self }
    }
}

impl fmt::Display for Pretty<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.write_module(f)
    }
}

/// Renders `ast` as a source string (convenience over [`Ast::pretty`]).
#[must_use]
pub fn pretty_to_string(ast: &Ast) -> String {
    ast.pretty().to_string()
}

impl Pretty<'_> {
    // -- Module / paragraphs ---------------------------------------------

    fn write_module<W: Write>(&self, w: &mut W) -> fmt::Result {
        let mut started = false;
        if let Some(header) = &self.ast.header {
            Self::write_header(w, header)?;
            w.write_char('\n')?;
            started = true;
        }
        for open in &self.ast.opens {
            if started {
                w.write_char('\n')?;
            }
            Self::write_open(w, open)?;
            w.write_char('\n')?;
            started = true;
        }
        for &pid in &self.ast.paragraphs {
            // A follow-up command (`cmd => run …`) attaches to the previous
            // command's line rather than opening a blank-separated paragraph.
            let followup = matches!(&self.ast.paras[pid], Para::Cmd(c) if c.is_followup);
            if started && !followup {
                w.write_char('\n')?;
            }
            self.write_para(w, pid)?;
            w.write_char('\n')?;
            started = true;
        }
        Ok(())
    }

    fn write_header<W: Write>(w: &mut W, header: &ModuleHeader) -> fmt::Result {
        w.write_str("module ")?;
        write_qualname(w, &header.name)?;
        if !header.params.is_empty() {
            w.write_char('[')?;
            for (i, param) in header.params.iter().enumerate() {
                if i > 0 {
                    w.write_str(", ")?;
                }
                if param.is_exact {
                    w.write_str("exactly ")?;
                }
                write_qualname(w, &param.name)?;
            }
            w.write_char(']')?;
        }
        Ok(())
    }

    fn write_open<W: Write>(w: &mut W, open: &Open) -> fmt::Result {
        if open.is_private {
            w.write_str("private ")?;
        }
        w.write_str("open ")?;
        write_qualname(w, &open.module)?;
        if !open.args.is_empty() {
            w.write_char('[')?;
            for (i, arg) in open.args.iter().enumerate() {
                if i > 0 {
                    w.write_str(", ")?;
                }
                write_qualname(w, arg)?;
            }
            w.write_char(']')?;
        }
        if let Some(alias) = &open.alias {
            w.write_str(" as ")?;
            w.write_str(&alias.text)?;
        }
        Ok(())
    }

    fn write_para<W: Write>(&self, w: &mut W, pid: ParaId) -> fmt::Result {
        match &self.ast.paras[pid] {
            Para::Sig(sig) => self.write_sig(w, sig),
            Para::Enum(e) => {
                w.write_str("enum ")?;
                w.write_str(&e.name.text)?;
                w.write_str(" { ")?;
                for (i, v) in e.variants.iter().enumerate() {
                    if i > 0 {
                        w.write_str(", ")?;
                    }
                    w.write_str(&v.text)?;
                }
                w.write_str(" }")
            }
            Para::Fact(f) => self.write_fact(w, f),
            Para::Assert(a) => {
                w.write_str("assert ")?;
                if let Some(name) = &a.name {
                    write_para_name(w, name)?;
                    w.write_char(' ')?;
                }
                self.write_body_block(w, a.body, 0)
            }
            Para::Pred(p) => self.write_pred(w, p),
            Para::Fun(f) => self.write_fun(w, f),
            Para::Macro(m) => self.write_macro(w, m),
            Para::Cmd(c) => self.write_cmd(w, c),
        }
    }

    fn write_fact<W: Write>(&self, w: &mut W, f: &FactDecl) -> fmt::Result {
        w.write_str("fact ")?;
        if let Some(name) = &f.name {
            write_para_name(w, name)?;
            w.write_char(' ')?;
        }
        self.write_body_block(w, f.body, 0)
    }

    fn write_sig<W: Write>(&self, w: &mut W, sig: &SigDecl) -> fmt::Result {
        let q = &sig.qual;
        if q.is_private {
            w.write_str("private ")?;
        }
        if q.is_abstract {
            w.write_str("abstract ")?;
        }
        if q.is_var {
            w.write_str("var ")?;
        }
        if let Some(mult) = q.mult {
            w.write_str(sig_mult_word(mult))?;
            w.write_char(' ')?;
        }
        w.write_str("sig ")?;
        for (i, name) in sig.names.iter().enumerate() {
            if i > 0 {
                w.write_str(", ")?;
            }
            w.write_str(&name.text)?;
        }
        Self::write_sig_parent(w, &sig.parent)?;
        w.write_char(' ')?;
        self.write_field_block(w, &sig.fields)?;
        if let Some(fact) = sig.fact {
            w.write_char(' ')?;
            self.write_body_block(w, fact, 0)?;
        }
        Ok(())
    }

    fn write_sig_parent<W: Write>(w: &mut W, parent: &SigParent) -> fmt::Result {
        match parent {
            SigParent::None => Ok(()),
            SigParent::Extends(p) => {
                w.write_str(" extends ")?;
                write_qualname(w, p)
            }
            SigParent::In(ps) => {
                w.write_str(" in ")?;
                Self::write_ref_union(w, ps)
            }
            SigParent::Eq(ps) => {
                w.write_str(" = ")?;
                Self::write_ref_union(w, ps)
            }
        }
    }

    fn write_ref_union<W: Write>(w: &mut W, refs: &[QualName]) -> fmt::Result {
        for (i, r) in refs.iter().enumerate() {
            if i > 0 {
                w.write_str(" + ")?;
            }
            write_qualname(w, r)?;
        }
        Ok(())
    }

    fn write_field_block<W: Write>(&self, w: &mut W, fields: &[DeclId]) -> fmt::Result {
        if fields.is_empty() {
            return w.write_str("{}");
        }
        w.write_str("{\n")?;
        for (i, &field) in fields.iter().enumerate() {
            write_indent(w, 1)?;
            self.write_decl(w, field, 1)?;
            if i + 1 < fields.len() {
                w.write_char(',')?;
            }
            w.write_char('\n')?;
        }
        w.write_char('}')
    }

    fn write_pred<W: Write>(&self, w: &mut W, p: &PredDecl) -> fmt::Result {
        if p.is_private {
            w.write_str("private ")?;
        }
        w.write_str("pred ")?;
        if let Some(recv) = &p.receiver {
            write_qualname(w, recv)?;
            w.write_char('.')?;
        }
        w.write_str(&p.name.text)?;
        self.write_params(w, &p.params)?;
        w.write_char(' ')?;
        self.write_body_block(w, p.body, 0)
    }

    fn write_fun<W: Write>(&self, w: &mut W, f: &FunDecl) -> fmt::Result {
        if f.is_private {
            w.write_str("private ")?;
        }
        w.write_str("fun ")?;
        if let Some(recv) = &f.receiver {
            write_qualname(w, recv)?;
            w.write_char('.')?;
        }
        w.write_str(&f.name.text)?;
        self.write_params(w, &f.params)?;
        w.write_str(": ")?;
        self.write_expr(w, f.returns, 0, true, BINDER_BUDGET_TOP)?;
        w.write_char(' ')?;
        self.write_body_block(w, f.body, 0)
    }

    fn write_params<W: Write>(&self, w: &mut W, params: &[DeclId]) -> fmt::Result {
        if params.is_empty() {
            return Ok(());
        }
        w.write_char('[')?;
        for (i, &d) in params.iter().enumerate() {
            if i > 0 {
                w.write_str(", ")?;
            }
            self.write_decl(w, d, 0)?;
        }
        w.write_char(']')
    }

    fn write_macro<W: Write>(&self, w: &mut W, m: &MacroDecl) -> fmt::Result {
        if m.is_private {
            w.write_str("private ")?;
        }
        w.write_str("let ")?;
        w.write_str(&m.name.text)?;
        if !m.params.is_empty() {
            w.write_char('[')?;
            for (i, name) in m.params.iter().enumerate() {
                if i > 0 {
                    w.write_str(", ")?;
                }
                w.write_str(&name.text)?;
            }
            w.write_char(']')?;
        }
        // A block body reprints with no `=` (both `let m { .. }` and
        // `let m = { .. }` parse to the same `Block` body); anything else is
        // the `= expr` form.
        if let ExprKind::Block(forms) = &self.ast.exprs[m.body].kind {
            w.write_char(' ')?;
            self.write_block_body(w, forms, 0)
        } else {
            w.write_str(" = ")?;
            self.write_expr(w, m.body, 0, true, BINDER_BUDGET_TOP)
        }
    }

    fn write_cmd<W: Write>(&self, w: &mut W, c: &crate::ast::CmdDecl) -> fmt::Result {
        if c.is_followup {
            w.write_str("=> ")?;
        }
        if let Some(label) = &c.label {
            w.write_str(&label.text)?;
            w.write_str(": ")?;
        }
        w.write_str(match c.kind {
            CmdKind::Run => "run",
            CmdKind::Check => "check",
        })?;
        w.write_char(' ')?;
        match &c.target {
            CmdTarget::Name(q) => write_qualname(w, q)?,
            CmdTarget::Block(b) => self.write_body_block(w, *b, 0)?,
        }
        if let Some(scope) = &c.scope {
            w.write_char(' ')?;
            Self::write_scope(w, scope)?;
        }
        match c.expect {
            None => Ok(()),
            Some(Expect::Sat) => w.write_str(" expect 1"),
            Some(Expect::Unsat) => w.write_str(" expect 0"),
            Some(Expect::Other(n)) => write!(w, " expect {n}"),
        }
    }

    // -- Scopes -----------------------------------------------------------

    fn write_scope<W: Write>(w: &mut W, scope: &Scope) -> fmt::Result {
        w.write_str("for ")?;
        match (scope.default, scope.entries.is_empty()) {
            (Some(n), true) => write!(w, "{n}")?,
            (Some(n), false) => {
                write!(w, "{n} but ")?;
                Self::write_scope_entries(w, &scope.entries)?;
            }
            (None, _) => Self::write_scope_entries(w, &scope.entries)?,
        }
        Ok(())
    }

    fn write_scope_entries<W: Write>(w: &mut W, entries: &[TypeScope]) -> fmt::Result {
        for (i, ts) in entries.iter().enumerate() {
            if i > 0 {
                w.write_str(", ")?;
            }
            Self::write_type_scope(w, ts)?;
        }
        Ok(())
    }

    fn write_type_scope<W: Write>(w: &mut W, ts: &TypeScope) -> fmt::Result {
        // `N..N` already marks the scope exact, so an explicit `exactly` would
        // be redundant (and, on `Int`/`seq`, rejected — but those never carry
        // exactness or ranges). Suppress it in that one case.
        let range_implies_exact = matches!(ts.end, ScopeEnd::Bounded(m) if m == ts.start);
        if ts.is_exact && !range_implies_exact {
            w.write_str("exactly ")?;
        }
        write!(w, "{}", ts.start)?;
        match ts.end {
            ScopeEnd::Same => {}
            ScopeEnd::Bounded(m) => write!(w, "..{m}")?,
            ScopeEnd::Unbounded => w.write_str("..")?,
        }
        if let Some(inc) = ts.increment {
            write!(w, ":{inc}")?;
        }
        w.write_char(' ')?;
        match &ts.target {
            ScopeTarget::Sig(q) => write_qualname(w, q),
            ScopeTarget::Int => w.write_str("Int"),
            ScopeTarget::Seq => w.write_str("seq"),
            ScopeTarget::Str => w.write_str("String"),
            ScopeTarget::Steps => w.write_str("steps"),
        }
    }

    // -- Declarations -----------------------------------------------------

    fn write_decl<W: Write>(&self, w: &mut W, d: DeclId, indent: usize) -> fmt::Result {
        let decl: &Decl = &self.ast.decls[d];
        if decl.is_var {
            w.write_str("var ")?;
        }
        if decl.is_private {
            w.write_str("private ")?;
        }
        if decl.is_disj {
            w.write_str("disj ")?;
        }
        for (i, name) in decl.names.iter().enumerate() {
            if i > 0 {
                w.write_str(", ")?;
            }
            w.write_str(&name.text)?;
        }
        // A defined decl (`names = expr`) stores its value under `ExactlyOf`;
        // every other bound is the `: expr` form (the bound expression carries
        // any multiplicity marker itself).
        if let ExprKind::Unary {
            op: UnOp::ExactlyOf,
            expr,
        } = &self.ast.exprs[decl.bound].kind
        {
            let inner = *expr;
            w.write_str(" = ")?;
            self.write_expr(w, inner, indent, true, BINDER_BUDGET_TOP)
        } else {
            w.write_str(": ")?;
            if decl.is_bound_disj {
                w.write_str("disj ")?;
            }
            self.write_expr(w, decl.bound, indent, true, BINDER_BUDGET_TOP)
        }
    }

    // -- Expressions ------------------------------------------------------

    /// Writes `e`. `rightmost` is true when nothing in the enclosing
    /// expression follows `e` (so a binder here is a syntactic candidate for
    /// going bare); `budget` is `e`'s binder-composition budget (mt-014
    /// Part 1/2, `crate::prec::child_binder_budget`) — the *same* value the
    /// parser would have had available when it parsed whatever occupies
    /// this slot. Both must independently allow it (see `needs_parens`):
    /// `rightmost` alone is not enough once a binder has already spent its
    /// one composition hop through an enclosing operator.
    fn write_expr<W: Write>(
        &self,
        w: &mut W,
        e: ExprId,
        indent: usize,
        rightmost: bool,
        budget: u8,
    ) -> fmt::Result {
        match &self.ast.exprs[e].kind {
            ExprKind::Num(n) => write!(w, "{n}"),
            ExprKind::Str(s) => write_escaped_str(w, s),
            ExprKind::Const(c) => w.write_str(match c {
                Const::None => "none",
                Const::Univ => "univ",
                Const::Iden => "iden",
            }),
            ExprKind::This => w.write_str("this"),
            ExprKind::Name(q) => write_qualname(w, q),
            ExprKind::AtName(q) => {
                w.write_char('@')?;
                write_qualname(w, q)
            }
            ExprKind::Unary { .. } => self.write_unary(w, e, indent, rightmost, budget),
            ExprKind::Binary { .. } => self.write_binary(w, e, indent, rightmost, budget),
            ExprKind::Arrow { .. } => self.write_arrow(w, e, indent, rightmost, budget),
            ExprKind::Compare { .. } => self.write_compare(w, e, indent, rightmost),
            ExprKind::IfThenElse { .. } => self.write_ite(w, e, indent, rightmost, budget),
            ExprKind::BoxJoin { .. } => self.write_boxjoin(w, e, indent),
            ExprKind::Quant { .. } => self.write_quant(w, e, indent, rightmost),
            ExprKind::Comprehension { .. } => self.write_comprehension(w, e, indent),
            ExprKind::Let { .. } => self.write_let(w, e, indent, rightmost),
            ExprKind::Block(forms) => self.write_block_body(w, forms, indent),
        }
    }

    /// Writes `e` in an operand slot the parent will re-parse at `min_bp`
    /// (`is_left` = the slot is the parent's *left* operand), wrapping in
    /// parens exactly when a bare `e` would not re-parse to itself there.
    /// Inside a freshly-opened paren, content is always a fresh expression
    /// start (`BINDER_BUDGET_TOP`), matching `Parser::parse_atom`'s
    /// `LParen` arm (`parse_expr`, budget `TOP`).
    #[allow(
        clippy::too_many_arguments,
        reason = "mirrors Parser::parse_operand's own (min_bp, budget) pair plus the printer's \
                  own (is_left, rightmost) placement flags (mt-014 Part 2) -- splitting these \
                  into a struct would obscure the 1:1 correspondence with the parser this \
                  module's own doc comment promises"
    )]
    fn write_operand<W: Write>(
        &self,
        w: &mut W,
        e: ExprId,
        min_bp: u8,
        is_left: bool,
        rightmost: bool,
        budget: u8,
        indent: usize,
    ) -> fmt::Result {
        if self.needs_parens(e, min_bp, is_left, rightmost, budget) {
            w.write_char('(')?;
            self.write_expr(w, e, indent, true, BINDER_BUDGET_TOP)?;
            w.write_char(')')
        } else {
            self.write_expr(w, e, indent, rightmost, budget)
        }
    }

    fn needs_parens(
        &self,
        e: ExprId,
        min_bp: u8,
        is_left: bool,
        rightmost: bool,
        budget: u8,
    ) -> bool {
        // Binders (`let`/quantifier) extend to the end of the enclosing
        // expression; they are safe bare only in tail position (`rightmost`)
        // *and* only while the composition budget still allows a bare
        // binder here (mt-014 Part 2) -- either condition alone can force
        // parens.
        if matches!(
            self.ast.exprs[e].kind,
            ExprKind::Quant { .. } | ExprKind::Let { .. }
        ) {
            return !rightmost || budget < BINDER_BUDGET_HOP;
        }
        let (lp, rp) = self.lp_rp(e);
        let edge = if is_left { rp } else { lp };
        edge < min_bp
    }

    /// The binding powers a node exposes on its (left, right) edges — the
    /// power an enclosing operator must exceed to split the node there.
    fn lp_rp(&self, e: ExprId) -> (u8, u8) {
        match &self.ast.exprs[e].kind {
            ExprKind::Num(_)
            | ExprKind::Str(_)
            | ExprKind::Const(_)
            | ExprKind::This
            | ExprKind::Name(_)
            | ExprKind::AtName(_)
            | ExprKind::Block(_)
            | ExprKind::Comprehension { .. } => (INF, INF),
            // A box join `t[..]` is closed on the right (ends in `]`), but its
            // left edge sits at the join tier: a tighter prefix (`~`/`^`/`*`)
            // to its left would bind the target before the `[..]`, so
            // `~(f[x])` must keep its parens.
            ExprKind::BoxJoin { .. } => (JOIN_BP.0, INF),
            ExprKind::Unary { op, .. } => match op {
                UnOp::Not
                | UnOp::Always
                | UnOp::Eventually
                | UnOp::After
                | UnOp::Before
                | UnOp::Historically
                | UnOp::Once => (BP_NOT, BP_NOT),
                UnOp::No
                | UnOp::Some
                | UnOp::Lone
                | UnOp::One
                | UnOp::SetOf
                | UnOp::SomeOf
                | UnOp::LoneOf
                | UnOp::OneOf
                | UnOp::SeqOf => (TIER_TEST, BP_TEST),
                UnOp::Card | UnOp::IntOf | UnOp::SumOf => (BP_NUMUNOP, BP_NUMUNOP),
                UnOp::Transpose | UnOp::Closure | UnOp::ReflexiveClosure => {
                    (BP_PRIME_CLOSURE, BP_PRIME_CLOSURE)
                }
                // Postfix prime is closed on the right (nothing binds past `'`).
                UnOp::Prime => (BP_PRIME_CLOSURE, INF),
                // `= e` only ever sits in a decl bound, never an operand slot.
                UnOp::ExactlyOf => (INF, INF),
            },
            ExprKind::Binary { op, .. } => binary_bp(*op),
            ExprKind::Arrow {
                lhs_mult, rhs_mult, ..
            } => arrow_bp(*lhs_mult, *rhs_mult),
            ExprKind::Compare { op, .. } => cmp_bp(*op),
            ExprKind::IfThenElse { .. } => binary_bp(BinOp::Implies),
            // Binders: parens are decided by `rightmost`, not these values.
            ExprKind::Quant { .. } | ExprKind::Let { .. } => (INF, 0),
        }
    }

    /// `budget` is `e`'s own composition budget (see `write_expr`). Every
    /// prefix here is *transparent*: it passes `budget` straight through to
    /// its operand unchanged, matching `Parser::parse_prefix`'s handling of
    /// every prefix tier except the set-tests, which instead hard-block
    /// (`BINDER_BUDGET_NONE`) regardless of `budget` -- jar-verified (mt-014
    /// Part 2): `no all x: A | …` is a syntax error even though `! all x: A
    /// | …` and `# all x: A | …` are fine.
    #[allow(
        clippy::too_many_lines,
        reason = "one match arm per UnOp variant (STYLE S2 soft-cap exception, same rationale \
                  as lexer.rs's operator table): splitting the table would only obscure the 1:1 \
                  correspondence with UnOp's variants"
    )]
    fn write_unary<W: Write>(
        &self,
        w: &mut W,
        e: ExprId,
        indent: usize,
        rightmost: bool,
        budget: u8,
    ) -> fmt::Result {
        let ExprKind::Unary { op, expr } = &self.ast.exprs[e].kind else {
            debug_assert!(false, "write_unary on non-unary node");
            return Ok(());
        };
        let (op, inner) = (*op, *expr);
        match op {
            UnOp::Prime => {
                self.write_operand(w, inner, BP_PRIME_CLOSURE, true, false, budget, indent)?;
                w.write_char('\'')
            }
            UnOp::Transpose => self.write_closure(w, '~', inner, indent, budget),
            UnOp::Closure => self.write_closure(w, '^', inner, indent, budget),
            UnOp::ReflexiveClosure => self.write_closure(w, '*', inner, indent, budget),
            UnOp::Not => {
                w.write_char('!')?;
                self.write_operand(w, inner, BP_NOT, false, rightmost, budget, indent)
            }
            UnOp::Always => {
                self.write_word_prefix(w, "always", inner, BP_NOT, indent, rightmost, budget)
            }
            UnOp::Eventually => {
                self.write_word_prefix(w, "eventually", inner, BP_NOT, indent, rightmost, budget)
            }
            UnOp::After => {
                self.write_word_prefix(w, "after", inner, BP_NOT, indent, rightmost, budget)
            }
            UnOp::Before => {
                self.write_word_prefix(w, "before", inner, BP_NOT, indent, rightmost, budget)
            }
            UnOp::Historically => {
                self.write_word_prefix(w, "historically", inner, BP_NOT, indent, rightmost, budget)
            }
            UnOp::Once => {
                self.write_word_prefix(w, "once", inner, BP_NOT, indent, rightmost, budget)
            }
            // Set tests and their bound-marker twins share surface spellings
            // (`some A` / `some A`): the reference's `mult()` distinguishes
            // them by context, so the printed text is identical. Hard
            // `BINDER_BUDGET_NONE`, not `budget` -- mt-014 Part 2.
            UnOp::No => self.write_word_prefix(
                w,
                "no",
                inner,
                BP_TEST,
                indent,
                rightmost,
                BINDER_BUDGET_NONE,
            ),
            UnOp::Some | UnOp::SomeOf => self.write_word_prefix(
                w,
                "some",
                inner,
                BP_TEST,
                indent,
                rightmost,
                BINDER_BUDGET_NONE,
            ),
            UnOp::Lone | UnOp::LoneOf => self.write_word_prefix(
                w,
                "lone",
                inner,
                BP_TEST,
                indent,
                rightmost,
                BINDER_BUDGET_NONE,
            ),
            UnOp::One | UnOp::OneOf => self.write_word_prefix(
                w,
                "one",
                inner,
                BP_TEST,
                indent,
                rightmost,
                BINDER_BUDGET_NONE,
            ),
            UnOp::SetOf => self.write_word_prefix(
                w,
                "set",
                inner,
                BP_TEST,
                indent,
                rightmost,
                BINDER_BUDGET_NONE,
            ),
            UnOp::SeqOf => self.write_word_prefix(
                w,
                "seq",
                inner,
                BP_TEST,
                indent,
                rightmost,
                BINDER_BUDGET_NONE,
            ),
            UnOp::Card => {
                w.write_char('#')?;
                self.write_operand(w, inner, BP_NUMUNOP, false, rightmost, budget, indent)
            }
            UnOp::IntOf => {
                self.write_word_prefix(w, "int", inner, BP_NUMUNOP, indent, rightmost, budget)
            }
            UnOp::SumOf => {
                self.write_word_prefix(w, "sum", inner, BP_NUMUNOP, indent, rightmost, budget)
            }
            // `= e` is only reachable via a decl bound (handled in write_decl);
            // this arm keeps the match total. A decl bound is a fresh
            // `parse_expr()` context in the parser, so `BINDER_BUDGET_TOP`.
            UnOp::ExactlyOf => {
                w.write_str("= ")?;
                self.write_expr(w, inner, indent, rightmost, BINDER_BUDGET_TOP)
            }
        }
    }

    /// Self-recursive (`~~~~~x`) like `Parser::parse_closure`, so it takes
    /// its own `budget` and threads it through unchanged (transparent).
    fn write_closure<W: Write>(
        &self,
        w: &mut W,
        sym: char,
        inner: ExprId,
        indent: usize,
        budget: u8,
    ) -> fmt::Result {
        w.write_char(sym)?;
        self.write_operand(w, inner, BP_PRIME_CLOSURE, false, false, budget, indent)
    }

    #[allow(
        clippy::too_many_arguments,
        reason = "shared helper for every word-spelled prefix (STYLE S1 -- one nameable thing: \
                  write `word operand`), each caller passing its own operand tier/eligibility; \
                  see write_operand's #[allow] for why a struct would obscure more than it helps"
    )]
    fn write_word_prefix<W: Write>(
        &self,
        w: &mut W,
        word: &str,
        inner: ExprId,
        operand_bp: u8,
        indent: usize,
        rightmost: bool,
        budget: u8,
    ) -> fmt::Result {
        w.write_str(word)?;
        w.write_char(' ')?;
        self.write_operand(w, inner, operand_bp, false, rightmost, budget, indent)
    }

    fn write_binary<W: Write>(
        &self,
        w: &mut W,
        e: ExprId,
        indent: usize,
        rightmost: bool,
        budget: u8,
    ) -> fmt::Result {
        let ExprKind::Binary { op, lhs, rhs } = &self.ast.exprs[e].kind else {
            debug_assert!(false, "write_binary on non-binary node");
            return Ok(());
        };
        let (op, lhs, rhs) = (*op, *lhs, *rhs);
        if matches!(op, BinOp::Join) {
            let (lbp, _) = JOIN_BP;
            self.write_operand(w, lhs, lbp, true, false, budget, indent)?;
            w.write_char('.')?;
            // The dot's right operand is a tight term (closure/prime/atom);
            // an ordinary (non-`implies`) composition hop, mt-014 Part 2.
            let dot_budget = child_binder_budget(budget, BinderOperator::Ordinary);
            return self.write_operand(w, rhs, BP_PRIME_CLOSURE, false, false, dot_budget, indent);
        }
        let (lbp, rbp) = binary_bp(op);
        self.write_operand(w, lhs, lbp, true, false, budget, indent)?;
        write!(w, " {} ", binop_str(op))?;
        // `implies` (no `else` -- that shape is `IfThenElse`, `write_ite`
        // below) refreshes the budget to `TOP`; every other binary operator
        // gets one ordinary hop (mt-014 Part 2, `child_binder_budget`).
        let class = if matches!(op, BinOp::Implies) {
            BinderOperator::Implies
        } else {
            BinderOperator::Ordinary
        };
        let rhs_budget = child_binder_budget(budget, class);
        self.write_operand(w, rhs, rbp, false, rightmost, rhs_budget, indent)
    }

    fn write_arrow<W: Write>(
        &self,
        w: &mut W,
        e: ExprId,
        indent: usize,
        rightmost: bool,
        budget: u8,
    ) -> fmt::Result {
        let ExprKind::Arrow {
            lhs,
            lhs_mult,
            rhs_mult,
            rhs,
        } = &self.ast.exprs[e].kind
        else {
            debug_assert!(false, "write_arrow on non-arrow node");
            return Ok(());
        };
        let (lhs, lhs_mult, rhs_mult, rhs) = (*lhs, *lhs_mult, *rhs_mult, *rhs);
        self.write_operand(w, lhs, ARROW_BP.0, true, false, budget, indent)?;
        w.write_char(' ')?;
        if let Some(m) = lhs_mult {
            w.write_str(mult_word(m))?;
            w.write_char(' ')?;
        }
        w.write_str("->")?;
        if let Some(m) = rhs_mult {
            w.write_char(' ')?;
            w.write_str(mult_word(m))?;
        }
        w.write_char(' ')?;
        let rhs_budget = child_binder_budget(budget, BinderOperator::Ordinary);
        self.write_operand(w, rhs, ARROW_BP.1, false, rightmost, rhs_budget, indent)
    }

    fn write_compare<W: Write>(
        &self,
        w: &mut W,
        e: ExprId,
        indent: usize,
        rightmost: bool,
    ) -> fmt::Result {
        let ExprKind::Compare {
            op,
            negated,
            lhs,
            rhs,
        } = &self.ast.exprs[e].kind
        else {
            debug_assert!(false, "write_compare on non-compare node");
            return Ok(());
        };
        let (op, negated, lhs, rhs) = (*op, *negated, *lhs, *rhs);
        // A comparison's own left/right operand budget doesn't matter for
        // the left side (`is_left` already forces parens on any bare
        // binder there); its own incoming budget is otherwise irrelevant to
        // `lhs` since `is_left=true` slots are never rightmost.
        self.write_operand(w, lhs, CMP_BP.0, true, false, BINDER_BUDGET_NONE, indent)?;
        write!(w, " {} ", cmp_str(op, negated))?;
        // Comparisons never accept a binder as their operand, at any
        // ambient budget (mt-014 Part 2, jar-verified) -- hard `NONE`.
        self.write_operand(
            w,
            rhs,
            CMP_BP.1,
            false,
            rightmost,
            BINDER_BUDGET_NONE,
            indent,
        )
    }

    fn write_ite<W: Write>(
        &self,
        w: &mut W,
        e: ExprId,
        indent: usize,
        rightmost: bool,
        budget: u8,
    ) -> fmt::Result {
        let ExprKind::IfThenElse {
            cond,
            then_branch,
            else_branch,
        } = &self.ast.exprs[e].kind
        else {
            debug_assert!(false, "write_ite on non-if node");
            return Ok(());
        };
        let (cond, then_branch, else_branch) = (*cond, *then_branch, *else_branch);
        self.write_operand(w, cond, 11, true, false, budget, indent)?;
        w.write_str(" => ")?;
        // Dangling-else guard: a bare `=>` (no else) in the then-branch would
        // capture this else on re-parse, so wrap it even though precedence
        // alone would not (its tier equals the branch slot's).
        if matches!(
            self.ast.exprs[then_branch].kind,
            ExprKind::Binary {
                op: BinOp::Implies,
                ..
            }
        ) {
            w.write_char('(')?;
            self.write_expr(w, then_branch, indent, true, BINDER_BUDGET_TOP)?;
            w.write_char(')')?;
        } else {
            // `implies … else`'s then-branch never accepts a binder operand
            // at all, jar-verified (mt-014 Part 2) -- hard `NONE`,
            // independent of `budget` (unlike a bare `implies` with no
            // `else`, whose then-branch is `write_binary`'s `Implies` case
            // above and *does* get the refreshed `TOP` budget).
            self.write_operand(
                w,
                then_branch,
                BP_IMPLIES_R,
                false,
                false,
                BINDER_BUDGET_NONE,
                indent,
            )?;
        }
        w.write_str(" else ")?;
        // The else-branch is the true rightmost operand of the whole
        // construct, so it gets the same `Implies`-refreshed budget a bare
        // `implies`'s then-branch would (jar-verified: `q implies r else s
        // and all x: A | …` parses).
        let else_budget = child_binder_budget(budget, BinderOperator::Implies);
        self.write_operand(
            w,
            else_branch,
            BP_IMPLIES_R,
            false,
            rightmost,
            else_budget,
            indent,
        )
    }

    fn write_boxjoin<W: Write>(&self, w: &mut W, e: ExprId, indent: usize) -> fmt::Result {
        let ExprKind::BoxJoin { target, args } = &self.ast.exprs[e].kind else {
            debug_assert!(false, "write_boxjoin on non-boxjoin node");
            return Ok(());
        };
        // The target inherits whatever budget got us here (transparent,
        // like an `is_left` operand); it is never itself a bare Quant/Let
        // in valid source (`is_left` positions always force parens), so the
        // exact value only matters for consistency.
        self.write_operand(
            w,
            *target,
            JOIN_BP.0,
            true,
            false,
            BINDER_BUDGET_NONE,
            indent,
        )?;
        w.write_char('[')?;
        for (i, &arg) in args.iter().enumerate() {
            if i > 0 {
                w.write_str(", ")?;
            }
            // Each argument is a full expression delimited by `,`/`]` --
            // a fresh `parse_expr()` context in the parser, `BINDER_BUDGET_TOP`.
            self.write_operand(w, arg, 0, false, true, BINDER_BUDGET_TOP, indent)?;
        }
        w.write_char(']')
    }

    fn write_quant<W: Write>(
        &self,
        w: &mut W,
        e: ExprId,
        indent: usize,
        rightmost: bool,
    ) -> fmt::Result {
        let ExprKind::Quant { quant, decls, body } = &self.ast.exprs[e].kind else {
            debug_assert!(false, "write_quant on non-quant node");
            return Ok(());
        };
        w.write_str(quant_word(*quant))?;
        w.write_char(' ')?;
        self.write_inline_decls(w, decls, indent)?;
        w.write_str(" | ")?;
        // A binder's body is a fresh `parse_quant_body`/`parse_expr` context
        // in the parser (`BINDER_BUDGET_TOP`), independent of whatever
        // budget got us to this Quant/Let node itself (that was already
        // resolved by the caller's `needs_parens` before it decided to
        // print this node bare vs. parenthesized).
        self.write_expr(w, *body, indent, rightmost, BINDER_BUDGET_TOP)
    }

    fn write_comprehension<W: Write>(&self, w: &mut W, e: ExprId, indent: usize) -> fmt::Result {
        let ExprKind::Comprehension { decls, body } = &self.ast.exprs[e].kind else {
            debug_assert!(false, "write_comprehension on non-comprehension node");
            return Ok(());
        };
        let body = *body;
        w.write_str("{ ")?;
        self.write_inline_decls(w, decls, indent)?;
        // An omitted body parses to an empty `Block`; reprint it omitted.
        let empty_body = matches!(&self.ast.exprs[body].kind, ExprKind::Block(v) if v.is_empty());
        if !empty_body {
            w.write_str(" | ")?;
            // Also a fresh `parse_quant_body` context, `BINDER_BUDGET_TOP`.
            self.write_expr(w, body, indent, true, BINDER_BUDGET_TOP)?;
        }
        w.write_str(" }")
    }

    fn write_let<W: Write>(
        &self,
        w: &mut W,
        e: ExprId,
        indent: usize,
        rightmost: bool,
    ) -> fmt::Result {
        let ExprKind::Let { bindings, body } = &self.ast.exprs[e].kind else {
            debug_assert!(false, "write_let on non-let node");
            return Ok(());
        };
        w.write_str("let ")?;
        for (i, b) in bindings.iter().enumerate() {
            if i > 0 {
                w.write_str(", ")?;
            }
            w.write_str(&b.name.text)?;
            w.write_str(" = ")?;
            // Deliberately conservative (not `BINDER_BUDGET_TOP`, though a
            // binding value is a fresh `parse_expr()` context): `rightmost`
            // is hardcoded `false` here regardless, since a bare binder
            // here would greedily read through the rest of this `let`'s
            // own bindings/body on re-parse (pre-dates mt-014; unaffected
            // either way since `rightmost=false` alone already forces
            // parens on any Quant/Let, whatever budget is passed).
            self.write_operand(w, b.value, 0, false, false, BINDER_BUDGET_NONE, indent)?;
        }
        w.write_str(" | ")?;
        self.write_expr(w, *body, indent, rightmost, BINDER_BUDGET_TOP)
    }

    fn write_inline_decls<W: Write>(
        &self,
        w: &mut W,
        decls: &[DeclId],
        indent: usize,
    ) -> fmt::Result {
        for (i, &d) in decls.iter().enumerate() {
            if i > 0 {
                w.write_str(", ")?;
            }
            self.write_decl(w, d, indent)?;
        }
        Ok(())
    }

    /// Writes a paragraph/appended-fact body: a `{ … }` block of formulas.
    fn write_body_block<W: Write>(&self, w: &mut W, body: ExprId, indent: usize) -> fmt::Result {
        if let ExprKind::Block(forms) = &self.ast.exprs[body].kind {
            self.write_block_body(w, forms, indent)
        } else {
            // Bodies are always blocks (parse_block); guard the invariant and
            // still emit reparseable text if it is ever violated.
            debug_assert!(false, "paragraph body is not a Block");
            w.write_str("{\n")?;
            write_indent(w, indent + 1)?;
            self.write_expr(w, body, indent + 1, true, BINDER_BUDGET_TOP)?;
            w.write_char('\n')?;
            write_indent(w, indent)?;
            w.write_char('}')
        }
    }

    /// Writes `{ … }` with one formula per line, 2-space indented; `{}` empty.
    fn write_block_body<W: Write>(
        &self,
        w: &mut W,
        forms: &[ExprId],
        indent: usize,
    ) -> fmt::Result {
        if forms.is_empty() {
            return w.write_str("{}");
        }
        w.write_str("{\n")?;
        for &f in forms {
            write_indent(w, indent + 1)?;
            self.write_expr(w, f, indent + 1, true, BINDER_BUDGET_TOP)?;
            w.write_char('\n')?;
        }
        write_indent(w, indent)?;
        w.write_char('}')
    }
}

fn write_qualname<W: Write>(w: &mut W, q: &QualName) -> fmt::Result {
    for (i, seg) in q.segments.iter().enumerate() {
        if i > 0 {
            w.write_char('/')?;
        }
        w.write_str(&seg.text)?;
    }
    Ok(())
}

// -- Small operator/keyword tables (exhaustive; a new variant must surface) --

fn binop_str(op: BinOp) -> &'static str {
    match op {
        BinOp::Or => "||",
        BinOp::And => "&&",
        BinOp::Iff => "<=>",
        BinOp::Implies => "=>",
        BinOp::Until => "until",
        BinOp::Releases => "releases",
        BinOp::Since => "since",
        BinOp::Triggered => "triggered",
        BinOp::Seq => ";",
        BinOp::Join => ".",
        BinOp::Union => "+",
        BinOp::Diff => "-",
        BinOp::Intersect => "&",
        BinOp::Override => "++",
        BinOp::DomRestrict => "<:",
        BinOp::RanRestrict => ":>",
        BinOp::Shl => "<<",
        BinOp::Sha => ">>",
        BinOp::Shr => ">>>",
        BinOp::IntAdd => "fun/add",
        BinOp::IntSub => "fun/sub",
        BinOp::IntMul => "fun/mul",
        BinOp::IntDiv => "fun/div",
        BinOp::IntRem => "fun/rem",
    }
}

/// The comparison operator's surface text, `!`-prefixed when negated. Each
/// negated spelling re-cooks (F2) to the matching negated-comparison token.
fn cmp_str(op: CmpOp, negated: bool) -> &'static str {
    match (op, negated) {
        (CmpOp::Eq, false) => "=",
        (CmpOp::Eq, true) => "!=",
        (CmpOp::In, false) => "in",
        (CmpOp::In, true) => "!in",
        (CmpOp::Lt, false) => "<",
        (CmpOp::Lt, true) => "!<",
        (CmpOp::Gt, false) => ">",
        (CmpOp::Gt, true) => "!>",
        (CmpOp::Le, false) => "<=",
        (CmpOp::Le, true) => "!<=",
        (CmpOp::Ge, false) => ">=",
        (CmpOp::Ge, true) => "!>=",
    }
}

fn mult_word(m: Mult) -> &'static str {
    match m {
        Mult::Lone => "lone",
        Mult::One => "one",
        Mult::Some => "some",
        Mult::Set => "set",
    }
}

fn sig_mult_word(m: SigMult) -> &'static str {
    match m {
        SigMult::Lone => "lone",
        SigMult::One => "one",
        SigMult::Some => "some",
    }
}

fn quant_word(q: Quant) -> &'static str {
    match q {
        Quant::All => "all",
        Quant::Some => "some",
        Quant::No => "no",
        Quant::Lone => "lone",
        Quant::One => "one",
        Quant::Sum => "sum",
    }
}

fn write_para_name<W: Write>(w: &mut W, name: &ParaName) -> fmt::Result {
    match name {
        ParaName::Ident(id) => w.write_str(&id.text),
        ParaName::Str { value, .. } => write_escaped_str(w, value),
    }
}

fn write_indent<W: Write>(w: &mut W, levels: usize) -> fmt::Result {
    for _ in 0..levels {
        w.write_str("  ")?;
    }
    Ok(())
}

/// Re-escapes a stored (unescaped) string value into a `"…"` literal that
/// re-lexes to the same value (the lexer's only escapes are `\\ \n \"`).
fn write_escaped_str<W: Write>(w: &mut W, value: &str) -> fmt::Result {
    w.write_char('"')?;
    for c in value.chars() {
        match c {
            '\\' => w.write_str("\\\\")?,
            '\n' => w.write_str("\\n")?,
            '"' => w.write_str("\\\"")?,
            other => w.write_char(other)?,
        }
    }
    w.write_char('"')
}

// -- Span-free structural dump (round-trip witness) --------------------------

/// A deterministic, indented tree of the whole AST that includes every
/// semantic field and excludes spans and arena indices.
///
/// Two ASTs are structurally equal iff `dump(a) == dump(b)`; a byte diff of
/// two dumps localizes the first structural divergence. Exhaustive matches
/// (no `_`, `PORTING_RULES` R1) keep it honest as the AST grows.
#[must_use]
pub fn dump(ast: &Ast) -> String {
    let mut out = String::new();
    // Writing to a String is infallible; the fmt::Result is discarded.
    let _ = Dumper { ast }.module(&mut out);
    out
}

struct Dumper<'a> {
    ast: &'a Ast,
}

impl Dumper<'_> {
    fn module(&self, w: &mut String) -> fmt::Result {
        writeln!(w, "Ast")?;
        if let Some(h) = &self.ast.header {
            writeln!(w, "  header {}", join_name(&h.name))?;
            for p in &h.params {
                writeln!(w, "    param {} exact={}", join_name(&p.name), p.is_exact)?;
            }
        }
        for open in &self.ast.opens {
            writeln!(
                w,
                "  open {} private={} alias={}",
                join_name(&open.module),
                open.is_private,
                open.alias.as_ref().map_or("-", |a| a.text.as_str())
            )?;
            for arg in &open.args {
                writeln!(w, "    arg {}", join_name(arg))?;
            }
        }
        for &pid in &self.ast.paragraphs {
            self.para(w, pid)?;
        }
        Ok(())
    }

    fn para(&self, w: &mut String, pid: ParaId) -> fmt::Result {
        match &self.ast.paras[pid] {
            Para::Sig(s) => self.sig(w, s),
            Para::Enum(e) => {
                let names: Vec<&str> = e.variants.iter().map(|v| v.text.as_str()).collect();
                writeln!(w, "  Enum {} [{}]", e.name.text, names.join("|"))
            }
            Para::Fact(f) => {
                writeln!(w, "  Fact {}", para_name(f.name.as_ref()))?;
                self.expr(w, f.body, 2)
            }
            Para::Assert(a) => {
                writeln!(w, "  Assert {}", para_name(a.name.as_ref()))?;
                self.expr(w, a.body, 2)
            }
            Para::Pred(p) => {
                writeln!(
                    w,
                    "  Pred {} recv={} private={}",
                    p.name.text,
                    p.receiver.as_ref().map_or("-".to_owned(), join_name),
                    p.is_private
                )?;
                for &d in &p.params {
                    self.decl(w, d, 2)?;
                }
                self.expr(w, p.body, 2)
            }
            Para::Fun(f) => {
                writeln!(
                    w,
                    "  Fun {} recv={} private={}",
                    f.name.text,
                    f.receiver.as_ref().map_or("-".to_owned(), join_name),
                    f.is_private
                )?;
                for &d in &f.params {
                    self.decl(w, d, 2)?;
                }
                writeln!(w, "    returns")?;
                self.expr(w, f.returns, 3)?;
                writeln!(w, "    body")?;
                self.expr(w, f.body, 3)
            }
            Para::Macro(m) => {
                let params: Vec<&str> = m.params.iter().map(|p| p.text.as_str()).collect();
                writeln!(
                    w,
                    "  Macro {} params=[{}] private={}",
                    m.name.text,
                    params.join("|"),
                    m.is_private
                )?;
                self.expr(w, m.body, 2)
            }
            Para::Cmd(c) => self.cmd(w, c),
        }
    }

    fn sig(&self, w: &mut String, s: &SigDecl) -> fmt::Result {
        let names: Vec<&str> = s.names.iter().map(|n| n.text.as_str()).collect();
        let q = &s.qual;
        let mult = match q.mult {
            None => "-",
            Some(SigMult::Lone) => "lone",
            Some(SigMult::One) => "one",
            Some(SigMult::Some) => "some",
        };
        writeln!(
            w,
            "  Sig [{}] abstract={} var={} private={} mult={}",
            names.join("|"),
            q.is_abstract,
            q.is_var,
            q.is_private,
            mult
        )?;
        match &s.parent {
            SigParent::None => writeln!(w, "    parent None")?,
            SigParent::Extends(p) => writeln!(w, "    parent Extends {}", join_name(p))?,
            SigParent::In(ps) => writeln!(w, "    parent In {}", join_names(ps))?,
            SigParent::Eq(ps) => writeln!(w, "    parent Eq {}", join_names(ps))?,
        }
        for &d in &s.fields {
            self.decl(w, d, 2)?;
        }
        if let Some(fact) = s.fact {
            writeln!(w, "    fact")?;
            self.expr(w, fact, 3)?;
        }
        Ok(())
    }

    fn cmd(&self, w: &mut String, c: &crate::ast::CmdDecl) -> fmt::Result {
        let kind = match c.kind {
            CmdKind::Run => "run",
            CmdKind::Check => "check",
        };
        writeln!(
            w,
            "  Cmd {} label={} followup={}",
            kind,
            c.label.as_ref().map_or("-", |l| l.text.as_str()),
            c.is_followup
        )?;
        match &c.target {
            CmdTarget::Name(q) => writeln!(w, "    target Name {}", join_name(q))?,
            CmdTarget::Block(b) => {
                writeln!(w, "    target Block")?;
                self.expr(w, *b, 3)?;
            }
        }
        if let Some(scope) = &c.scope {
            writeln!(w, "    scope default={:?}", scope.default)?;
            for ts in &scope.entries {
                dump_type_scope(w, ts)?;
            }
        }
        match c.expect {
            None => {}
            Some(Expect::Sat) => writeln!(w, "    expect Sat")?,
            Some(Expect::Unsat) => writeln!(w, "    expect Unsat")?,
            Some(Expect::Other(n)) => writeln!(w, "    expect Other({n})")?,
        }
        Ok(())
    }

    fn decl(&self, w: &mut String, d: DeclId, indent: usize) -> fmt::Result {
        let decl: &Decl = &self.ast.decls[d];
        let names: Vec<&str> = decl.names.iter().map(|n| n.text.as_str()).collect();
        write_pad(w, indent)?;
        writeln!(
            w,
            "decl [{}] disj={} bound_disj={} var={} private={}",
            names.join("|"),
            decl.is_disj,
            decl.is_bound_disj,
            decl.is_var,
            decl.is_private
        )?;
        self.expr(w, decl.bound, indent + 1)
    }

    fn expr(&self, w: &mut String, e: ExprId, indent: usize) -> fmt::Result {
        write_pad(w, indent)?;
        match &self.ast.exprs[e].kind {
            ExprKind::Num(n) => writeln!(w, "Num {n}"),
            ExprKind::Str(s) => writeln!(w, "Str {s:?}"),
            ExprKind::Const(c) => writeln!(w, "Const {c:?}"),
            ExprKind::This => writeln!(w, "This"),
            ExprKind::Name(q) => writeln!(w, "Name {}", join_name(q)),
            ExprKind::AtName(q) => writeln!(w, "AtName {}", join_name(q)),
            ExprKind::Unary { op, expr } => {
                let inner = *expr;
                writeln!(w, "Unary {op:?}")?;
                self.expr(w, inner, indent + 1)
            }
            ExprKind::Binary { op, lhs, rhs } => {
                let (lhs, rhs) = (*lhs, *rhs);
                writeln!(w, "Binary {op:?}")?;
                self.expr(w, lhs, indent + 1)?;
                self.expr(w, rhs, indent + 1)
            }
            ExprKind::Arrow {
                lhs,
                lhs_mult,
                rhs_mult,
                rhs,
            } => {
                let (lhs, rhs) = (*lhs, *rhs);
                writeln!(w, "Arrow lhs_mult={lhs_mult:?} rhs_mult={rhs_mult:?}")?;
                self.expr(w, lhs, indent + 1)?;
                self.expr(w, rhs, indent + 1)
            }
            ExprKind::Compare {
                op,
                negated,
                lhs,
                rhs,
            } => {
                let (lhs, rhs) = (*lhs, *rhs);
                writeln!(w, "Compare {op:?} negated={negated}")?;
                self.expr(w, lhs, indent + 1)?;
                self.expr(w, rhs, indent + 1)
            }
            ExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => {
                let (cond, then_branch, else_branch) = (*cond, *then_branch, *else_branch);
                writeln!(w, "IfThenElse")?;
                self.expr(w, cond, indent + 1)?;
                self.expr(w, then_branch, indent + 1)?;
                self.expr(w, else_branch, indent + 1)
            }
            ExprKind::BoxJoin { target, args } => {
                writeln!(w, "BoxJoin")?;
                self.expr(w, *target, indent + 1)?;
                for &arg in args {
                    self.expr(w, arg, indent + 1)?;
                }
                Ok(())
            }
            ExprKind::Quant { quant, decls, body } => {
                writeln!(w, "Quant {quant:?}")?;
                for &d in decls {
                    self.decl(w, d, indent + 1)?;
                }
                self.expr(w, *body, indent + 1)
            }
            ExprKind::Comprehension { decls, body } => {
                writeln!(w, "Comprehension")?;
                for &d in decls {
                    self.decl(w, d, indent + 1)?;
                }
                self.expr(w, *body, indent + 1)
            }
            ExprKind::Let { bindings, body } => {
                writeln!(w, "Let")?;
                for b in bindings {
                    write_pad(w, indent + 1)?;
                    writeln!(w, "bind {}", b.name.text)?;
                    self.expr(w, b.value, indent + 2)?;
                }
                self.expr(w, *body, indent + 1)
            }
            ExprKind::Block(forms) => {
                writeln!(w, "Block")?;
                for &f in forms {
                    self.expr(w, f, indent + 1)?;
                }
                Ok(())
            }
        }
    }
}

fn write_pad(w: &mut String, indent: usize) -> fmt::Result {
    for _ in 0..indent {
        w.write_str("  ")?;
    }
    Ok(())
}

/// A qualified name's segments joined by `|` — unambiguous in the dump because
/// `|` is never an identifier character, so `[pred/totalOrder]` (one segment)
/// and `[a|b]` (two segments) never collide.
fn join_name(q: &QualName) -> String {
    q.segments
        .iter()
        .map(|s| s.text.as_str())
        .collect::<Vec<_>>()
        .join("|")
}

fn join_names(qs: &[QualName]) -> String {
    qs.iter().map(join_name).collect::<Vec<_>>().join(" + ")
}

fn dump_type_scope(w: &mut String, ts: &TypeScope) -> fmt::Result {
    let end = match ts.end {
        ScopeEnd::Same => "Same".to_owned(),
        ScopeEnd::Bounded(m) => format!("Bounded({m})"),
        ScopeEnd::Unbounded => "Unbounded".to_owned(),
    };
    let target = match &ts.target {
        ScopeTarget::Sig(q) => format!("Sig {}", join_name(q)),
        ScopeTarget::Int => "Int".to_owned(),
        ScopeTarget::Seq => "Seq".to_owned(),
        ScopeTarget::Str => "Str".to_owned(),
        ScopeTarget::Steps => "Steps".to_owned(),
    };
    writeln!(
        w,
        "      entry exact={} start={} end={} inc={:?} target={}",
        ts.is_exact, ts.start, end, ts.increment, target
    )
}

fn para_name(name: Option<&ParaName>) -> String {
    match name {
        None => "-".to_owned(),
        Some(ParaName::Ident(id)) => format!("ident:{}", id.text),
        Some(ParaName::Str { value, .. }) => format!("str:{value:?}"),
    }
}

#[cfg(test)]
mod tests;
