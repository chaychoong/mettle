//! IR lowering + goal assembly: the third translation phase (mt-031,
//! translation-ref §2). [`lower_command`] turns the resolved, type-checked
//! surface AST of one command into the single three-sorted-IR goal
//! ([`crate::ir`]) that the CNF encoder (mt-033) and solver (mt-032) consume.
//!
//! **Semantics faithful, structure idiomatic** (PORTING prime directive): a
//! bottom-up walk over the surface [`als_syntax::ast::Expr`], dispatching every
//! name / join / call at the exact point the reference does — but it **never
//! re-derives §4.4 resolution**. The mt-025 checker already recorded, for every
//! name and application spine, what it chose ([`als_types::choice`]); the
//! lowerer replays those choices ([`als_types::ChoiceTable`]) so name binding,
//! overload choice, implicit-`this` insertion, and macro expansion are read, not
//! recomputed (they took two beads to get right — duplication is drift).
//!
//! ## The goal (translation-ref §2.5), conjoined in order
//! 1. the bounds builder's constraint formulas (sibling disjointness, subset
//!    containment, **sig size/multiplicity** — mt-030 owns these, so the lowerer
//!    never re-emits them);
//! 2. every reachable module's **facts**;
//! 3. **synthesized field facts** — each field's declaration multiplicity
//!    (`all this: S | one this.f and this.f in bound`), domain (`f.univ… in S`),
//!    and defined-field value (`all this: S | this.f = e`);
//! 4. **sig appended facts** (`sig A {…}{ φ }`, with `this` bound to `A`);
//! 5. the **command formula** — a `run` pred body (params existentially
//!    quantified), a `run`/`check` block as-is/negated, or a `check` assertion
//!    body negated.
//!
//! The reference's §2.5(4) reflexive `r = r` padding is **not** emitted here: it
//! is a Kodkod solving detail (keeping unreferenced relations alive), and mt-033
//! owns it — see the note there.
//!
//! ## Deferred, as **typed** errors (never a silent skip, never a wrong verdict)
//! - **Temporal** operators (`always`/`until`/`'`/`var`) lower faithfully into
//!   the IR temporal kinds but the command then reports
//!   [`TranslateError::TemporalUnsupported`] (bounded LTL→FOL is Rung 6).
//! - **String literals** → [`TranslateError::StringUnsupported`] (Rung 4).
//! - Exotic field multiplicity shapes, higher-order (lean) macros, and
//!   unhandled command-target shapes → [`TranslateError::LoweringUnsupported`].
//! - **Skolemization is skipped** (ADR-0011 / translation-ref §2.3): quantifiers
//!   are lowered directly. Skolem relations never appear in instances; this is
//!   never a verdict change (recorded in LIMITATIONS).

// Pervasive, harmless stylistic lints in this walk: `e`/`a`/`b`/`l`/`r` are the
// domain-idiomatic names for expression ids and operands (STYLE N4); several
// `match` arms over distinct `ExprKind`/choice variants share a body (a sort
// classification), which is clearer left un-merged; `choice`/`sort_of` helpers
// read as methods though a couple do not touch `self`.
#![allow(
    clippy::many_single_char_names,
    clippy::match_same_arms,
    clippy::unused_self
)]

use als_syntax::ast::{Ast, BinOp, CmpOp, Const, Decl, ExprId, ExprKind, Mult, Quant, UnOp};
use als_syntax::{ArenaId, Span};
use als_types::choice::{BuiltinCall, ExprChoice, NameChoice, SpineChoice};
use als_types::{
    ChoiceTable, CmdTargetResolved, FieldId, ModuleGraph, ModuleId, ResolvedWorld, SigId,
};

use crate::bounds_builder::BoundsResult;
use crate::error::TranslateError;
use crate::ir::{
    CompDecl, Formula, FormulaId, FormulaKind, IntBinOp, IntCmpOp, IntExpr, IntExprId, IntExprKind,
    Ir, MultTest, QuantKind, RelBinOp, RelCmpOp, RelConst, RelExpr, RelExprId, RelExprKind,
    RelUnOp, TemporalBinOp, TemporalUnOp, Var,
};
use crate::scope::ScopedUniverse;

/// The lowered command goal (mt-031) and its provenance-labeled top-level
/// conjuncts (bookkeeping for mt-033's CNF encoder and for debugging).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LoweredGoal {
    /// The single goal formula: the conjunction of every conjunct below.
    pub goal: FormulaId,
    /// The top-level conjuncts with provenance, in §2.5 order.
    pub conjuncts: Vec<GoalConjunct>,
}

/// One top-level conjunct of the goal, with where it came from.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct GoalConjunct {
    /// The conjunct formula.
    pub formula: FormulaId,
    /// Its origin (translation-ref §2.5).
    pub provenance: Provenance,
}

/// Where a top-level goal conjunct came from (translation-ref §2.5).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Provenance {
    /// A bounds-builder constraint (sig disjointness/subset/size/mult, mt-030).
    BoundsConstraint,
    /// A reachable module fact.
    Fact,
    /// A synthesized field fact (multiplicity / domain / defined value).
    FieldFact(FieldId),
    /// A sig appended fact (`this` bound to the owning sig).
    AppendedFact(SigId),
    /// The command formula.
    Command,
}

/// Lowers command `command_index` into the shared [`Ir`], producing the goal
/// (translation-ref §2). Consumes mt-029's [`ScopedUniverse`] and mt-030's
/// [`BoundsResult`] (denotation seam + constraint formulas); reads the resolved
/// choices from `world.choices`.
///
/// # Errors
/// A [`TranslateError`] for a deferred construct (temporal / string / exotic
/// field shape / unhandled target) — never a wrong verdict.
pub fn lower_command(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    scoped: &ScopedUniverse,
    bounds: &BoundsResult,
    ir: &mut Ir,
    command_index: usize,
) -> Result<LoweredGoal, TranslateError> {
    // `scoped` (the universe/bitwidth) is not needed for lowering itself — the
    // bounds builder already consumed it into the denotation seam. It stays in
    // the signature for mt-033 (CNF encoding needs the universe).
    let _ = scoped;
    let mut lowerer = Lowerer {
        world,
        graph,
        bounds,
        ir,
        binders: Vec::new(),
        inline_stack: Vec::new(),
        temporal: None,
    };
    lowerer.lower(command_index)
}

/// A lexical binding active during lowering: mirrors the checker's env so a
/// `NameChoice::Var` resolves to the right IR node (innermost-wins shadowing).
#[derive(Clone)]
enum Binding {
    /// A quantifier / comprehension / `sum` variable → an IR relation variable.
    Var(crate::ir::VarId),
    /// A `let` binding, a func/pred parameter, or a macro argument → the
    /// already-lowered value expression (substituted in place, the reference's
    /// inlining).
    Expr(RelExprId),
}

/// A resolution context: the module the expression lives in and the choice
/// table to read (the world's top table, or a macro body's nested table).
#[derive(Copy, Clone)]
struct Ctx<'a> {
    module: ModuleId,
    choices: &'a ChoiceTable,
}

/// The three sorts an expression can lower to (translation-ref §2), decided
/// from the recorded choices — never a re-derivation of the §4 type checker.
#[derive(Copy, Clone, PartialEq, Eq)]
enum Sort {
    Formula,
    Int,
    Rel,
}

struct Lowerer<'a> {
    world: &'a ResolvedWorld,
    graph: &'a ModuleGraph,
    bounds: &'a BoundsResult,
    ir: &'a mut Ir,
    /// Active lexical bindings (innermost last).
    binders: Vec<(String, Binding)>,
    /// Funcs/preds currently being inlined (recursion guard — the reference
    /// rejects recursive funcs/preds; mettle refuses rather than looping).
    inline_stack: Vec<FuncIdx>,
    /// The first temporal construct hit (deferred at the end, translation-ref
    /// §2.3): `(op, span)`.
    temporal: Option<(&'static str, Span)>,
}

impl<'a> Lowerer<'a> {
    // =============================== driver ===============================

    fn lower(&mut self, command_index: usize) -> Result<LoweredGoal, TranslateError> {
        let cmd = self.world.commands.get(command_index).ok_or_else(|| {
            TranslateError::LoweringUnsupported {
                what: "command index out of range".to_owned(),
                span: als_types_synthetic_span(),
            }
        })?;
        let mut conjuncts: Vec<GoalConjunct> = Vec::new();

        // 1. bounds-builder constraints (mt-030 owns sig size/mult/disjoint).
        for &f in &self.bounds.constraints {
            conjuncts.push(GoalConjunct {
                formula: f,
                provenance: Provenance::BoundsConstraint,
            });
        }

        // 2. every reachable module fact.
        for fact in &self.world.facts {
            let ctx = self.ctx(fact.module);
            let f = self.lower_formula(ctx, fact.body)?;
            conjuncts.push(GoalConjunct {
                formula: f,
                provenance: Provenance::Fact,
            });
        }

        // 3. synthesized field facts.
        for (fid, field) in self.world.fields.iter() {
            if let Some(f) = self.lower_field_facts(fid)? {
                conjuncts.push(GoalConjunct {
                    formula: f,
                    provenance: Provenance::FieldFact(fid),
                });
            }
            let _ = field;
        }

        // 4. sig appended facts (`this` bound to the owning sig).
        for (sig, s) in self.world.sigs.iter() {
            if let Some(body) = s.appended_fact {
                let f = self.lower_appended_fact(sig, s.module, body)?;
                conjuncts.push(GoalConjunct {
                    formula: f,
                    provenance: Provenance::AppendedFact(sig),
                });
            }
        }

        // 5. the command formula.
        let cmd_f = self.lower_command_formula(command_index)?;
        conjuncts.push(GoalConjunct {
            formula: cmd_f,
            provenance: Provenance::Command,
        });

        // Defer if any temporal operator was lowered (translation-ref §2.3).
        if let Some((op, span)) = self.temporal {
            return Err(TranslateError::TemporalUnsupported { op, span });
        }

        let goal = self.conjoin(conjuncts.iter().map(|c| c.formula).collect(), cmd.span);
        Ok(LoweredGoal { goal, conjuncts })
    }

    /// Builds the command formula (translation-ref §2.5(3)).
    fn lower_command_formula(&mut self, command_index: usize) -> Result<FormulaId, TranslateError> {
        let cmd = &self.world.commands[command_index];
        let is_check = matches!(cmd.kind, als_syntax::ast::CmdKind::Check);
        let span = cmd.span;
        match cmd.target.clone() {
            CmdTargetResolved::Block { body, module } => {
                let ctx = self.ctx(module);
                let f = self.lower_formula(ctx, body)?;
                Ok(if is_check { self.not(f, span) } else { f })
            }
            CmdTargetResolved::Assert { body, module } => {
                // `check a`: the assertion body, negated (SAT = counterexample).
                let ctx = self.ctx(module);
                let f = self.lower_formula(ctx, body)?;
                Ok(self.not(f, span))
            }
            CmdTargetResolved::Named(funcs) => {
                if is_check {
                    return Err(TranslateError::LoweringUnsupported {
                        what: "`check` on a named pred/fun".to_owned(),
                        span,
                    });
                }
                let &func = funcs
                    .first()
                    .ok_or_else(|| TranslateError::LoweringUnsupported {
                        what: "empty run target".to_owned(),
                        span,
                    })?;
                if funcs.len() > 1 {
                    return Err(TranslateError::LoweringUnsupported {
                        what: "overloaded run target".to_owned(),
                        span,
                    });
                }
                let f = &self.world.funcs[func];
                if !f.is_pred {
                    return Err(TranslateError::LoweringUnsupported {
                        what: "`run` on a fun".to_owned(),
                        span,
                    });
                }
                // Existentially quantify the params over their bounds, then the
                // body (translation-ref §2.5(3)).
                self.run_pred(func, span)
            }
            CmdTargetResolved::Unresolved => Err(TranslateError::LoweringUnsupported {
                what: "unresolved command target".to_owned(),
                span,
            }),
        }
    }

    /// `run p`: `some x1: B1, …, xn: Bn | body` — the pred's params existentially
    /// quantified over their declaration bounds (translation-ref §2.5(3)). A
    /// receiver param (`pred A.p`) is quantified over its sig `A`.
    fn run_pred(&mut self, func: FuncIdx, span: Span) -> Result<FormulaId, TranslateError> {
        let module = self.world.funcs[func].module;
        let body = self.world.funcs[func].body;
        let ctx = self.ctx(module);
        let Some(para) = self.find_func_para(module, func) else {
            return Err(TranslateError::LoweringUnsupported {
                what: "run pred: declaration not found".to_owned(),
                span,
            });
        };
        let ast = self.ast(module);
        let (receiver, param_decls) = match &ast.paras[para] {
            als_syntax::ast::Para::Pred(p) => (p.receiver.clone(), p.params.clone()),
            als_syntax::ast::Para::Fun(f) => (f.receiver.clone(), f.params.clone()),
            _ => (None, Vec::new()),
        };
        let mut var_bounds: Vec<(crate::ir::VarId, RelExprId)> = Vec::new();
        let mut pushed = 0usize;
        // Receiver `this` over its sig.
        if let Some(recv) = receiver {
            let sig = self.world.funcs[func]
                .params
                .first()
                .map(|_| ())
                .and_then(|()| {
                    // The receiver sig is the type of param 0 (`this`); recover it via
                    // the receiver name lookup.
                    self.lookup_sig_by_name(module, &recv)
                });
            let Some(sig) = sig else {
                return Err(TranslateError::LoweringUnsupported {
                    what: "run pred: unresolved receiver sig".to_owned(),
                    span,
                });
            };
            let bound = self.sig_denote(sig, span)?;
            let vid = self.ir.vars.alloc(Var {
                name: "this".to_owned(),
                arity: 1,
                span,
            });
            var_bounds.push((vid, bound));
            self.binders.push(("this".to_owned(), Binding::Var(vid)));
            pushed += 1;
        }
        for &d in &param_decls {
            let decl = ast.decls[d].clone();
            let bound = self.lower_decl_bound_set(ctx, &decl)?;
            for name in &decl.names {
                let vid = self.ir.vars.alloc(Var {
                    name: name.text.clone(),
                    arity: 1,
                    span: name.span,
                });
                var_bounds.push((vid, bound));
                self.binders.push((name.text.clone(), Binding::Var(vid)));
                pushed += 1;
            }
        }
        let body_f = self.lower_formula(ctx, body);
        for _ in 0..pushed {
            self.binders.pop();
        }
        let mut acc = body_f?;
        for (vid, bound) in var_bounds.into_iter().rev() {
            acc = self.mk_formula(
                FormulaKind::Quant {
                    kind: QuantKind::Some,
                    var: vid,
                    bound,
                    body: acc,
                },
                span,
            );
        }
        Ok(acc)
    }

    /// Looks up the sig a (possibly qualified) receiver name denotes, in a
    /// module's scope, via the resolved sigs' qualified names.
    fn lookup_sig_by_name(
        &self,
        module: ModuleId,
        name: &als_syntax::ast::QualName,
    ) -> Option<SigId> {
        let bare = name.segments.last()?.text.clone();
        let _ = module;
        self.world
            .sigs
            .iter()
            .find(|(_, s)| s.name == bare && !s.is_builtin)
            .map(|(id, _)| id)
    }

    // ============================ field facts ============================

    /// Synthesizes a field's declaration facts (translation-ref §2.5): domain
    /// (`f.univ… in owner`), per-declaration multiplicity + bound membership
    /// (`all this: S | mult(this.f) and this.f in bound`), or, for a defined
    /// field, `all this: S | this.f = e`. Returns `None` when there is nothing to
    /// add (a field whose bounds fully pin it).
    fn lower_field_facts(&mut self, fid: FieldId) -> Result<Option<FormulaId>, TranslateError> {
        let field = self.world.fields[fid].clone();
        let owner = field.owner;
        let module = self.world.sigs[owner].module;
        let ctx = self.ctx(module);
        let span = field.span;
        let field_denote = *self.bounds.field_denote.get(&fid).ok_or_else(|| {
            TranslateError::LoweringUnsupported {
                what: format!("field `{}` has no denotation", field.name),
                span,
            }
        })?;
        let owner_denote = self.sig_denote(owner, span)?;

        // `this` ranges over the owner; `this.f` is the value.
        let this_var = self.ir.vars.alloc(Var {
            name: "this".to_owned(),
            arity: 1,
            span,
        });
        let this_expr = self.mk_rel(RelExprKind::Var(this_var), span);
        let this_f = self.mk_rel(
            RelExprKind::Binary {
                op: RelBinOp::Join,
                lhs: this_expr,
                rhs: field_denote,
            },
            span,
        );

        let mut body_parts: Vec<FormulaId> = Vec::new();
        if field.is_defined {
            // `= e`: bound is `ExactlyOf(e)`; lower `e` in a `this`-context.
            let value = unwrap_exactly(self.ast(module), field.bound).ok_or_else(|| {
                TranslateError::LoweringUnsupported {
                    what: format!("defined field `{}` malformed bound", field.name),
                    span,
                }
            })?;
            self.binders
                .push(("this".to_owned(), Binding::Var(this_var)));
            let e = self.lower_rel(ctx, value);
            self.binders.pop();
            let e = e?;
            body_parts.push(self.mk_formula(
                FormulaKind::RelCompare {
                    op: RelCmpOp::Equal,
                    lhs: this_f,
                    rhs: e,
                },
                span,
            ));
        } else {
            // Multiplicity + membership from the declaration bound shape.
            self.binders
                .push(("this".to_owned(), Binding::Var(this_var)));
            let mult = self.field_mult_constraint(ctx, this_f, field.bound, span);
            self.binders.pop();
            body_parts.extend(mult?);
        }

        // `all this: owner | <body>` (only when there is a body).
        let quant = if body_parts.is_empty() {
            None
        } else {
            let body = self.conjoin(body_parts, span);
            Some(self.mk_formula(
                FormulaKind::Quant {
                    kind: QuantKind::All,
                    var: this_var,
                    bound: owner_denote,
                    body,
                },
                span,
            ))
        };

        // Domain constraint `(f.univ…) in owner` — the field's first column
        // lies in the owner (translation-ref §2.5, jar-verified). Arity = the
        // field's full arity; join `univ` (arity-1) `arity-1` times to project to
        // the first column.
        let full_arity = self.world.fields[fid].ty.arity().filter(|&a| a >= 2);
        let domain = if let Some(arity) = full_arity {
            let mut proj = field_denote;
            let univ = self.mk_rel(RelExprKind::Const(RelConst::Univ), span);
            for _ in 0..(arity - 1) {
                proj = self.mk_rel(
                    RelExprKind::Binary {
                        op: RelBinOp::Join,
                        lhs: proj,
                        rhs: univ,
                    },
                    span,
                );
            }
            Some(self.mk_formula(
                FormulaKind::RelCompare {
                    op: RelCmpOp::Subset,
                    lhs: proj,
                    rhs: owner_denote,
                },
                span,
            ))
        } else {
            None
        };

        match (quant, domain) {
            (Some(q), Some(d)) => Ok(Some(self.conjoin(vec![q, d], span))),
            (Some(q), None) => Ok(Some(q)),
            (None, Some(d)) => Ok(Some(d)),
            (None, None) => Ok(None),
        }
    }

    /// The per-declaration field multiplicity + membership constraints on
    /// `this_f = this.f`, from the declaration bound expression `bound`
    /// (translation-ref §2.1/§2.5): a plain unary bound gets an implicit `one`;
    /// `set`/`some`/`lone`/`one` markers set the multiplicity; a single arrow
    /// `A m -> n B` adds per-column multiplicity quantifiers. Deeper/exotic
    /// shapes defer.
    fn field_mult_constraint(
        &mut self,
        ctx: Ctx,
        this_f: RelExprId,
        bound: ExprId,
        span: Span,
    ) -> Result<Vec<FormulaId>, TranslateError> {
        let ast = self.ast(ctx.module);
        match &ast.exprs[bound].kind {
            // Multiplicity markers on a unary/relation bound.
            ExprKind::Unary { op, expr } if is_mult_marker(*op) => {
                let inner = *expr;
                let rel = self.lower_rel(ctx, inner)?;
                let membership = self.mk_formula(
                    FormulaKind::RelCompare {
                        op: RelCmpOp::Subset,
                        lhs: this_f,
                        rhs: rel,
                    },
                    span,
                );
                let mut out = vec![membership];
                if let Some(test) = mult_of_marker(*op) {
                    out.push(self.mk_formula(FormulaKind::MultTest { test, expr: this_f }, span));
                }
                Ok(out)
            }
            // A single arrow product with (optional) column multiplicities.
            ExprKind::Arrow {
                lhs,
                lhs_mult,
                rhs_mult,
                rhs,
            } => self.arrow_field_constraint(ctx, this_f, *lhs, *lhs_mult, *rhs_mult, *rhs, span),
            // A plain relation bound: implicit `one` for a unary value.
            _ => {
                let rel = self.lower_rel(ctx, bound)?;
                let membership = self.mk_formula(
                    FormulaKind::RelCompare {
                        op: RelCmpOp::Subset,
                        lhs: this_f,
                        rhs: rel,
                    },
                    span,
                );
                let mut out = vec![membership];
                // Implicit `one` when the value is unary (arity of this.f == 1).
                if self.rel_value_arity(bound, ctx) == Some(1) {
                    out.push(self.mk_formula(
                        FormulaKind::MultTest {
                            test: MultTest::One,
                            expr: this_f,
                        },
                        span,
                    ));
                }
                Ok(out)
            }
        }
    }

    /// A single-arrow field bound `A m -> n B` (arity-2 value): membership
    /// `this.f in A->B`, plus per-column multiplicity — `all a: A | n (a.this.f)`
    /// and `all b: B | m ((this.f).b)` (translation-ref §2.1 arrow row).
    #[allow(clippy::too_many_arguments)]
    fn arrow_field_constraint(
        &mut self,
        ctx: Ctx,
        this_f: RelExprId,
        lhs: ExprId,
        lhs_mult: Option<Mult>,
        rhs_mult: Option<Mult>,
        rhs: ExprId,
        span: Span,
    ) -> Result<Vec<FormulaId>, TranslateError> {
        // Only a flat binary arrow (both sides unary) is handled; nested arrows
        // or a non-unary side defer (never a wrong constraint).
        if matches!(
            &self.ast(ctx.module).exprs[lhs].kind,
            ExprKind::Arrow { .. }
        ) || matches!(
            &self.ast(ctx.module).exprs[rhs].kind,
            ExprKind::Arrow { .. }
        ) {
            return Err(TranslateError::LoweringUnsupported {
                what: "nested multiplicity arrow in a field bound".to_owned(),
                span,
            });
        }
        let a = self.lower_rel(ctx, lhs)?;
        let b = self.lower_rel(ctx, rhs)?;
        let product = self.mk_rel(
            RelExprKind::Binary {
                op: RelBinOp::Product,
                lhs: a,
                rhs: b,
            },
            span,
        );
        let membership = self.mk_formula(
            FormulaKind::RelCompare {
                op: RelCmpOp::Subset,
                lhs: this_f,
                rhs: product,
            },
            span,
        );
        let mut out = vec![membership];
        // Right multiplicity `n` on B: `all a: A | n (a . this.f)`.
        if let Some(test) = mult_test_of(rhs_mult) {
            let av = self.ir.vars.alloc(Var {
                name: "_c0".to_owned(),
                arity: 1,
                span,
            });
            let ave = self.mk_rel(RelExprKind::Var(av), span);
            let image = self.mk_rel(
                RelExprKind::Binary {
                    op: RelBinOp::Join,
                    lhs: ave,
                    rhs: this_f,
                },
                span,
            );
            let inner = self.mk_formula(FormulaKind::MultTest { test, expr: image }, span);
            out.push(self.mk_formula(
                FormulaKind::Quant {
                    kind: QuantKind::All,
                    var: av,
                    bound: a,
                    body: inner,
                },
                span,
            ));
        }
        // Left multiplicity `m` on A: `all b: B | m (this.f . b)`.
        if let Some(test) = mult_test_of(lhs_mult) {
            let bv = self.ir.vars.alloc(Var {
                name: "_c1".to_owned(),
                arity: 1,
                span,
            });
            let bve = self.mk_rel(RelExprKind::Var(bv), span);
            let preimage = self.mk_rel(
                RelExprKind::Binary {
                    op: RelBinOp::Join,
                    lhs: this_f,
                    rhs: bve,
                },
                span,
            );
            let inner = self.mk_formula(
                FormulaKind::MultTest {
                    test,
                    expr: preimage,
                },
                span,
            );
            out.push(self.mk_formula(
                FormulaKind::Quant {
                    kind: QuantKind::All,
                    var: bv,
                    bound: b,
                    body: inner,
                },
                span,
            ));
        }
        Ok(out)
    }

    /// A sig appended fact `sig A {…}{ φ }` — `φ` with `this` bound to `A`
    /// (translation-ref §2.5, resolution §3.3). Unlike a field/module fact it is
    /// `all this: A | φ` (the appended block holds for every atom of `A`).
    fn lower_appended_fact(
        &mut self,
        sig: SigId,
        module: ModuleId,
        body: ExprId,
    ) -> Result<FormulaId, TranslateError> {
        let span = self.world.sigs[sig].span;
        let ctx = self.ctx(module);
        let sig_denote = self.sig_denote(sig, span)?;
        let this_var = self.ir.vars.alloc(Var {
            name: "this".to_owned(),
            arity: 1,
            span,
        });
        self.binders
            .push(("this".to_owned(), Binding::Var(this_var)));
        let inner = self.lower_formula(ctx, body);
        self.binders.pop();
        let inner = inner?;
        Ok(self.mk_formula(
            FormulaKind::Quant {
                kind: QuantKind::All,
                var: this_var,
                bound: sig_denote,
                body: inner,
            },
            span,
        ))
    }

    // ============================ formulas ============================

    #[allow(clippy::too_many_lines)]
    fn lower_formula(&mut self, ctx: Ctx, e: ExprId) -> Result<FormulaId, TranslateError> {
        let node = self.ast(ctx.module).exprs[e].clone();
        let span = node.span;
        match node.kind {
            ExprKind::Block(exprs) => {
                let mut parts = Vec::with_capacity(exprs.len());
                for f in exprs {
                    parts.push(self.lower_formula(ctx, f)?);
                }
                Ok(self.conjoin(parts, span))
            }
            ExprKind::Compare {
                op,
                negated,
                lhs,
                rhs,
            } => {
                let f = self.lower_compare(ctx, op, lhs, rhs, span)?;
                Ok(if negated { self.not(f, span) } else { f })
            }
            ExprKind::Unary { op, expr } => self.lower_unary_formula(ctx, op, expr, span),
            // A `.`-join in formula position is a pred call spine.
            ExprKind::Binary {
                op: BinOp::Join, ..
            } => self.lower_call_formula(ctx, e, span),
            ExprKind::Binary { op, lhs, rhs } => self.lower_binary_formula(ctx, op, lhs, rhs, span),
            ExprKind::Quant { quant, decls, body } => {
                self.lower_quant(ctx, quant, &decls, body, span)
            }
            ExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => {
                // A formula-valued ITE: `(cond and then) or (not cond and else)`.
                let c = self.lower_formula(ctx, cond)?;
                let t = self.lower_formula(ctx, then_branch)?;
                let el = self.lower_formula(ctx, else_branch)?;
                let nc = self.not(c, span);
                let a = self.mk_formula(FormulaKind::And(vec![c, t]), span);
                let b = self.mk_formula(FormulaKind::And(vec![nc, el]), span);
                Ok(self.mk_formula(FormulaKind::Or(vec![a, b]), span))
            }
            ExprKind::Let { bindings, body } => {
                let mut pushed = 0;
                for b in &bindings {
                    let v = self.lower_rel(ctx, b.value)?;
                    self.binders.push((b.name.text.clone(), Binding::Expr(v)));
                    pushed += 1;
                }
                let r = self.lower_formula(ctx, body);
                for _ in 0..pushed {
                    self.binders.pop();
                }
                r
            }
            // A spine / name that resolves to a pred call or a 0-ary pred.
            ExprKind::BoxJoin { .. } | ExprKind::Name(_) | ExprKind::AtName(_) => {
                self.lower_call_formula(ctx, e, span)
            }
            ExprKind::This | ExprKind::Num(_) | ExprKind::Str(_) | ExprKind::Const(_) => {
                Err(TranslateError::LoweringUnsupported {
                    what: "non-formula in a formula position".to_owned(),
                    span,
                })
            }
            ExprKind::Arrow { .. } | ExprKind::Comprehension { .. } => {
                Err(TranslateError::LoweringUnsupported {
                    what: "non-formula expression in a formula position".to_owned(),
                    span,
                })
            }
        }
    }

    /// A name/spine in formula position: a 0-ary pred value or a pred call →
    /// inline the pred body; a builtin `disj[…]`/`pred/totalOrder[…]`.
    fn lower_call_formula(
        &mut self,
        ctx: Ctx,
        e: ExprId,
        span: Span,
    ) -> Result<FormulaId, TranslateError> {
        match self.choice(ctx, e) {
            Some(ExprChoice::Name(NameChoice::Call0(func))) => {
                self.inline_pred(ctx, *func, &[], span)
            }
            Some(ExprChoice::Name(NameChoice::Macro(mc))) => {
                let mc = mc.clone();
                self.replay_macro_formula(&mc, span)
            }
            Some(ExprChoice::Spine(SpineChoice::Call(cc))) => {
                let cc = cc.clone();
                self.inline_pred(ctx, cc.func, &cc.args, span)
            }
            Some(ExprChoice::Spine(SpineChoice::Builtin { op })) => {
                self.lower_builtin_formula(ctx, *op, e, span)
            }
            Some(ExprChoice::Spine(SpineChoice::Macro(mc))) => {
                let mc = mc.clone();
                self.replay_macro_formula(&mc, span)
            }
            _ => Err(TranslateError::LoweringUnsupported {
                what: "unrecognized formula-position spine".to_owned(),
                span,
            }),
        }
    }

    fn lower_unary_formula(
        &mut self,
        ctx: Ctx,
        op: UnOp,
        expr: ExprId,
        span: Span,
    ) -> Result<FormulaId, TranslateError> {
        match op {
            UnOp::Not => {
                let f = self.lower_formula(ctx, expr)?;
                Ok(self.not(f, span))
            }
            UnOp::No | UnOp::Some | UnOp::Lone | UnOp::One => {
                let r = self.lower_rel(ctx, expr)?;
                let test = match op {
                    UnOp::No => MultTest::No,
                    UnOp::Some => MultTest::Some,
                    UnOp::Lone => MultTest::Lone,
                    UnOp::One => MultTest::One,
                    _ => unreachable!(),
                };
                Ok(self.mk_formula(FormulaKind::MultTest { test, expr: r }, span))
            }
            UnOp::Always
            | UnOp::Eventually
            | UnOp::After
            | UnOp::Before
            | UnOp::Historically
            | UnOp::Once => {
                let body = self.lower_formula(ctx, expr)?;
                let (kind, name) = temporal_un(op);
                self.mark_temporal(name, span);
                Ok(self.mk_formula(FormulaKind::TemporalUnary { op: kind, body }, span))
            }
            _ => Err(TranslateError::LoweringUnsupported {
                what: "unary operator in a formula position".to_owned(),
                span,
            }),
        }
    }

    fn lower_binary_formula(
        &mut self,
        ctx: Ctx,
        op: BinOp,
        lhs: ExprId,
        rhs: ExprId,
        span: Span,
    ) -> Result<FormulaId, TranslateError> {
        match op {
            BinOp::And => {
                let l = self.lower_formula(ctx, lhs)?;
                let r = self.lower_formula(ctx, rhs)?;
                Ok(self.mk_formula(FormulaKind::And(vec![l, r]), span))
            }
            BinOp::Or => {
                let l = self.lower_formula(ctx, lhs)?;
                let r = self.lower_formula(ctx, rhs)?;
                Ok(self.mk_formula(FormulaKind::Or(vec![l, r]), span))
            }
            BinOp::Implies => {
                let l = self.lower_formula(ctx, lhs)?;
                let r = self.lower_formula(ctx, rhs)?;
                Ok(self.mk_formula(
                    FormulaKind::Implies {
                        antecedent: l,
                        consequent: r,
                    },
                    span,
                ))
            }
            BinOp::Iff => {
                let l = self.lower_formula(ctx, lhs)?;
                let r = self.lower_formula(ctx, rhs)?;
                Ok(self.mk_formula(FormulaKind::Iff(l, r), span))
            }
            BinOp::Until | BinOp::Releases | BinOp::Since | BinOp::Triggered => {
                let l = self.lower_formula(ctx, lhs)?;
                let r = self.lower_formula(ctx, rhs)?;
                let (kind, name) = temporal_bin(op);
                self.mark_temporal(name, span);
                Ok(self.mk_formula(
                    FormulaKind::TemporalBinary {
                        op: kind,
                        lhs: l,
                        rhs: r,
                    },
                    span,
                ))
            }
            BinOp::Seq => {
                // `a ; b` ≡ `a && after b` (grammar-ref §precedence level 1) —
                // not a primitive temporal connective. Still temporal (Rung 6).
                let l = self.lower_formula(ctx, lhs)?;
                let r = self.lower_formula(ctx, rhs)?;
                self.mark_temporal(";", span);
                let after = self.mk_formula(
                    FormulaKind::TemporalUnary {
                        op: TemporalUnOp::After,
                        body: r,
                    },
                    span,
                );
                Ok(self.mk_formula(FormulaKind::And(vec![l, after]), span))
            }
            _ => Err(TranslateError::LoweringUnsupported {
                what: "binary operator in a formula position".to_owned(),
                span,
            }),
        }
    }

    fn lower_compare(
        &mut self,
        ctx: Ctx,
        op: CmpOp,
        lhs: ExprId,
        rhs: ExprId,
        span: Span,
    ) -> Result<FormulaId, TranslateError> {
        match op {
            CmpOp::Lt | CmpOp::Gt | CmpOp::Le | CmpOp::Ge => {
                let l = self.lower_int(ctx, lhs)?;
                let r = self.lower_int(ctx, rhs)?;
                let iop = match op {
                    CmpOp::Lt => IntCmpOp::Lt,
                    CmpOp::Gt => IntCmpOp::Gt,
                    CmpOp::Le => IntCmpOp::Le,
                    CmpOp::Ge => IntCmpOp::Ge,
                    _ => unreachable!(),
                };
                Ok(self.mk_formula(
                    FormulaKind::IntCompare {
                        op: iop,
                        lhs: l,
                        rhs: r,
                    },
                    span,
                ))
            }
            CmpOp::Eq | CmpOp::In => {
                // Integer special case (translation-ref §2.2): `=`/`in` compare as
                // integers iff BOTH sides are small-int casts; otherwise a
                // relational compare, promoting a lone small-int side via `Int[·]`.
                let l_int = self.sort_of(ctx, lhs) == Sort::Int;
                let r_int = self.sort_of(ctx, rhs) == Sort::Int;
                if matches!(op, CmpOp::Eq) && l_int && r_int {
                    let l = self.lower_int(ctx, lhs)?;
                    let r = self.lower_int(ctx, rhs)?;
                    return Ok(self.mk_formula(
                        FormulaKind::IntCompare {
                            op: IntCmpOp::Eq,
                            lhs: l,
                            rhs: r,
                        },
                        span,
                    ));
                }
                let l = self.lower_rel_promote(ctx, lhs, l_int)?;
                let r = self.lower_rel_promote(ctx, rhs, r_int)?;
                let rop = if matches!(op, CmpOp::Eq) {
                    RelCmpOp::Equal
                } else {
                    RelCmpOp::Subset
                };
                Ok(self.mk_formula(
                    FormulaKind::RelCompare {
                        op: rop,
                        lhs: l,
                        rhs: r,
                    },
                    span,
                ))
            }
        }
    }

    /// Lowers `e` as a relation, promoting a small-int value to its `Int` atom
    /// (`Int[e]`, translation-ref §2.2) so it can be set-compared.
    fn lower_rel_promote(
        &mut self,
        ctx: Ctx,
        e: ExprId,
        is_int: bool,
    ) -> Result<RelExprId, TranslateError> {
        if is_int {
            let ie = self.lower_int(ctx, e)?;
            Ok(self.mk_rel(RelExprKind::IntToAtom(ie), self.span_of(ctx, e)))
        } else {
            self.lower_rel(ctx, e)
        }
    }

    // ============================ relations ============================

    #[allow(clippy::too_many_lines)]
    fn lower_rel(&mut self, ctx: Ctx, e: ExprId) -> Result<RelExprId, TranslateError> {
        let node = self.ast(ctx.module).exprs[e].clone();
        let span = node.span;
        match node.kind {
            ExprKind::Name(_) | ExprKind::AtName(_) => self.lower_name_rel(ctx, e, span),
            ExprKind::This => self.lower_this(span),
            ExprKind::Const(c) => Ok(self.mk_rel(
                RelExprKind::Const(match c {
                    Const::None => RelConst::None,
                    Const::Univ => RelConst::Univ,
                    Const::Iden => RelConst::Iden,
                }),
                span,
            )),
            ExprKind::Num(_) => {
                // A small-int in relation position → its `Int` atom.
                let ie = self.lower_int(ctx, e)?;
                Ok(self.mk_rel(RelExprKind::IntToAtom(ie), span))
            }
            ExprKind::Str(_) => Err(TranslateError::StringUnsupported { span }),
            ExprKind::Binary { op, lhs, rhs } => self.lower_binary_rel(ctx, e, op, lhs, rhs, span),
            ExprKind::BoxJoin { .. } => self.lower_spine_rel(ctx, e, span),
            ExprKind::Arrow { lhs, rhs, .. } => {
                let l = self.lower_rel(ctx, lhs)?;
                let r = self.lower_rel(ctx, rhs)?;
                Ok(self.mk_rel(
                    RelExprKind::Binary {
                        op: RelBinOp::Product,
                        lhs: l,
                        rhs: r,
                    },
                    span,
                ))
            }
            ExprKind::Unary { op, expr } => self.lower_unary_rel(ctx, op, expr, span),
            ExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => {
                let c = self.lower_formula(ctx, cond)?;
                let t = self.lower_rel(ctx, then_branch)?;
                let el = self.lower_rel(ctx, else_branch)?;
                Ok(self.mk_rel(
                    RelExprKind::IfThenElse {
                        cond: c,
                        then_branch: t,
                        else_branch: el,
                    },
                    span,
                ))
            }
            ExprKind::Comprehension { decls, body } => {
                self.lower_comprehension(ctx, &decls, body, span)
            }
            ExprKind::Let { bindings, body } => {
                let mut pushed = 0;
                for b in &bindings {
                    let v = self.lower_rel(ctx, b.value)?;
                    self.binders.push((b.name.text.clone(), Binding::Expr(v)));
                    pushed += 1;
                }
                let r = self.lower_rel(ctx, body);
                for _ in 0..pushed {
                    self.binders.pop();
                }
                r
            }
            // A single-element block `{ e }` (e.g. a fun body) is just `e`.
            ExprKind::Block(exprs) if exprs.len() == 1 => self.lower_rel(ctx, exprs[0]),
            ExprKind::Block(_) | ExprKind::Quant { .. } | ExprKind::Compare { .. } => {
                Err(TranslateError::LoweringUnsupported {
                    what: "formula in a relation position".to_owned(),
                    span,
                })
            }
        }
    }

    fn lower_name_rel(
        &mut self,
        ctx: Ctx,
        e: ExprId,
        span: Span,
    ) -> Result<RelExprId, TranslateError> {
        let choice = self.choice(ctx, e).cloned();
        match choice {
            Some(ExprChoice::Name(nc)) => self.lower_name_choice(ctx, &nc, span),
            _ => Err(TranslateError::LoweringUnsupported {
                what: "name without a recorded resolution".to_owned(),
                span,
            }),
        }
    }

    fn lower_name_choice(
        &mut self,
        ctx: Ctx,
        nc: &NameChoice,
        span: Span,
    ) -> Result<RelExprId, TranslateError> {
        match nc {
            NameChoice::Var(name) => self.lookup_binder(name, span),
            NameChoice::Sig(sig) => self.sig_denote(*sig, span),
            NameChoice::Field {
                field,
                implicit_this,
            } => {
                let fd = *self.bounds.field_denote.get(field).ok_or_else(|| {
                    TranslateError::LoweringUnsupported {
                        what: "field without a denotation".to_owned(),
                        span,
                    }
                })?;
                if *implicit_this {
                    let this = self.lookup_binder("this", span)?;
                    Ok(self.mk_rel(
                        RelExprKind::Binary {
                            op: RelBinOp::Join,
                            lhs: this,
                            rhs: fd,
                        },
                        span,
                    ))
                } else {
                    Ok(fd)
                }
            }
            NameChoice::Call0(func) => self.inline_fun(ctx, *func, &[], span),
            NameChoice::Builtin(_) => Err(TranslateError::LoweringUnsupported {
                what: "integer-ordering builtin (fun/min|max|next|prev) is Rung 4".to_owned(),
                span,
            }),
            NameChoice::Macro(mc) => self.replay_macro_rel(mc, span),
            NameChoice::EmptyArity(k) => Ok(self.none_of_arity(*k, span)),
        }
    }

    fn lower_binary_rel(
        &mut self,
        ctx: Ctx,
        e: ExprId,
        op: BinOp,
        lhs: ExprId,
        rhs: ExprId,
        span: Span,
    ) -> Result<RelExprId, TranslateError> {
        let rel_op = match op {
            BinOp::Union => Some(RelBinOp::Union),
            BinOp::Diff => Some(RelBinOp::Diff),
            BinOp::Intersect => Some(RelBinOp::Intersect),
            BinOp::Override => Some(RelBinOp::Override),
            _ => None,
        };
        if let Some(rb) = rel_op {
            let l = self.lower_rel(ctx, lhs)?;
            let r = self.lower_rel(ctx, rhs)?;
            return Ok(self.mk_rel(
                RelExprKind::Binary {
                    op: rb,
                    lhs: l,
                    rhs: r,
                },
                span,
            ));
        }
        match op {
            BinOp::Join => self.lower_spine_rel(ctx, e, span),
            BinOp::DomRestrict => self.lower_restrict(ctx, lhs, rhs, true, span),
            BinOp::RanRestrict => self.lower_restrict(ctx, lhs, rhs, false, span),
            _ => Err(TranslateError::LoweringUnsupported {
                what: "binary operator in a relation position".to_owned(),
                span,
            }),
        }
    }

    /// A `.`-join or box-join spine in relation position — dispatch on the
    /// recorded [`SpineChoice`] (join / fun call / `Int[·]` / macro).
    fn lower_spine_rel(
        &mut self,
        ctx: Ctx,
        e: ExprId,
        span: Span,
    ) -> Result<RelExprId, TranslateError> {
        let choice = self.choice(ctx, e).cloned();
        match choice {
            Some(ExprChoice::Spine(SpineChoice::Join)) => self.lower_join_structural(ctx, e, span),
            Some(ExprChoice::Spine(SpineChoice::Call(cc))) => {
                self.inline_fun(ctx, cc.func, &cc.args, span)
            }
            Some(ExprChoice::Spine(SpineChoice::Builtin {
                op: BuiltinCall::IntAtom,
            })) => {
                let arg = self.first_box_arg(ctx, e, span)?;
                let ie = self.lower_int(ctx, arg)?;
                Ok(self.mk_rel(RelExprKind::IntToAtom(ie), span))
            }
            Some(ExprChoice::Spine(SpineChoice::Macro(mc))) => self.replay_macro_rel(&mc, span),
            Some(ExprChoice::Spine(SpineChoice::Empty(k))) => Ok(self.none_of_arity(k, span)),
            _ => Err(TranslateError::LoweringUnsupported {
                what: "relation-position spine without a recorded resolution".to_owned(),
                span,
            }),
        }
    }

    /// Lowers a relational join spine structurally (translation-ref §2.1): a
    /// `Binary{Join}` is `lower(lhs) . lower(rhs)`; a `BoxJoin` `t[a,b]` folds to
    /// `b . (a . t)`.
    fn lower_join_structural(
        &mut self,
        ctx: Ctx,
        e: ExprId,
        span: Span,
    ) -> Result<RelExprId, TranslateError> {
        match self.ast(ctx.module).exprs[e].kind.clone() {
            ExprKind::Binary {
                op: BinOp::Join,
                lhs,
                rhs,
            } => {
                let l = self.lower_rel(ctx, lhs)?;
                let r = self.lower_rel(ctx, rhs)?;
                Ok(self.mk_rel(
                    RelExprKind::Binary {
                        op: RelBinOp::Join,
                        lhs: l,
                        rhs: r,
                    },
                    span,
                ))
            }
            ExprKind::BoxJoin { target, args } => {
                let mut acc = self.lower_rel(ctx, target)?;
                for a in args {
                    let av = self.lower_rel(ctx, a)?;
                    acc = self.mk_rel(
                        RelExprKind::Binary {
                            op: RelBinOp::Join,
                            lhs: av,
                            rhs: acc,
                        },
                        span,
                    );
                }
                Ok(acc)
            }
            _ => Err(TranslateError::LoweringUnsupported {
                what: "join spine of unexpected shape".to_owned(),
                span,
            }),
        }
    }

    /// `A <: r` / `r :> A` via product-pad-and-intersect (translation-ref §2.1):
    /// `A <: r` = `(A -> univ^{n-1}) & r`; `r :> A` = `r & (univ^{n-1} -> A)`.
    fn lower_restrict(
        &mut self,
        ctx: Ctx,
        lhs: ExprId,
        rhs: ExprId,
        domain: bool,
        span: Span,
    ) -> Result<RelExprId, TranslateError> {
        // `A <: r`: set = A (lhs), rel = r (rhs). `r :> A`: rel = r (lhs), set = A (rhs).
        let (set_e, rel_e) = if domain { (lhs, rhs) } else { (rhs, lhs) };
        let rel = self.lower_rel(ctx, rel_e)?;
        let set = self.lower_rel(ctx, set_e)?;
        // The restricted relation's arity, read off the lowered IR (works for any
        // compound, unlike a name-only lookup).
        let arity = self
            .ir_arity(rel)
            .ok_or_else(|| TranslateError::LoweringUnsupported {
                what: "restriction over a relation of unknown arity".to_owned(),
                span,
            })?;
        if arity < 2 {
            // A unary relation's only column *is* its domain/range, so `A <: r`
            // and `r :> A` both reduce to `r & A`.
            return Ok(self.mk_rel(
                RelExprKind::Binary {
                    op: RelBinOp::Intersect,
                    lhs: rel,
                    rhs: set,
                },
                span,
            ));
        }
        let univ = self.mk_rel(RelExprKind::Const(RelConst::Univ), span);
        let pad = {
            // univ^{arity-1}
            let mut acc: Option<RelExprId> = None;
            for _ in 0..(arity - 1) {
                acc = Some(match acc {
                    None => univ,
                    Some(a) => self.mk_rel(
                        RelExprKind::Binary {
                            op: RelBinOp::Product,
                            lhs: a,
                            rhs: univ,
                        },
                        span,
                    ),
                });
            }
            acc
        };
        let Some(pad) = pad else {
            return Err(TranslateError::LoweringUnsupported {
                what: "restriction padding".to_owned(),
                span,
            });
        };
        let padded = if domain {
            // set -> univ^{n-1}
            self.mk_rel(
                RelExprKind::Binary {
                    op: RelBinOp::Product,
                    lhs: set,
                    rhs: pad,
                },
                span,
            )
        } else {
            // univ^{n-1} -> set
            self.mk_rel(
                RelExprKind::Binary {
                    op: RelBinOp::Product,
                    lhs: pad,
                    rhs: set,
                },
                span,
            )
        };
        Ok(self.mk_rel(
            RelExprKind::Binary {
                op: RelBinOp::Intersect,
                lhs: rel,
                rhs: padded,
            },
            span,
        ))
    }

    fn lower_unary_rel(
        &mut self,
        ctx: Ctx,
        op: UnOp,
        expr: ExprId,
        span: Span,
    ) -> Result<RelExprId, TranslateError> {
        match op {
            UnOp::Transpose => {
                let r = self.lower_rel(ctx, expr)?;
                Ok(self.mk_rel(
                    RelExprKind::Unary {
                        op: RelUnOp::Transpose,
                        expr: r,
                    },
                    span,
                ))
            }
            UnOp::Closure => {
                let r = self.lower_rel(ctx, expr)?;
                Ok(self.mk_rel(
                    RelExprKind::Unary {
                        op: RelUnOp::Closure,
                        expr: r,
                    },
                    span,
                ))
            }
            UnOp::ReflexiveClosure => {
                let r = self.lower_rel(ctx, expr)?;
                Ok(self.mk_rel(
                    RelExprKind::Unary {
                        op: RelUnOp::ReflexiveClosure,
                        expr: r,
                    },
                    span,
                ))
            }
            // Multiplicity/`seq` decl markers in an expression position: strip.
            UnOp::SetOf | UnOp::ExactlyOf | UnOp::SomeOf | UnOp::LoneOf | UnOp::OneOf => {
                self.lower_rel(ctx, expr)
            }
            UnOp::SeqOf => Err(TranslateError::LoweringUnsupported {
                what: "`seq` bound (Rung 4)".to_owned(),
                span,
            }),
            UnOp::Prime => {
                let r = self.lower_rel(ctx, expr)?;
                self.mark_temporal("'", span);
                Ok(self.mk_rel(RelExprKind::Prime(r), span))
            }
            _ => Err(TranslateError::LoweringUnsupported {
                what: "unary operator in a relation position".to_owned(),
                span,
            }),
        }
    }

    fn lower_comprehension(
        &mut self,
        ctx: Ctx,
        decls: &[als_syntax::ast::DeclId],
        body: ExprId,
        span: Span,
    ) -> Result<RelExprId, TranslateError> {
        let (comp_decls, disj, pushed) = self.bind_decls(ctx, decls, span)?;
        let body_f = self.lower_formula(ctx, body);
        for _ in 0..pushed {
            self.binders.pop();
        }
        let mut body_f = body_f?;
        // A `disj` comprehension conjoins pairwise disjointness into the body.
        if let Some(d) = disj {
            body_f = self.mk_formula(FormulaKind::And(vec![d, body_f]), span);
        }
        Ok(self.mk_rel(
            RelExprKind::Comprehension {
                decls: comp_decls,
                body: body_f,
            },
            span,
        ))
    }

    // ============================ integers ============================

    #[allow(clippy::too_many_lines)] // one arm per integer-position `ExprKind`
    fn lower_int(&mut self, ctx: Ctx, e: ExprId) -> Result<IntExprId, TranslateError> {
        let node = self.ast(ctx.module).exprs[e].clone();
        let span = node.span;
        // An expression that resolves to a *relation* of `Int` atoms in an
        // integer position is implicitly cast (`int[·]`, the reference's
        // CAST2INT) — e.g. `sum a: A | a.n` or `plus[x, a.n]`.
        if self.sort_of(ctx, e) == Sort::Rel {
            let r = self.lower_rel(ctx, e)?;
            return Ok(self.mk_int(IntExprKind::AtomToInt(r), span));
        }
        match node.kind {
            ExprKind::Num(n) => Ok(self.mk_int(IntExprKind::Const(n), span)),
            ExprKind::Unary { op, expr } => match op {
                UnOp::Card => {
                    let r = self.lower_rel(ctx, expr)?;
                    Ok(self.mk_int(IntExprKind::Card(r), span))
                }
                UnOp::IntOf | UnOp::SumOf => {
                    let r = self.lower_rel(ctx, expr)?;
                    Ok(self.mk_int(IntExprKind::AtomToInt(r), span))
                }
                _ => Err(TranslateError::LoweringUnsupported {
                    what: "unary operator in an integer position".to_owned(),
                    span,
                }),
            },
            ExprKind::Binary { op, lhs, rhs } => {
                if let Some(iop) = int_binop(op) {
                    let l = self.lower_int(ctx, lhs)?;
                    let r = self.lower_int(ctx, rhs)?;
                    Ok(self.mk_int(
                        IntExprKind::Binary {
                            op: iop,
                            lhs: l,
                            rhs: r,
                        },
                        span,
                    ))
                } else {
                    Err(TranslateError::LoweringUnsupported {
                        what: "binary operator in an integer position".to_owned(),
                        span,
                    })
                }
            }
            ExprKind::BoxJoin { .. } => {
                // `int[e]`/`sum[e]` → AtomToInt of the operand.
                match self.choice(ctx, e).cloned() {
                    Some(ExprChoice::Spine(SpineChoice::Builtin {
                        op: BuiltinCall::IntCast,
                    })) => {
                        let arg = self.first_box_arg(ctx, e, span)?;
                        let r = self.lower_rel(ctx, arg)?;
                        Ok(self.mk_int(IntExprKind::AtomToInt(r), span))
                    }
                    Some(ExprChoice::Spine(SpineChoice::Call(cc))) => {
                        self.inline_fun_int(ctx, cc.func, &cc.args, span)
                    }
                    _ => Err(TranslateError::LoweringUnsupported {
                        what: "integer-position spine".to_owned(),
                        span,
                    }),
                }
            }
            ExprKind::Quant {
                quant: Quant::Sum,
                decls,
                body,
            } => self.lower_sum(ctx, &decls, body, span),
            ExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => {
                let c = self.lower_formula(ctx, cond)?;
                let t = self.lower_int(ctx, then_branch)?;
                let el = self.lower_int(ctx, else_branch)?;
                Ok(self.mk_int(
                    IntExprKind::IfThenElse {
                        cond: c,
                        then_branch: t,
                        else_branch: el,
                    },
                    span,
                ))
            }
            ExprKind::Name(_) | ExprKind::AtName(_) => {
                // A 0-ary fun returning an int, inlined.
                match self.choice(ctx, e).cloned() {
                    Some(ExprChoice::Name(NameChoice::Call0(func))) => {
                        self.inline_fun_int(ctx, func, &[], span)
                    }
                    _ => Err(TranslateError::LoweringUnsupported {
                        what: "integer-position name".to_owned(),
                        span,
                    }),
                }
            }
            ExprKind::Let { bindings, body } => {
                let mut pushed = 0;
                for b in &bindings {
                    let v = self.lower_rel(ctx, b.value)?;
                    self.binders.push((b.name.text.clone(), Binding::Expr(v)));
                    pushed += 1;
                }
                let r = self.lower_int(ctx, body);
                for _ in 0..pushed {
                    self.binders.pop();
                }
                r
            }
            // A single-element block `{ e }` (a fun body) is just `e`.
            ExprKind::Block(exprs) if exprs.len() == 1 => self.lower_int(ctx, exprs[0]),
            _ => Err(TranslateError::LoweringUnsupported {
                what: "unexpected integer-position expression".to_owned(),
                span,
            }),
        }
    }

    fn lower_sum(
        &mut self,
        ctx: Ctx,
        decls: &[als_syntax::ast::DeclId],
        body: ExprId,
        span: Span,
    ) -> Result<IntExprId, TranslateError> {
        // `sum` desugars to nested single-var `Sum` (IR shape).
        let mut var_bounds: Vec<(crate::ir::VarId, RelExprId)> = Vec::new();
        let mut pushed = 0;
        for &d in decls {
            let decl = self.ast(ctx.module).decls[d].clone();
            let bound = self.lower_decl_bound_set(ctx, &decl)?;
            for name in &decl.names {
                let vid = self.ir.vars.alloc(Var {
                    name: name.text.clone(),
                    arity: 1,
                    span: name.span,
                });
                var_bounds.push((vid, bound));
                self.binders.push((name.text.clone(), Binding::Var(vid)));
                pushed += 1;
            }
        }
        let body_i = self.lower_int(ctx, body);
        for _ in 0..pushed {
            self.binders.pop();
        }
        let mut acc = body_i?;
        for (vid, bound) in var_bounds.into_iter().rev() {
            acc = self.mk_int(
                IntExprKind::Sum {
                    var: vid,
                    bound,
                    body: acc,
                },
                span,
            );
        }
        Ok(acc)
    }

    // ============================ quantifiers ============================

    /// Lowers a quantifier (translation-ref §2.3): `all`/`some` desugar to nested
    /// single-var `Quant`; `no x | φ` ⇒ `all x | ¬φ`; `one`/`lone x | φ` via the
    /// comprehension-cardinality route (`one {x | φ}` / `lone {x | φ}`).
    fn lower_quant(
        &mut self,
        ctx: Ctx,
        quant: Quant,
        decls: &[als_syntax::ast::DeclId],
        body: ExprId,
        span: Span,
    ) -> Result<FormulaId, TranslateError> {
        match quant {
            Quant::Sum => Err(TranslateError::LoweringUnsupported {
                what: "`sum` in a formula position".to_owned(),
                span,
            }),
            Quant::All | Quant::Some | Quant::No => {
                let (var_bounds, disj, pushed) = self.bind_decls_vars(ctx, decls, span)?;
                let body_f = self.lower_formula(ctx, body);
                for _ in 0..pushed {
                    self.binders.pop();
                }
                let mut inner = body_f?;
                // `no` = `all ¬`.
                let kind = if matches!(quant, Quant::Some) {
                    QuantKind::Some
                } else {
                    QuantKind::All
                };
                if matches!(quant, Quant::No) {
                    inner = self.not(inner, span);
                }
                // disj guard: All/No use implication; Some uses conjunction.
                if let Some(d) = disj {
                    inner = if matches!(quant, Quant::Some) {
                        self.mk_formula(FormulaKind::And(vec![d, inner]), span)
                    } else {
                        self.mk_formula(
                            FormulaKind::Implies {
                                antecedent: d,
                                consequent: inner,
                            },
                            span,
                        )
                    };
                }
                let mut acc = inner;
                for (vid, bound) in var_bounds.into_iter().rev() {
                    acc = self.mk_formula(
                        FormulaKind::Quant {
                            kind,
                            var: vid,
                            bound,
                            body: acc,
                        },
                        span,
                    );
                }
                Ok(acc)
            }
            Quant::One | Quant::Lone => {
                // `one/lone x: B | φ` ⇒ `one/lone {x: B | φ}`.
                let comp = self.lower_comprehension(ctx, decls, body, span)?;
                let test = if matches!(quant, Quant::One) {
                    MultTest::One
                } else {
                    MultTest::Lone
                };
                Ok(self.mk_formula(FormulaKind::MultTest { test, expr: comp }, span))
            }
        }
    }

    /// Binds a decl list into fresh IR quantifier vars, returning `(var, bound)`
    /// pairs (in order), the optional pairwise-disjointness formula from `disj`
    /// markers, and the count of pushed binders.
    fn bind_decls_vars(
        &mut self,
        ctx: Ctx,
        decls: &[als_syntax::ast::DeclId],
        span: Span,
    ) -> Result<(VarBounds, Option<FormulaId>, usize), TranslateError> {
        let mut var_bounds = Vec::new();
        let mut disj_parts: Vec<FormulaId> = Vec::new();
        let mut pushed = 0;
        for &d in decls {
            let decl = self.ast(ctx.module).decls[d].clone();
            let bound = self.lower_decl_bound_set(ctx, &decl)?;
            let mut group: Vec<RelExprId> = Vec::new();
            for name in &decl.names {
                let vid = self.ir.vars.alloc(Var {
                    name: name.text.clone(),
                    arity: 1,
                    span: name.span,
                });
                var_bounds.push((vid, bound));
                self.binders.push((name.text.clone(), Binding::Var(vid)));
                pushed += 1;
                group.push(self.mk_rel(RelExprKind::Var(vid), name.span));
            }
            if decl.is_disj && group.len() >= 2 {
                self.push_pairwise_disjoint(&group, span, &mut disj_parts);
            }
        }
        let disj = if disj_parts.is_empty() {
            None
        } else {
            Some(self.conjoin(disj_parts, span))
        };
        Ok((var_bounds, disj, pushed))
    }

    /// Like [`Self::bind_decls_vars`] but returns [`CompDecl`]s for a
    /// comprehension (each var + its unary bound).
    fn bind_decls(
        &mut self,
        ctx: Ctx,
        decls: &[als_syntax::ast::DeclId],
        span: Span,
    ) -> Result<(Vec<CompDecl>, Option<FormulaId>, usize), TranslateError> {
        let (var_bounds, disj, pushed) = self.bind_decls_vars(ctx, decls, span)?;
        let comp = var_bounds
            .into_iter()
            .map(|(var, bound)| CompDecl { var, bound })
            .collect();
        Ok((comp, disj, pushed))
    }

    fn push_pairwise_disjoint(
        &mut self,
        group: &[RelExprId],
        span: Span,
        out: &mut Vec<FormulaId>,
    ) {
        for i in 0..group.len() {
            for j in (i + 1)..group.len() {
                let inter = self.mk_rel(
                    RelExprKind::Binary {
                        op: RelBinOp::Intersect,
                        lhs: group[i],
                        rhs: group[j],
                    },
                    span,
                );
                out.push(self.mk_formula(
                    FormulaKind::MultTest {
                        test: MultTest::No,
                        expr: inter,
                    },
                    span,
                ));
            }
        }
    }

    /// Lowers a declaration bound to its **set** relation, stripping any
    /// multiplicity/`seq` marker (the marker constrains the bound, handled at the
    /// quantifier/field level, not the bound value).
    fn lower_decl_bound_set(&mut self, ctx: Ctx, decl: &Decl) -> Result<RelExprId, TranslateError> {
        let ast = self.ast(ctx.module);
        let bound = match &ast.exprs[decl.bound].kind {
            ExprKind::Unary { op, expr } if is_mult_marker(*op) => *expr,
            _ => decl.bound,
        };
        self.lower_rel(ctx, bound)
    }

    // ============================ calls / macros ============================

    /// Inlines a pred body as a formula, binding each parameter to the
    /// (lowered) argument (translation-ref §3.5). The receiver (`implicit_this`
    /// on the call) is the caller's current `this`.
    fn inline_pred(
        &mut self,
        ctx: Ctx,
        func: FuncIdx,
        args: &[ExprId],
        span: Span,
    ) -> Result<FormulaId, TranslateError> {
        let (fmod, body, pushed) = self.bind_call_params(ctx, func, args, span)?;
        let fctx = self.ctx(fmod);
        let r = self.lower_formula(fctx, body);
        for _ in 0..pushed {
            self.binders.pop();
        }
        self.inline_stack.pop();
        r
    }

    /// Inlines a fun body as a relation.
    fn inline_fun(
        &mut self,
        ctx: Ctx,
        func: FuncIdx,
        args: &[ExprId],
        span: Span,
    ) -> Result<RelExprId, TranslateError> {
        let (fmod, body, pushed) = self.bind_call_params(ctx, func, args, span)?;
        let fctx = self.ctx(fmod);
        let r = self.lower_rel(fctx, body);
        for _ in 0..pushed {
            self.binders.pop();
        }
        self.inline_stack.pop();
        r
    }

    /// Inlines a fun body as an integer.
    fn inline_fun_int(
        &mut self,
        ctx: Ctx,
        func: FuncIdx,
        args: &[ExprId],
        span: Span,
    ) -> Result<IntExprId, TranslateError> {
        let (fmod, body, pushed) = self.bind_call_params(ctx, func, args, span)?;
        let fctx = self.ctx(fmod);
        let r = self.lower_int(fctx, body);
        for _ in 0..pushed {
            self.binders.pop();
        }
        self.inline_stack.pop();
        r
    }

    /// Binds a call's parameters to its (lowered) argument expressions and
    /// returns the func's module, body, and how many binders were pushed. Guards
    /// self-recursion (the reference rejects recursive funcs/preds) with a bound.
    fn bind_call_params(
        &mut self,
        ctx: Ctx,
        func: FuncIdx,
        args: &[ExprId],
        span: Span,
    ) -> Result<(ModuleId, ExprId, usize), TranslateError> {
        // Recursion guard: refuse if this func is already being inlined.
        if self.inline_stack.contains(&func) {
            return Err(TranslateError::LoweringUnsupported {
                what: "recursive func/pred call".to_owned(),
                span,
            });
        }
        let f = self.world.funcs[func].clone();
        let params = f.params.clone();
        let has_recv = params.first().is_some_and(|p| p.name == "this");
        // Lower each explicit argument in the *caller's* context first.
        let mut arg_rels: Vec<RelExprId> = Vec::with_capacity(args.len());
        for &a in args {
            arg_rels.push(self.lower_rel(ctx, a)?);
        }
        let mut pushed = 0usize;
        let mut arg_iter = arg_rels.into_iter();
        for p in &params {
            // Bind the receiver `this` to the caller's current `this`.
            if p.name == "this" && has_recv {
                let this = self.lookup_binder("this", span)?;
                self.binders.push(("this".to_owned(), Binding::Expr(this)));
                pushed += 1;
                continue;
            }
            let Some(av) = arg_iter.next() else {
                return Err(TranslateError::LoweringUnsupported {
                    what: format!("call to `{}`: too few arguments", f.name),
                    span,
                });
            };
            self.binders.push((p.name.clone(), Binding::Expr(av)));
            pushed += 1;
        }
        self.inline_stack.push(func);
        Ok((f.module, f.body, pushed))
    }

    /// Replays a macro expansion as a formula (translation-ref §3.7): bind each
    /// parameter to its (lowered) argument, then lower the body in the macro's
    /// module + nested choice table.
    fn replay_macro_formula(
        &mut self,
        mc: &als_types::MacroChoice,
        span: Span,
    ) -> Result<FormulaId, TranslateError> {
        let pushed = self.bind_macro(mc, span)?;
        let ctx = Ctx {
            module: mc.body_module,
            choices: &mc.body_choices,
        };
        let body = self.world.macros[mc.macro_id].body;
        let r = self.lower_formula(ctx, body);
        for _ in 0..pushed {
            self.binders.pop();
        }
        r
    }

    fn replay_macro_rel(
        &mut self,
        mc: &als_types::MacroChoice,
        span: Span,
    ) -> Result<RelExprId, TranslateError> {
        let pushed = self.bind_macro(mc, span)?;
        let ctx = Ctx {
            module: mc.body_module,
            choices: &mc.body_choices,
        };
        let body = self.world.macros[mc.macro_id].body;
        let r = self.lower_rel(ctx, body);
        for _ in 0..pushed {
            self.binders.pop();
        }
        r
    }

    fn bind_macro(
        &mut self,
        mc: &als_types::MacroChoice,
        span: Span,
    ) -> Result<usize, TranslateError> {
        if mc.lean {
            return Err(TranslateError::LoweringUnsupported {
                what: "higher-order macro (callable-by-name argument)".to_owned(),
                span,
            });
        }
        let arg_ctx = self.ctx(mc.arg_module);
        let params = self.world.macros[mc.macro_id].params.clone();
        if params.len() != mc.args.len() {
            return Err(TranslateError::LoweringUnsupported {
                what: "macro arity mismatch".to_owned(),
                span,
            });
        }
        let mut arg_rels: Vec<RelExprId> = Vec::with_capacity(mc.args.len());
        for &a in &mc.args {
            arg_rels.push(self.lower_rel(arg_ctx, a)?);
        }
        let mut pushed = 0;
        for (name, av) in params.iter().zip(arg_rels) {
            self.binders.push((name.clone(), Binding::Expr(av)));
            pushed += 1;
        }
        Ok(pushed)
    }

    /// A builtin box-join in formula position: `disj[…]` / `pred/totalOrder[…]`.
    fn lower_builtin_formula(
        &mut self,
        ctx: Ctx,
        op: BuiltinCall,
        e: ExprId,
        span: Span,
    ) -> Result<FormulaId, TranslateError> {
        let args = self.box_args(ctx, e, span)?;
        match op {
            BuiltinCall::Disj => {
                // Staged pairwise disjointness (translation-ref §2.2):
                // `no(a&b) ∧ no((a+b)&c) ∧ …`.
                let mut rels = Vec::with_capacity(args.len());
                for &a in &args {
                    rels.push(self.lower_rel(ctx, a)?);
                }
                let mut parts: Vec<FormulaId> = Vec::new();
                let mut acc: Option<RelExprId> = None;
                for r in rels {
                    if let Some(prev) = acc {
                        let inter = self.mk_rel(
                            RelExprKind::Binary {
                                op: RelBinOp::Intersect,
                                lhs: prev,
                                rhs: r,
                            },
                            span,
                        );
                        parts.push(self.mk_formula(
                            FormulaKind::MultTest {
                                test: MultTest::No,
                                expr: inter,
                            },
                            span,
                        ));
                        acc = Some(self.mk_rel(
                            RelExprKind::Binary {
                                op: RelBinOp::Union,
                                lhs: prev,
                                rhs: r,
                            },
                            span,
                        ));
                    } else {
                        acc = Some(r);
                    }
                }
                if parts.is_empty() {
                    Ok(self.mk_formula(FormulaKind::Const(true), span))
                } else {
                    Ok(self.conjoin(parts, span))
                }
            }
            BuiltinCall::TotalOrder => {
                // `pred/totalOrder[elem, first, next]` (translation-ref §5/§2.2,
                // LEDGER-004): the hand-built total-order formula the reference's
                // non-native path uses, semantically equivalent to Kodkod's native
                // `ord[next, elem, first, last]`. `next` is the immediate-successor
                // relation of a single linear chain over `elem`, `first` its minimum.
                // Exactly the `n!` orderings over a fixed `elem` of size `n` satisfy
                // it, so the enumerated count matches the jar's sym0 column whenever
                // the ordered sig has a genuine partition choice (bounds pinning does
                // not engage — probes T14a-e). When pinning *does* engage
                // (bounds_builder), `first`/`next` are exact constants and this
                // formula is trivially satisfied.
                if args.len() != 3 {
                    return Err(TranslateError::LoweringUnsupported {
                        what: "`pred/totalOrder` with other than 3 arguments".to_owned(),
                        span,
                    });
                }
                let elem = self.lower_rel(ctx, args[0])?;
                let first = self.lower_rel(ctx, args[1])?;
                let next = self.lower_rel(ctx, args[2])?;
                Ok(self.total_order_formula(elem, first, next, span))
            }
            BuiltinCall::IntCast | BuiltinCall::IntAtom => {
                Err(TranslateError::LoweringUnsupported {
                    what: "int cast in a formula position".to_owned(),
                    span,
                })
            }
        }
    }

    // ============================ sort classification ============================

    /// The sort of expression `e` (translation-ref §2), from the recorded
    /// choices — used only to route `=`/`in` (int special case) and small-int
    /// promotion; never a re-derivation of the type checker.
    fn sort_of(&self, ctx: Ctx, e: ExprId) -> Sort {
        match &self.ast(ctx.module).exprs[e].kind {
            ExprKind::Num(_) => Sort::Int,
            ExprKind::Str(_) | ExprKind::Const(_) | ExprKind::This => Sort::Rel,
            ExprKind::Unary { op, expr } => match op {
                UnOp::Card | UnOp::IntOf | UnOp::SumOf => Sort::Int,
                UnOp::Not
                | UnOp::No
                | UnOp::Some
                | UnOp::Lone
                | UnOp::One
                | UnOp::Always
                | UnOp::Eventually
                | UnOp::After
                | UnOp::Before
                | UnOp::Historically
                | UnOp::Once => Sort::Formula,
                _ => self.sort_of(ctx, *expr),
            },
            ExprKind::Binary { op, lhs, .. } => match op {
                BinOp::Or
                | BinOp::And
                | BinOp::Iff
                | BinOp::Implies
                | BinOp::Until
                | BinOp::Releases
                | BinOp::Since
                | BinOp::Triggered
                | BinOp::Seq => Sort::Formula,
                BinOp::Shl
                | BinOp::Sha
                | BinOp::Shr
                | BinOp::IntAdd
                | BinOp::IntSub
                | BinOp::IntMul
                | BinOp::IntDiv
                | BinOp::IntRem => Sort::Int,
                BinOp::Join => self.spine_sort(ctx, e),
                _ => {
                    let _ = lhs;
                    Sort::Rel
                }
            },
            ExprKind::BoxJoin { .. } => self.spine_sort(ctx, e),
            ExprKind::Name(_) | ExprKind::AtName(_) => self.name_sort(ctx, e),
            ExprKind::Arrow { .. } | ExprKind::Comprehension { .. } => Sort::Rel,
            ExprKind::Compare { .. } => Sort::Formula,
            ExprKind::IfThenElse {
                then_branch,
                else_branch,
                ..
            } => {
                if self.sort_of(ctx, *then_branch) == Sort::Int
                    || self.sort_of(ctx, *else_branch) == Sort::Int
                {
                    Sort::Int
                } else {
                    Sort::Rel
                }
            }
            ExprKind::Quant { quant, .. } => {
                if matches!(quant, Quant::Sum) {
                    Sort::Int
                } else {
                    Sort::Formula
                }
            }
            ExprKind::Let { body, .. } => self.sort_of(ctx, *body),
            // A single-element block `{ e }` (a fun body) has `e`'s sort.
            ExprKind::Block(exprs) if exprs.len() == 1 => self.sort_of(ctx, exprs[0]),
            ExprKind::Block(_) => Sort::Formula,
        }
    }

    fn name_sort(&self, ctx: Ctx, e: ExprId) -> Sort {
        match self.choice(ctx, e) {
            Some(ExprChoice::Name(NameChoice::Call0(func))) => self.func_sort(*func),
            Some(ExprChoice::Name(NameChoice::Macro(mc))) => self.macro_sort(mc),
            _ => Sort::Rel,
        }
    }

    fn spine_sort(&self, ctx: Ctx, e: ExprId) -> Sort {
        match self.choice(ctx, e) {
            Some(ExprChoice::Spine(SpineChoice::Call(cc))) => self.func_sort(cc.func),
            Some(ExprChoice::Spine(SpineChoice::Builtin { op })) => match op {
                BuiltinCall::IntCast => Sort::Int,
                BuiltinCall::IntAtom => Sort::Rel,
                BuiltinCall::Disj | BuiltinCall::TotalOrder => Sort::Formula,
            },
            Some(ExprChoice::Spine(SpineChoice::Macro(mc))) => self.macro_sort(mc),
            _ => Sort::Rel,
        }
    }

    fn func_sort(&self, func: FuncIdx) -> Sort {
        let f = &self.world.funcs[func];
        if f.is_pred {
            Sort::Formula
        } else if f.return_ty.is_small_int {
            Sort::Int
        } else {
            Sort::Rel
        }
    }

    fn macro_sort(&self, mc: &als_types::MacroChoice) -> Sort {
        let ctx = Ctx {
            module: mc.body_module,
            choices: &mc.body_choices,
        };
        self.sort_of(ctx, self.world.macros[mc.macro_id].body)
    }

    // ============================ small helpers ============================

    fn ctx(&self, module: ModuleId) -> Ctx<'a> {
        Ctx {
            module,
            choices: &self.world.choices,
        }
    }

    fn ast(&self, module: ModuleId) -> &'a Ast {
        let file = self.graph.modules[module].file;
        self.graph.files.file(file).ast_ref()
    }

    fn choice<'c>(&self, ctx: Ctx<'c>, e: ExprId) -> Option<&'c ExprChoice> {
        ctx.choices.get(ctx.module, e)
    }

    fn span_of(&self, ctx: Ctx, e: ExprId) -> Span {
        self.ast(ctx.module).exprs[e].span
    }

    fn sig_denote(&mut self, sig: SigId, span: Span) -> Result<RelExprId, TranslateError> {
        self.bounds.sig_denote.get(&sig).copied().ok_or_else(|| {
            TranslateError::LoweringUnsupported {
                what: format!("sig `{}` has no denotation", self.world.sigs[sig].name),
                span,
            }
        })
    }

    fn lookup_binder(&mut self, name: &str, span: Span) -> Result<RelExprId, TranslateError> {
        for (n, b) in self.binders.iter().rev() {
            if n == name {
                return Ok(match b {
                    Binding::Var(vid) => {
                        let vid = *vid;
                        self.mk_rel(RelExprKind::Var(vid), span)
                    }
                    Binding::Expr(id) => *id,
                });
            }
        }
        Err(TranslateError::LoweringUnsupported {
            what: format!("unbound variable `{name}`"),
            span,
        })
    }

    fn lower_this(&mut self, span: Span) -> Result<RelExprId, TranslateError> {
        self.lookup_binder("this", span)
    }

    /// The arity of a lowered relation expression, read off the IR (used for
    /// `<:`/`:>` padding). Total by construction over the relational IR.
    fn ir_arity(&self, r: RelExprId) -> Option<usize> {
        match &self.ir.rel_exprs[r].kind {
            RelExprKind::Relation(rel) => Some(self.ir.relations[*rel].arity),
            RelExprKind::Var(v) => Some(self.ir.vars[*v].arity),
            RelExprKind::Const(RelConst::None | RelConst::Univ) => Some(1),
            RelExprKind::Const(RelConst::Iden) => Some(2),
            RelExprKind::Binary { op, lhs, rhs } => {
                let a = self.ir_arity(*lhs)?;
                let b = self.ir_arity(*rhs)?;
                Some(match op {
                    RelBinOp::Join => a + b - 2,
                    RelBinOp::Product => a + b,
                    RelBinOp::Union | RelBinOp::Diff | RelBinOp::Intersect | RelBinOp::Override => {
                        a
                    }
                })
            }
            RelExprKind::Unary { op, expr } => match op {
                RelUnOp::Transpose | RelUnOp::Closure | RelUnOp::ReflexiveClosure => {
                    let _ = expr;
                    Some(2)
                }
            },
            RelExprKind::Prime(e) => self.ir_arity(*e),
            RelExprKind::IfThenElse { then_branch, .. } => self.ir_arity(*then_branch),
            RelExprKind::Comprehension { decls, .. } => {
                let mut n = 0;
                for d in decls {
                    n += self.ir.vars[d.var].arity;
                }
                Some(n)
            }
            RelExprKind::IntToAtom(_) => Some(1),
        }
    }

    fn none_of_arity(&mut self, k: usize, span: Span) -> RelExprId {
        let none = self.mk_rel(RelExprKind::Const(RelConst::None), span);
        let mut acc = none;
        for _ in 1..k.max(1) {
            let n = self.mk_rel(RelExprKind::Const(RelConst::None), span);
            acc = self.mk_rel(
                RelExprKind::Binary {
                    op: RelBinOp::Product,
                    lhs: acc,
                    rhs: n,
                },
                span,
            );
        }
        acc
    }

    fn conjoin(&mut self, parts: Vec<FormulaId>, span: Span) -> FormulaId {
        match parts.len() {
            0 => self.mk_formula(FormulaKind::Const(true), span),
            1 => parts[0],
            _ => self.mk_formula(FormulaKind::And(parts), span),
        }
    }

    fn not(&mut self, f: FormulaId, span: Span) -> FormulaId {
        self.mk_formula(FormulaKind::Not(f), span)
    }

    /// The hand-built `pred/totalOrder[elem, first, next]` formula (LEDGER-004,
    /// translation-ref §5/§2.2): `first` is the unique minimum, `next` is the
    /// functional/injective immediate-successor relation of a single acyclic
    /// chain that reaches all of `elem`. Its models are exactly the `n!`
    /// linear orders over a fixed `elem`, so it pins the enumerated count in the
    /// subsig partition-choice case where the bounds pinning does not engage.
    fn total_order_formula(
        &mut self,
        elem: RelExprId,
        first: RelExprId,
        next: RelExprId,
        span: Span,
    ) -> FormulaId {
        let mut parts: Vec<FormulaId> = Vec::with_capacity(5);
        // `one first`.
        parts.push(self.mk_formula(
            FormulaKind::MultTest {
                test: MultTest::One,
                expr: first,
            },
            span,
        ));
        // `no next.first` — `first` has no predecessor (rules out cycles).
        let pred_of_first = self.mk_rel(
            RelExprKind::Binary {
                op: RelBinOp::Join,
                lhs: next,
                rhs: first,
            },
            span,
        );
        parts.push(self.mk_formula(
            FormulaKind::MultTest {
                test: MultTest::No,
                expr: pred_of_first,
            },
            span,
        ));
        // `all e: elem | lone e.next` — each element has ≤ 1 successor.
        let ev = self.ir.vars.alloc(Var {
            name: "totalOrder_e".to_owned(),
            arity: 1,
            span,
        });
        let ev_expr = self.mk_rel(RelExprKind::Var(ev), span);
        let e_next = self.mk_rel(
            RelExprKind::Binary {
                op: RelBinOp::Join,
                lhs: ev_expr,
                rhs: next,
            },
            span,
        );
        let lone_succ = self.mk_formula(
            FormulaKind::MultTest {
                test: MultTest::Lone,
                expr: e_next,
            },
            span,
        );
        parts.push(self.mk_formula(
            FormulaKind::Quant {
                kind: QuantKind::All,
                var: ev,
                bound: elem,
                body: lone_succ,
            },
            span,
        ));
        // `all e: elem | lone next.e` — each element has ≤ 1 predecessor.
        let pv = self.ir.vars.alloc(Var {
            name: "totalOrder_p".to_owned(),
            arity: 1,
            span,
        });
        let pv_expr = self.mk_rel(RelExprKind::Var(pv), span);
        let next_e = self.mk_rel(
            RelExprKind::Binary {
                op: RelBinOp::Join,
                lhs: next,
                rhs: pv_expr,
            },
            span,
        );
        let lone_pred = self.mk_formula(
            FormulaKind::MultTest {
                test: MultTest::Lone,
                expr: next_e,
            },
            span,
        );
        parts.push(self.mk_formula(
            FormulaKind::Quant {
                kind: QuantKind::All,
                var: pv,
                bound: elem,
                body: lone_pred,
            },
            span,
        ));
        // `elem in first.*next` — every element is reachable from `first`.
        let star_next = self.mk_rel(
            RelExprKind::Unary {
                op: RelUnOp::ReflexiveClosure,
                expr: next,
            },
            span,
        );
        let reach = self.mk_rel(
            RelExprKind::Binary {
                op: RelBinOp::Join,
                lhs: first,
                rhs: star_next,
            },
            span,
        );
        parts.push(self.mk_formula(
            FormulaKind::RelCompare {
                op: RelCmpOp::Subset,
                lhs: elem,
                rhs: reach,
            },
            span,
        ));
        self.conjoin(parts, span)
    }

    fn mark_temporal(&mut self, op: &'static str, span: Span) {
        if self.temporal.is_none() {
            self.temporal = Some((op, span));
        }
    }

    fn mk_formula(&mut self, kind: FormulaKind, span: Span) -> FormulaId {
        self.ir.formulas.alloc(Formula { kind, span })
    }

    fn mk_rel(&mut self, kind: RelExprKind, span: Span) -> RelExprId {
        self.ir.rel_exprs.alloc(RelExpr { kind, span })
    }

    fn mk_int(&mut self, kind: IntExprKind, span: Span) -> IntExprId {
        self.ir.int_exprs.alloc(IntExpr { kind, span })
    }

    /// The single argument of a one-arg builtin box join (`int[e]`/`Int[e]`).
    fn first_box_arg(&self, ctx: Ctx, e: ExprId, span: Span) -> Result<ExprId, TranslateError> {
        match &self.ast(ctx.module).exprs[e].kind {
            ExprKind::BoxJoin { args, .. } if !args.is_empty() => Ok(args[0]),
            _ => Err(TranslateError::LoweringUnsupported {
                what: "builtin cast with no argument".to_owned(),
                span,
            }),
        }
    }

    fn box_args(&self, ctx: Ctx, e: ExprId, span: Span) -> Result<Vec<ExprId>, TranslateError> {
        match &self.ast(ctx.module).exprs[e].kind {
            ExprKind::BoxJoin { args, .. } => Ok(args.clone()),
            _ => Err(TranslateError::LoweringUnsupported {
                what: "builtin form of unexpected shape".to_owned(),
                span,
            }),
        }
    }

    /// The value-arity of a decl bound (for the implicit-`one`): the arity of the
    /// bound expression's resolved type, from the sig/field it denotes. `1` for a
    /// unary sig/field-value; `None` if unknown (then no implicit `one`).
    fn rel_value_arity(&self, bound: ExprId, ctx: Ctx) -> Option<usize> {
        self.rel_arity(bound, ctx)
    }

    /// The arity of a relation expression, from the sig/field it denotes (for
    /// restriction padding and implicit `one`). Best-effort: known for a plain
    /// sig/field name; `None` for compounds (callers defer).
    fn rel_arity(&self, e: ExprId, ctx: Ctx) -> Option<usize> {
        match &self.ast(ctx.module).exprs[e].kind {
            ExprKind::Name(_) | ExprKind::AtName(_) => match self.choice(ctx, e)? {
                ExprChoice::Name(NameChoice::Sig(_)) => Some(1),
                ExprChoice::Name(NameChoice::Field {
                    field,
                    implicit_this,
                }) => {
                    let a = self.world.fields[*field].ty.arity()?;
                    Some(if *implicit_this { a - 1 } else { a })
                }
                _ => None,
            },
            ExprKind::Const(Const::Iden) => Some(2),
            ExprKind::Const(_) => Some(1),
            _ => None,
        }
    }

    fn find_func_para(&self, module: ModuleId, func: FuncIdx) -> Option<als_syntax::ast::ParaId> {
        let ast = self.ast(module);
        let name = &self.world.funcs[func].name;
        // Match the nth func/pred with this name to its FuncId is fragile; the
        // simplest correct link is the declaration order. Find by name + body.
        let body = self.world.funcs[func].body;
        for &p in &ast.paragraphs {
            match &ast.paras[p] {
                als_syntax::ast::Para::Pred(pr) if &pr.name.text == name && pr.body == body => {
                    return Some(p)
                }
                als_syntax::ast::Para::Fun(fu) if &fu.name.text == name && fu.body == body => {
                    return Some(p)
                }
                _ => {}
            }
        }
        None
    }
}

// A local alias so the many signatures read clearly.
type FuncIdx = als_types::FuncId;

/// A list of quantifier/`sum` variables with their (unary) bounds, in order.
type VarBounds = Vec<(crate::ir::VarId, RelExprId)>;

/// Whether `op` is a declaration-bound multiplicity marker.
fn is_mult_marker(op: UnOp) -> bool {
    matches!(
        op,
        UnOp::SetOf | UnOp::SomeOf | UnOp::LoneOf | UnOp::OneOf | UnOp::ExactlyOf
    )
}

/// The multiplicity test a decl-bound marker enforces on `this.f` (none for
/// `set`/`exactly`).
fn mult_of_marker(op: UnOp) -> Option<MultTest> {
    match op {
        UnOp::SomeOf => Some(MultTest::Some),
        UnOp::LoneOf => Some(MultTest::Lone),
        UnOp::OneOf => Some(MultTest::One),
        UnOp::SetOf | UnOp::ExactlyOf => None,
        _ => None,
    }
}

/// The multiplicity test an arrow-column marker enforces (none for `set`).
fn mult_test_of(m: Option<Mult>) -> Option<MultTest> {
    match m {
        Some(Mult::One) => Some(MultTest::One),
        Some(Mult::Lone) => Some(MultTest::Lone),
        Some(Mult::Some) => Some(MultTest::Some),
        Some(Mult::Set) | None => None,
    }
}

fn int_binop(op: BinOp) -> Option<IntBinOp> {
    Some(match op {
        BinOp::IntAdd => IntBinOp::Add,
        BinOp::IntSub => IntBinOp::Sub,
        BinOp::IntMul => IntBinOp::Mul,
        BinOp::IntDiv => IntBinOp::Div,
        BinOp::IntRem => IntBinOp::Rem,
        BinOp::Shl => IntBinOp::Shl,
        BinOp::Sha => IntBinOp::Sha,
        BinOp::Shr => IntBinOp::Shr,
        _ => return None,
    })
}

fn temporal_un(op: UnOp) -> (TemporalUnOp, &'static str) {
    match op {
        UnOp::Always => (TemporalUnOp::Always, "always"),
        UnOp::Eventually => (TemporalUnOp::Eventually, "eventually"),
        UnOp::After => (TemporalUnOp::After, "after"),
        UnOp::Before => (TemporalUnOp::Before, "before"),
        UnOp::Historically => (TemporalUnOp::Historically, "historically"),
        UnOp::Once => (TemporalUnOp::Once, "once"),
        _ => unreachable!("non-temporal unary op"),
    }
}

fn temporal_bin(op: BinOp) -> (TemporalBinOp, &'static str) {
    match op {
        BinOp::Until => (TemporalBinOp::Until, "until"),
        BinOp::Releases => (TemporalBinOp::Releases, "releases"),
        BinOp::Since => (TemporalBinOp::Since, "since"),
        BinOp::Triggered => (TemporalBinOp::Triggered, "triggered"),
        _ => unreachable!("non-temporal binary op"),
    }
}

/// Unwraps a defined-field bound `= e` (`ExactlyOf(e)`) to `e`.
fn unwrap_exactly(ast: &Ast, bound: ExprId) -> Option<ExprId> {
    match &ast.exprs[bound].kind {
        ExprKind::Unary {
            op: UnOp::ExactlyOf,
            expr,
        } => Some(*expr),
        _ => None,
    }
}

/// A synthetic span for internal errors that predate any source construct.
fn als_types_synthetic_span() -> Span {
    Span::new(als_syntax::FileId::from_index(0), 0, 0)
}
