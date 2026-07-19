//! The two SB-0 count-divergence classifiers and the mettle defer-reason
//! classifier for the solve gauge (mt-037).
//!
//! Both classifiers exist to keep the counting net **honest**: they carve out
//! exactly the goal families where mettle's raw SB-0 count legitimately differs
//! from the jar's (documented in LIMITATIONS, translation-ref §10.4/§10.6), so
//! the net never fabricates a `COUNT_MISMATCH`. Following the gauge's contract
//! (a wrong skip only loses coverage; a wrong inclusion fabricates a
//! disagreement) both are written to **over-skip** when in doubt.

use als_core::ir::{FormulaId, FormulaKind, Ir, QuantKind};
use als_core::{ScopedUniverse, TranslateError};
use als_types::{ResolvedWorld, SigId, SigKind};

/// Whether the goal contains a **first-order** quantifier the jar would
/// skolemize as a depth-0 skolem constant (translation-ref §2.3/§10.6): an
/// effective-existential quantifier reachable from the goal root through only
/// monotone Boolean context (∧/∨/parity-tracked ¬/⇒) and **not** in the scope
/// of an effective-universal quantifier or a non-monotone connective.
///
/// mettle does not skolemize first-order decls (ADR-0011), so such a quantifier
/// survives in the lowered IR as [`FormulaKind::Quant`]; the jar counts the
/// skolem relation's assignments too, so the SB-0 counts diverge while the
/// verdict is identical. Higher-order existentials are already gone from the
/// formula (minted into `skolem_bounds`), so every `Quant` seen here is
/// first-order.
///
/// The pinned example: `oracle/test1.als`'s `check NoEmpty` lowers to
/// `Not(all b: B | some b.r)` — the enclosing `Not` (a `check`'s negation) puts
/// the `all` at negative polarity, making it effective-existential, so this
/// returns `true` (the jar's 561 vs mettle's 464).
#[must_use]
pub fn has_skolemizable_fo_existential(ir: &Ir, goal: FormulaId) -> bool {
    walk_polarity(ir, goal, true, false)
}

/// Recursive polarity/blocked walk. `positive` is the node's parity below the
/// goal root (flipped by `not` and an `implies` antecedent); `blocked` is set
/// once the walk passes an effective-universal quantifier body or a
/// non-monotone connective (`iff`), where a nested existential is **not**
/// skolemized at depth 0.
fn walk_polarity(ir: &Ir, id: FormulaId, positive: bool, blocked: bool) -> bool {
    match &ir.formulas[id].kind {
        FormulaKind::Const(_)
        | FormulaKind::RelCompare { .. }
        | FormulaKind::IntCompare { .. }
        | FormulaKind::MultTest { .. } => false,
        FormulaKind::Not(f) => walk_polarity(ir, *f, !positive, blocked),
        FormulaKind::And(fs) | FormulaKind::Or(fs) => {
            fs.iter().any(|f| walk_polarity(ir, *f, positive, blocked))
        }
        FormulaKind::Implies {
            antecedent,
            consequent,
        } => {
            walk_polarity(ir, *antecedent, !positive, blocked)
                || walk_polarity(ir, *consequent, positive, blocked)
        }
        // Bi-implication is non-monotone: neither operand has a settled parity,
        // so any quantifier under it is treated as blocked (conservative).
        FormulaKind::Iff(a, b) => {
            walk_polarity(ir, *a, positive, true) || walk_polarity(ir, *b, positive, true)
        }
        FormulaKind::Quant { kind, body, .. } => {
            let existential = matches!(
                (kind, positive),
                (QuantKind::Some, true) | (QuantKind::All, false)
            );
            if existential && !blocked {
                return true;
            }
            // An effective-universal blocks nested existentials (depth-0 rule);
            // an effective-existential does not (a chain of top-level `some`s
            // all skolemize). The body keeps the ambient parity.
            let universal = !existential;
            walk_polarity(ir, *body, positive, blocked || universal)
        }
        // Temporal goals defer before solving (never reached here); a temporal
        // connective is a non-monotone context, so treat its bodies as blocked.
        FormulaKind::TemporalUnary { body, .. } => walk_polarity(ir, *body, positive, true),
        FormulaKind::TemporalBinary { lhs, rhs, .. } => {
            walk_polarity(ir, *lhs, positive, true) || walk_polarity(ir, *rhs, positive, true)
        }
    }
}

/// Whether this command opens `util/ordering` over a sig whose population is a
/// **free partition** — an ordered sig with at least one non-exact prim
/// (`extends`) child (the T14a / T14d family, translation-ref §10.1). At
/// symmetry 0 the jar mints atoms per child and counts each atom→child
/// labelling separately; mettle mints canonical parent atoms, so the counts
/// diverge by a permutation factor while the verdict agrees (LIMITATIONS).
///
/// Over-skips deliberately: any ordered sig with a non-exact prim descendant
/// disqualifies the command from the counting net, whether or not the parent is
/// `abstract` (T14a's non-abstract ordered sig diverges too). Determinate-
/// population cases — all children exact (T14b/c/e), or no children at all
/// (T10–T13, T15) — are **not** skipped and count exactly.
#[must_use]
pub fn ordered_abstract_partition(world: &ResolvedWorld, scoped: &ScopedUniverse) -> bool {
    world
        .ordering
        .iter()
        .any(|oi| has_nonexact_prim_child(world, scoped, oi.elem))
}

/// The single prim (`extends`) parent of `sig`, or `None` for a root prim sig
/// or a subset (`in`/`=`) sig (which never partitions an ordered pool).
fn prim_parent(world: &ResolvedWorld, sig: SigId) -> Option<SigId> {
    match &world.sigs[sig].kind {
        SigKind::Prim { parent } => *parent,
        SigKind::Subset { .. } => None,
    }
}

/// Whether any sig is a transitive prim descendant of `elem` and non-exact in
/// this command's scope. A sig with no scope entry is treated as non-exact
/// (free) — the conservative direction.
fn has_nonexact_prim_child(world: &ResolvedWorld, scoped: &ScopedUniverse, elem: SigId) -> bool {
    for (sig, _) in world.sigs.iter() {
        if sig == elem {
            continue;
        }
        if !is_prim_descendant(world, sig, elem) {
            continue;
        }
        let exact = scoped.scopes.get(sig).is_some_and(|sc| sc.is_exact);
        if !exact {
            return true;
        }
    }
    false
}

/// Whether `sig`'s prim-parent chain reaches `ancestor`. Bounded by the sig
/// count so a (resolve-rejected, but defensively guarded) inheritance cycle
/// cannot loop forever.
fn is_prim_descendant(world: &ResolvedWorld, sig: SigId, ancestor: SigId) -> bool {
    let mut current = prim_parent(world, sig);
    for _ in 0..world.sigs.len() {
        match current {
            Some(p) if p == ancestor => return true,
            Some(p) => current = prim_parent(world, p),
            None => return false,
        }
    }
    false
}

/// The stable class of a **lowering** defer (`lower_command`'s typed error), for
/// the gauge's `mettle_defer:lower:<class>` sub-bucket. Scope-phase and
/// encode-phase defers are bucketed by the caller from their own phase, so those
/// variants are not expected here — but the classifier stays total (`PORTING`
/// R1: no catch-all) so a new `TranslateError` variant is a compile error, not a
/// silently mis-bucketed defer.
#[must_use]
pub fn lower_defer_class(err: &TranslateError) -> &'static str {
    match err {
        TranslateError::TemporalUnsupported { .. } => "temporal",
        TranslateError::LoweringUnsupported { .. } => "lowering",
        TranslateError::HigherOrder { .. } => "higher_order",
        TranslateError::CapacityExceeded { .. } => "capacity",
        TranslateError::ScopeOnSubset { .. }
        | TranslateError::ScopeOnEnum { .. }
        | TranslateError::StringScopeNotExact { .. }
        | TranslateError::OneSigScope { .. }
        | TranslateError::LoneSigScope { .. }
        | TranslateError::SomeSigScope { .. }
        | TranslateError::MustSpecifyScope { .. }
        | TranslateError::BitwidthTooLarge { .. } => "scope",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use als_core::ir::{Formula, FormulaKind, QuantKind, RelConst, RelExpr, RelExprKind, Var};
    use als_core::{compute_universe, ScopedUniverse};
    use als_syntax::{ArenaId, FileId, Span};
    use als_types::{MapLoader, ModuleGraph, ResolvedWorld};

    fn dummy_span() -> Span {
        Span::new(FileId::from_index(0), 0, 1)
    }

    /// Builds `Quant{kind, x: univ | inner}` in `ir` and returns its id.
    fn quant(ir: &mut Ir, kind: QuantKind, inner: FormulaId) -> FormulaId {
        let var = ir.vars.alloc(Var {
            name: "x".to_owned(),
            arity: 1,
            span: dummy_span(),
        });
        let bound = ir.rel_exprs.alloc(RelExpr {
            kind: RelExprKind::Const(RelConst::Univ),
            span: dummy_span(),
        });
        ir.formulas.alloc(Formula {
            kind: FormulaKind::Quant {
                kind,
                var,
                bound,
                body: inner,
            },
            span: dummy_span(),
        })
    }

    fn constf(ir: &mut Ir, b: bool) -> FormulaId {
        ir.formulas.alloc(Formula {
            kind: FormulaKind::Const(b),
            span: dummy_span(),
        })
    }

    fn not(ir: &mut Ir, f: FormulaId) -> FormulaId {
        ir.formulas.alloc(Formula {
            kind: FormulaKind::Not(f),
            span: dummy_span(),
        })
    }

    #[test]
    fn fo_top_level_some_is_skolemizable() {
        let mut ir = Ir::default();
        let t = constf(&mut ir, true);
        let g = quant(&mut ir, QuantKind::Some, t);
        assert!(has_skolemizable_fo_existential(&ir, g));
    }

    #[test]
    fn fo_top_level_all_is_not() {
        let mut ir = Ir::default();
        let t = constf(&mut ir, true);
        let g = quant(&mut ir, QuantKind::All, t);
        assert!(!has_skolemizable_fo_existential(&ir, g));
    }

    #[test]
    fn fo_negated_all_is_effective_existential() {
        // `check`-style: Not(all x | φ) — the `all` is at negative polarity.
        let mut ir = Ir::default();
        let t = constf(&mut ir, true);
        let all = quant(&mut ir, QuantKind::All, t);
        let g = not(&mut ir, all);
        assert!(has_skolemizable_fo_existential(&ir, g));
    }

    #[test]
    fn fo_some_under_all_is_blocked() {
        // `all x | some y | φ` — the inner `some` is under a universal, not
        // skolemized at depth 0.
        let mut ir = Ir::default();
        let t = constf(&mut ir, true);
        let inner_some = quant(&mut ir, QuantKind::Some, t);
        let g = quant(&mut ir, QuantKind::All, inner_some);
        assert!(!has_skolemizable_fo_existential(&ir, g));
    }

    #[test]
    fn fo_double_negated_all_stays_universal() {
        // Not(Not(all x | φ)) — parity returns to positive, so the `all` is
        // effective-universal again: not skolemizable.
        let mut ir = Ir::default();
        let t = constf(&mut ir, true);
        let all = quant(&mut ir, QuantKind::All, t);
        let n1 = not(&mut ir, all);
        let g = not(&mut ir, n1);
        assert!(!has_skolemizable_fo_existential(&ir, g));
    }

    // --- ordered-abstract detector, via the real pipeline -----------------

    /// Resolves `source` (with the embedded stdlib as fallback) and computes the
    /// scoped universe of command 0.
    fn pipeline(source: &str) -> (ResolvedWorld, ScopedUniverse) {
        let loader = MapLoader::new();
        let graph = ModuleGraph::load_with_source("mem/model.als", source.to_owned(), &loader)
            .unwrap_or_else(|e| panic!("load failed: {e:?}"));
        let resolved =
            als_types::resolve(&graph).unwrap_or_else(|e| panic!("resolve failed: {e:?}"));
        let world = resolved.world;
        let scoped = compute_universe(&world, &graph, &world.commands[0])
            .unwrap_or_else(|e| panic!("compute_universe failed: {e:?}"));
        (world, scoped)
    }

    #[test]
    fn ordered_no_children_is_not_skipped() {
        let (world, scoped) = pipeline("open util/ordering[S]\nsig S {}\nrun {} for 3");
        assert!(!ordered_abstract_partition(&world, &scoped));
    }

    #[test]
    fn ordered_abstract_nonexact_children_is_skipped() {
        // The T14d shape: abstract A, two non-exact children.
        let (world, scoped) = pipeline(
            "open util/ordering[A]\nabstract sig A {}\nsig B extends A {}\nsig C extends A {}\nrun {} for 4 A",
        );
        assert!(ordered_abstract_partition(&world, &scoped));
    }

    #[test]
    fn ordered_all_children_exact_is_not_skipped() {
        // T14c-style: every child exactly scoped → determinate population.
        let (world, scoped) = pipeline(
            "open util/ordering[A]\nabstract sig A {}\nsig B extends A {}\nsig C extends A {}\nrun {} for 3 A, exactly 2 B, exactly 1 C",
        );
        assert!(!ordered_abstract_partition(&world, &scoped));
    }

    #[test]
    fn no_ordering_is_not_skipped() {
        let (world, scoped) = pipeline("sig A {}\nsig B extends A {}\nrun {} for 3");
        assert!(!ordered_abstract_partition(&world, &scoped));
    }
}
