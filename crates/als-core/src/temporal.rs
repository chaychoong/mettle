//! Temporal machinery: the k-state unroller and the lasso loop selector
//! (ADR-0015 decision 1, mt-065).
//!
//! Rung 6 solves a temporal command as **bounded lasso solving by k-fold
//! unrolling over the existing, unmodified engine**: for a trace length `k`,
//! every `var`-backed relation is instantiated `k` times — one copy per state —
//! while static relations bind once and are shared by every state (the
//! static/variable partition lives on the relation table as
//! [`crate::ir::Mutability`]). Atoms are **rigid**: the universe never changes
//! between states, only relation *values* do, which is exactly why every
//! per-state copy inherits its original's `[lower, upper]` bound verbatim
//! (alloy6-temporal.md §(d); probe T-13 live-reconfirmed that `univ`/`Int`/
//! `String`/`seq/Int` are byte-identical across the states of a real trace).
//!
//! [`unroll`] produces the bounds view; the **bridge map** it returns
//! (original var [`RelId`] → the `k` per-state copies) is what mt-066's
//! state-indexed lowering consumes to turn "relation `r` at state `s`" into a
//! concrete [`RelId`]. [`LassoSelector`] mints the back-loop index `l ∈ [0,k-1]`
//! as an exactly-one-encoded variable set; mt-067 places it into `translate()`.
//!
//! **Determinism (STYLE D1/D2).** [`RelId`] allocation order *is* downstream
//! variable numbering, so the unroller pins it: copies are allocated
//! **relation-major** — original-`RelId`-ascending (the input [`Bounds`]
//! iterates in `RelId` order, being a `BTreeMap`), and within one original,
//! state `0..k` ascending. Relation-major rather than state-major so that one
//! variable relation's `k` copies occupy a contiguous `RelId` (hence primary
//! variable) range, which keeps per-relation reasoning — decoding a trace,
//! asserting density — local. Nothing here iterates a hash container.
//!
//! Inert at mt-065: neither entry point is wired into `lower_command`,
//! `compute_bounds`, or `solve_goal`.

use std::collections::{BTreeMap, BTreeSet};

use als_solve::{Cnf, Lit, Var};
use als_syntax::ArenaId;

use crate::bounds::{Bounds, RelBound};
use crate::ir::{Ir, Mutability, RelId, Relation};

/// The separator between a variable relation's name and its state index in a
/// per-state copy's diagnostic name (`this/Node@2`).
///
/// Reserved by construction: `@` is only ever a *prefix* token in Alloy
/// (`@name` suppresses implicit-`this` expansion) and can never occur inside an
/// identifier, so a copy name cannot collide with a user-source relation name,
/// with a skolem (`$label_var`, `als_core::lower`), or with an atom name
/// (`Sig$index`, `als_core::scope`).
const STATE_SUFFIX: char = '@';

/// A [`Bounds`] unrolled to a fixed trace length: static relations bound once,
/// each variable relation replaced by `k` per-state copies.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct UnrolledBounds {
    /// The unrolled bounds. Contains every static relation of the input
    /// unchanged, plus `k` copies of every variable relation.
    ///
    /// The **original** variable [`RelId`]s are deliberately *not* bound here:
    /// the copies replace them outright, so [`Self::states`] is the only bridge
    /// from an original to its per-state instances. Leaving the original bound
    /// too would mint primary variables for a relation no state ever reads
    /// (`allocate_primaries` bounds-drives numbering), inflating the CNF and
    /// the instance-enumeration count with a phantom relation.
    pub bounds: Bounds,
    /// The trace length this view was unrolled to (`>= 1`).
    pub k: usize,
    /// Bridge map: original variable [`RelId`] → its `k` per-state copies,
    /// indexed by state (`states[&r][s]` is `r` at state `s`). Keyed by
    /// `BTreeMap` so iteration is `RelId`-ordered (STYLE C2).
    pub states: BTreeMap<RelId, Vec<RelId>>,
}

impl UnrolledBounds {
    /// The [`RelId`] denoting `original` at `state`, or `None` if `original` is
    /// not a variable relation of this view.
    ///
    /// # Panics
    /// Panics if `state >= k` for a relation that *is* in the map — asking for
    /// a state outside the trace is a caller bug, not user input (STYLE I5).
    #[must_use]
    pub fn at(&self, original: RelId, state: usize) -> Option<RelId> {
        let copies = self.states.get(&original)?;
        assert!(
            state < self.k,
            "state index out of trace: state={state} k={}",
            self.k
        );
        Some(copies[state])
    }

    /// Whether `rel` is one of the unrolled variable relations.
    #[must_use]
    pub fn is_unrolled(&self, rel: RelId) -> bool {
        self.states.contains_key(&rel)
    }
}

/// Unrolls `bounds` to trace length `k`, allocating the per-state copies into
/// `ir` (ADR-0015 decision 1).
///
/// The static/variable partition is read off `ir.relations[r].mutability` —
/// [`compute_bounds`](crate::compute_bounds) set it at every allocation site
/// from the resolved `var` flags, so no separate partition argument exists to
/// fall out of sync with the relation table.
///
/// Only relations *bound in* `bounds` are considered; a caller that wants a
/// command's skolem relations covered passes the augmented bounds (base +
/// `LoweredGoal::skolem_bounds`), exactly as `solve::translate` already builds
/// them. Skolems are static (skolemization is off under temporal operators,
/// `Skolemizer.java:494-526`), so they are copied through untouched either way.
///
/// # Panics
/// Panics if `k == 0` (a trace has at least one state — the jar's `mintrace`
/// floor is 1, alloy6-temporal.md §(b)) or if `bounds` binds a relation `ir`
/// never allocated. Both are internal invariant violations (STYLE I1/E2).
#[must_use]
pub fn unroll(ir: &mut Ir, bounds: &Bounds, k: usize) -> UnrolledBounds {
    assert!(k >= 1, "trace length must be >= 1, got {k}");

    // Snapshot first: allocating into `ir.relations` inside the loop would
    // otherwise interleave reads of a growing arena with the partition lookup.
    // `bounds.iter()` is `RelId`-ascending (BTreeMap), which *is* the pinned
    // copy-allocation order.
    let classified: Vec<(RelId, Mutability, RelBound)> = bounds
        .iter()
        .map(|(rel, bound)| {
            assert!(
                rel.index() < ir.relations.len(),
                "bounds bind a relation absent from the IR: {rel:?}"
            );
            (rel, ir.relations[rel].mutability, bound.clone())
        })
        .collect();

    let mut unrolled = Bounds::new(bounds.universe.clone());
    let mut states: BTreeMap<RelId, Vec<RelId>> = BTreeMap::new();
    let mut static_count = 0usize;

    for (rel, mutability, bound) in &classified {
        match mutability {
            Mutability::Static => {
                unrolled.bind(*rel, bound.clone());
                static_count += 1;
            }
            Mutability::Variable => {
                let template = ir.relations[*rel].clone();
                let copies: Vec<RelId> = (0..k)
                    .map(|state| {
                        let copy = ir.relations.alloc(Relation {
                            name: format!("{}{STATE_SUFFIX}{state}", template.name),
                            arity: template.arity,
                            // The declaring construct is unchanged by unrolling,
                            // so every copy points a diagnostic at the same
                            // `var` declaration (STYLE G2).
                            span: template.span,
                            mutability: Mutability::Variable,
                        });
                        // Atoms are rigid: only the value varies between
                        // states, so every copy keeps the original's bound.
                        unrolled.bind(copy, bound.clone());
                        copy
                    })
                    .collect();
                let previous = states.insert(*rel, copies);
                debug_assert!(
                    previous.is_none(),
                    "relation unrolled twice: {rel:?} (bounds iterate distinct keys)"
                );
            }
        }
    }

    let view = UnrolledBounds {
        bounds: unrolled,
        k,
        states,
    };
    debug_assert_unrolled(&view, &classified, static_count);
    view
}

/// Re-checks the unroller's postconditions, including the negative space
/// (STYLE I1/I3): the shape, the bridge map's totality over exactly the
/// variable relations, and that no original variable relation survives in the
/// unrolled bounds.
fn debug_assert_unrolled(
    view: &UnrolledBounds,
    classified: &[(RelId, Mutability, RelBound)],
    static_count: usize,
) {
    debug_assert_eq!(
        view.bounds.iter().count(),
        static_count + view.states.len() * view.k,
        "unrolled bound count: {} static + {} variable x k={}",
        static_count,
        view.states.len(),
        view.k
    );
    let variables: BTreeSet<RelId> = classified
        .iter()
        .filter(|(_, m, _)| matches!(m, Mutability::Variable))
        .map(|(rel, _, _)| *rel)
        .collect();
    let mapped: BTreeSet<RelId> = view.states.keys().copied().collect();
    debug_assert_eq!(
        variables, mapped,
        "bridge map must cover exactly the variable relations"
    );
    for (original, copies) in &view.states {
        debug_assert_eq!(
            copies.len(),
            view.k,
            "per-state copy count for {original:?}"
        );
        debug_assert!(
            view.bounds.get(*original).is_none(),
            "original variable relation still bound after unrolling: {original:?}"
        );
        debug_assert!(
            copies.iter().all(|copy| copy > original),
            "per-state copies must be allocated after their original: {original:?}"
        );
    }
}

/// The lasso back-loop selector: one solver variable per candidate loop-back
/// state, constrained to exactly one (ADR-0015 decision 1).
///
/// Every SAT temporal instance is a lasso — `k` states plus a back-loop target
/// `l ∈ [0, k-1]`; finite non-looping traces do not exist in this engine
/// (alloy6-temporal.md §(c), `getLoopState()` in range in every SAT probe).
/// `loop_var(s)` is true exactly when the trace loops back to state `s`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LassoSelector {
    vars: Vec<Var>,
}

impl LassoSelector {
    /// Mints `k` fresh variables in `cnf` and constrains exactly one of them.
    ///
    /// Encoding: one at-least-one clause `(l₀ ∨ … ∨ l_{k-1})` plus **pairwise**
    /// at-most-one `⋀_{i<j} (¬lᵢ ∨ ¬l_j)` — the same pairwise shape the
    /// encoder's `at_most_one` uses for `lone`/`one` (`encode/mod.rs`), kept
    /// consistent deliberately: `k` is a trace length (single digits in
    /// practice), so a ladder encoding would trade clarity for nothing.
    ///
    /// Variables are minted before any clause is emitted, in state order, so
    /// numbering is a deterministic function of `k` and the pool size (STYLE
    /// D1).
    ///
    /// # Panics
    /// Panics if `k == 0` — a lasso always has a loop target.
    #[must_use]
    pub fn mint(cnf: &mut Cnf, k: usize) -> Self {
        assert!(k >= 1, "lasso selector needs k >= 1, got {k}");
        let vars: Vec<Var> = (0..k).map(|_| cnf.fresh_var()).collect();
        cnf.add_clause(vars.iter().map(|&v| Lit::positive(v)).collect());
        for i in 0..vars.len() {
            for j in (i + 1)..vars.len() {
                cnf.add_clause(vec![Lit::negative(vars[i]), Lit::negative(vars[j])]);
            }
        }
        Self { vars }
    }

    /// The trace length this selector ranges over.
    #[must_use]
    pub fn k(&self) -> usize {
        self.vars.len()
    }

    /// The variable that is true iff the trace loops back to `state`.
    ///
    /// # Panics
    /// Panics if `state >= k` (STYLE I5: internal indexing, never user input).
    #[must_use]
    pub fn loop_var(&self, state: usize) -> Var {
        assert!(
            state < self.vars.len(),
            "loop state out of range: state={state} k={}",
            self.vars.len()
        );
        self.vars[state]
    }

    /// The loop-index variables, in state order.
    #[must_use]
    pub fn vars(&self) -> &[Var] {
        &self.vars
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use als_syntax::{ArenaId, FileId, Span};

    use crate::bounds::{AtomId, Tuple, TupleSet, Universe};

    fn span() -> Span {
        Span::new(FileId::from_index(0), 0, 1)
    }

    fn universe(n: usize) -> Universe {
        Universe::new((0..n).map(|i| format!("A${i}")).collect())
    }

    fn unary(atoms: &[usize]) -> TupleSet {
        let mut set = TupleSet::empty(1);
        for &a in atoms {
            set.insert(Tuple::new(vec![AtomId::from_index(a)]));
        }
        set
    }

    fn alloc(ir: &mut Ir, name: &str, mutability: Mutability) -> RelId {
        ir.relations.alloc(Relation {
            name: name.to_owned(),
            arity: 1,
            span: span(),
            mutability,
        })
    }

    /// A two-static/two-variable fixture over a 3-atom universe.
    fn fixture() -> (Ir, Bounds, Vec<RelId>) {
        let mut ir = Ir::default();
        let s0 = alloc(&mut ir, "this/S0", Mutability::Static);
        let v0 = alloc(&mut ir, "this/V0", Mutability::Variable);
        let s1 = alloc(&mut ir, "this/S1", Mutability::Static);
        let v1 = alloc(&mut ir, "this/V1", Mutability::Variable);
        let mut bounds = Bounds::new(universe(3));
        bounds.bind(s0, RelBound::exact(unary(&[0])));
        bounds.bind(v0, RelBound::new(unary(&[0]), unary(&[0, 1, 2])));
        bounds.bind(s1, RelBound::new(TupleSet::empty(1), unary(&[1, 2])));
        bounds.bind(v1, RelBound::new(TupleSet::empty(1), unary(&[2])));
        (ir, bounds, vec![s0, v0, s1, v1])
    }

    #[test]
    fn unroll_copies_only_variable_relations() {
        let (mut ir, bounds, rels) = fixture();
        let view = unroll(&mut ir, &bounds, 3);

        // 2 static + 2 variable x 3 states.
        assert_eq!(view.bounds.iter().count(), 2 + 2 * 3);
        assert_eq!(view.states.len(), 2);
        assert!(view.is_unrolled(rels[1]) && view.is_unrolled(rels[3]));
        assert!(!view.is_unrolled(rels[0]) && !view.is_unrolled(rels[2]));
        // Statics survive with their identity and bound untouched.
        assert_eq!(view.bounds.get(rels[0]), bounds.get(rels[0]));
        assert_eq!(view.bounds.get(rels[2]), bounds.get(rels[2]));
        // The originals of the variable relations are gone (the copies replace
        // them — the bridge map is the only handle).
        assert!(view.bounds.get(rels[1]).is_none());
        assert!(view.bounds.get(rels[3]).is_none());
    }

    #[test]
    fn per_state_copies_share_the_original_bound() {
        let (mut ir, bounds, rels) = fixture();
        let view = unroll(&mut ir, &bounds, 4);
        for &original in &[rels[1], rels[3]] {
            for state in 0..view.k {
                let Some(copy) = view.at(original, state) else {
                    panic!("a variable relation must be in the bridge map")
                };
                assert_eq!(view.bounds.get(copy), bounds.get(original));
                assert_eq!(ir.relations[copy].arity, ir.relations[original].arity);
                assert_eq!(ir.relations[copy].span, ir.relations[original].span);
                assert!(ir.relations[copy].is_var());
            }
        }
    }

    #[test]
    fn copy_names_are_state_suffixed_and_collision_proof() {
        let (mut ir, bounds, rels) = fixture();
        let view = unroll(&mut ir, &bounds, 2);
        let names: Vec<&str> = view.states[&rels[1]]
            .iter()
            .map(|&r| ir.relations[r].name.as_str())
            .collect();
        assert_eq!(names, vec!["this/V0@0", "this/V0@1"]);
        // `@` cannot occur inside an Alloy identifier, so no user-source name,
        // skolem (`$…`), or atom name (`Sig$i`) can produce this shape.
        assert!(names.iter().all(|n| n.contains(STATE_SUFFIX)));
    }

    #[test]
    fn allocation_order_is_relation_major_then_state() {
        let (mut ir, bounds, rels) = fixture();
        let before = ir.relations.len();
        let view = unroll(&mut ir, &bounds, 3);
        // V0's three copies, then V1's three, all after the originals.
        let expected: Vec<usize> = (before..before + 6).collect();
        let actual: Vec<usize> = view.states[&rels[1]]
            .iter()
            .chain(view.states[&rels[3]].iter())
            .map(|r| r.index())
            .collect();
        assert_eq!(actual, expected);
    }

    #[test]
    fn k_of_one_is_a_single_copy_per_variable_relation() {
        let (mut ir, bounds, rels) = fixture();
        let view = unroll(&mut ir, &bounds, 1);
        assert_eq!(view.k, 1);
        assert_eq!(view.bounds.iter().count(), 2 + 2);
        assert_eq!(view.states[&rels[1]].len(), 1);
        assert_eq!(
            view.bounds.get(view.states[&rels[1]][0]),
            bounds.get(rels[1])
        );
    }

    #[test]
    fn unrolling_is_deterministic() {
        let dump = |k: usize| {
            let (mut ir, bounds, _) = fixture();
            let view = unroll(&mut ir, &bounds, k);
            let names: Vec<String> = view
                .bounds
                .iter()
                .map(|(r, b)| format!("{}|{:?}|{:?}", ir.relations[r].name, b.lower(), b.upper()))
                .collect();
            format!("{names:?}|{:?}", view.states)
        };
        assert_eq!(dump(3), dump(3));
        assert_ne!(dump(3), dump(2));
    }

    #[test]
    #[should_panic(expected = "trace length must be >= 1")]
    fn unroll_rejects_zero_states() {
        let (mut ir, bounds, _) = fixture();
        let _ = unroll(&mut ir, &bounds, 0);
    }

    #[test]
    #[should_panic(expected = "state index out of trace")]
    fn at_rejects_an_out_of_range_state() {
        let (mut ir, bounds, rels) = fixture();
        let view = unroll(&mut ir, &bounds, 2);
        let _ = view.at(rels[1], 2);
    }

    /// A fully static bounds table unrolls to itself at any `k` — the property
    /// that keeps mt-065 inert for non-temporal models.
    #[test]
    fn a_static_model_unrolls_to_itself() {
        let mut ir = Ir::default();
        let a = alloc(&mut ir, "this/A", Mutability::Static);
        let mut bounds = Bounds::new(universe(2));
        bounds.bind(a, RelBound::new(TupleSet::empty(1), unary(&[0, 1])));
        for k in 1..4 {
            let view = unroll(&mut ir, &bounds, k);
            assert!(view.states.is_empty());
            assert_eq!(view.bounds, bounds);
        }
    }

    /// Brute-force all `2^k` assignments over the selector's variables: the
    /// emitted clauses must admit exactly `k` models (one per loop state).
    #[test]
    fn lasso_selector_admits_exactly_k_models() {
        for k in 1..=5usize {
            let mut cnf = Cnf::new();
            let selector = LassoSelector::mint(&mut cnf, k);
            assert_eq!(selector.k(), k);
            let mut models = 0;
            for mask in 0..(1u32 << k) {
                let value = |v: Var| mask >> v.index() & 1 == 1;
                let satisfied = cnf.clauses().iter().all(|clause| {
                    clause
                        .iter()
                        .any(|lit| value(lit.var()) == lit.is_positive())
                });
                if satisfied {
                    models += 1;
                    // The satisfying assignments are exactly the singletons.
                    assert_eq!(mask.count_ones(), 1);
                }
            }
            assert_eq!(models, k, "exactly-one over k={k}");
        }
    }

    #[test]
    fn lasso_selector_variables_are_state_indexed() {
        let mut cnf = Cnf::new();
        // Mint an unrelated variable first: the selector must not assume it
        // owns variable 0.
        let other = cnf.fresh_var();
        let selector = LassoSelector::mint(&mut cnf, 3);
        assert_eq!(selector.vars().len(), 3);
        assert!(selector.vars().iter().all(|&v| v != other));
        for state in 0..3 {
            assert_eq!(selector.loop_var(state), selector.vars()[state]);
        }
    }

    #[test]
    #[should_panic(expected = "loop state out of range")]
    fn lasso_selector_rejects_an_out_of_range_state() {
        let mut cnf = Cnf::new();
        let selector = LassoSelector::mint(&mut cnf, 2);
        let _ = selector.loop_var(2);
    }

    #[test]
    #[should_panic(expected = "lasso selector needs k >= 1")]
    fn lasso_selector_rejects_zero_states() {
        let mut cnf = Cnf::new();
        let _ = LassoSelector::mint(&mut cnf, 0);
    }
}
