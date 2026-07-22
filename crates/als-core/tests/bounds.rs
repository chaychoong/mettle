//! Bounds-builder tests (mt-030): the reference's `BoundsComputer` behavior,
//! one group per translation-ref §1.4 rule, with per-relation lower/upper tuple
//! sets whose exact values were **jar-verified** against Alloy 6.2.0 (probe
//! harness `scratchpad/probe/BoundsShim.java` + `DumpK2.java`, dumping
//! `A4Solution.getBounds()` / `debugExtractKInput()` at symmetry 0, noOverflow
//! false, `inferPartialInstance=false`). Every golden lists its probe id (B*).
//! The jar prints relation atoms as names (`A$0`, `-8`, …), so we compare
//! mettle's bounds by atom **name** — directly comparable to the oracle dump.
//!
//! These tests do not require the jar to run: the expected tuple sets are pinned
//! as literals here (STYLE U3). The pipeline is resolve → `compute_universe`
//! (mt-029) → `compute_bounds` (mt-030).

use als_core::bounds::RelBound;
use als_core::ir::{
    FormulaKind, Ir, MultTest, RelBinOp, RelCmpOp, RelConst, RelExprId, RelExprKind, RelId,
};
use als_core::{compute_bounds, compute_universe, BoundsResult};
use als_types::{resolve, MapLoader, ModuleGraph, ResolvedWorld, SigId};

/// A fully built command: the resolved world, the shared IR, and the bounds
/// result, plus the universe for name lookups.
struct Built {
    world: ResolvedWorld,
    ir: Ir,
    result: BoundsResult,
}

/// Resolves `src` (single root file), computes the universe + bounds of command
/// 0, and returns everything for inspection.
fn build(src: &str) -> Built {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let scoped = compute_universe(&world, &graph, &world.commands[0]).expect("compute_universe");
    let mut ir = Ir::default();
    let result = compute_bounds(&world, &scoped, &mut ir);
    Built { world, ir, result }
}

impl Built {
    /// The `RelId` of the relation named `name` (as the builder names it:
    /// `A`, `A_remainder`, `A.f`, `Int`, `seq/Int`, `String`).
    fn rel(&self, name: &str) -> RelId {
        match self.ir.relations.iter().find(|(_, r)| r.name == name) {
            Some((id, _)) => id,
            None => panic!("no relation named `{name}`; have: {:?}", self.rel_names()),
        }
    }

    fn rel_names(&self) -> Vec<String> {
        self.ir
            .relations
            .iter()
            .map(|(_, r)| r.name.clone())
            .collect()
    }

    fn has_rel(&self, name: &str) -> bool {
        self.ir.relations.iter().any(|(_, r)| r.name == name)
    }

    fn bound(&self, name: &str) -> &RelBound {
        self.result
            .bounds
            .get(self.rel(name))
            .expect("relation bound")
    }

    /// The lower bound of relation `name` as name-tuples.
    fn lower(&self, name: &str) -> Vec<Vec<String>> {
        self.tuples(self.bound(name).lower())
    }

    /// The upper bound of relation `name` as name-tuples.
    fn upper(&self, name: &str) -> Vec<Vec<String>> {
        self.tuples(self.bound(name).upper())
    }

    fn tuples(&self, ts: &als_core::bounds::TupleSet) -> Vec<Vec<String>> {
        ts.iter()
            .map(|t| {
                t.atoms()
                    .iter()
                    .map(|&a| self.result.bounds.universe.name(a).to_owned())
                    .collect()
            })
            .collect()
    }

    fn sig(&self, qualified: &str) -> SigId {
        self.world
            .sigs
            .iter()
            .find(|(_, s)| s.qualified_name == qualified)
            .map(|(id, _)| id)
            .expect("sig by qualified name")
    }
}

/// A unary golden: `["A$0","A$1"]` → `[["A$0"],["A$1"]]`.
fn unary(names: &[&str]) -> Vec<Vec<String>> {
    names.iter().map(|n| vec![(*n).to_owned()]).collect()
}

// ======================= §1.4 leaf / exact bounds =======================

#[test]
fn plain_leaf_lower_empty_upper_full() {
    // Probe B1: `sig A {} run {} for 3` → this/A lower {} upper {A$0..A$2}.
    let b = build("sig A {}\nrun {} for 3\n");
    assert_eq!(b.lower("this/A"), Vec::<Vec<String>>::new());
    assert_eq!(b.upper("this/A"), unary(&["A$0", "A$1", "A$2"]));
    // Bound alone caps #A (upper==scope): no size constraint (probe B1).
    assert!(b.result.constraints.is_empty());
}

#[test]
fn exact_leaf_is_pinned_lower_equals_upper() {
    // Probe B2: `run {} for exactly 3 A` → lower == upper == {A$0..A$2}; no
    // size formula (bounds pin it).
    let b = build("sig A {}\nrun {} for exactly 3 A\n");
    assert_eq!(b.lower("this/A"), unary(&["A$0", "A$1", "A$2"]));
    assert_eq!(b.upper("this/A"), unary(&["A$0", "A$1", "A$2"]));
    assert!(b.result.constraints.is_empty());
}

// ==================== §1.4 remainder / children ====================

#[test]
fn non_abstract_parent_gets_remainder_no_this_relation() {
    // Probe B3: `sig A {} sig B extends A {} for 3`. A has no own relation; a
    // this/A_remainder relation appears; both B and remainder upper = A pool.
    let b = build("sig A {}\nsig B extends A {}\nrun {} for 3\n");
    assert!(
        !b.has_rel("this/A"),
        "parent A must not get its own relation"
    );
    assert_eq!(b.upper("this/B"), unary(&["A$0", "A$1", "A$2"]));
    assert_eq!(b.upper("this/A_remainder"), unary(&["A$0", "A$1", "A$2"]));
    assert_eq!(b.lower("this/A_remainder"), Vec::<Vec<String>>::new());
    // One child ⇒ no sibling-disjointness formula, and upper==scope ⇒ no size.
    assert!(b.result.constraints.is_empty());
}

#[test]
fn two_children_share_pool_and_get_disjointness() {
    // Probe B4: two children of A share the 3-atom pool; formula `no (B & C)`.
    let b = build("sig A {}\nsig B extends A {}\nsig C extends A {}\nrun {} for 3\n");
    for r in ["this/B", "this/C", "this/A_remainder"] {
        assert_eq!(b.upper(r), unary(&["A$0", "A$1", "A$2"]), "{r}");
    }
    assert_eq!(b.result.constraints.len(), 1, "one disjointness formula");
    assert_disjointness(&b, b.result.constraints[0], "this/B", "this/C");
}

#[test]
fn abstract_parent_has_no_remainder() {
    // Probe B5: abstract A ⇒ no this/A and no this/A_remainder; children only.
    let b = build("abstract sig A {}\nsig B extends A {}\nsig C extends A {}\nrun {} for 3\n");
    assert!(!b.has_rel("this/A"));
    assert!(
        !b.has_rel("this/A_remainder"),
        "abstract parent has no remainder"
    );
    assert_eq!(b.upper("this/B"), unary(&["A$0", "A$1", "A$2"]));
    assert_eq!(b.result.constraints.len(), 1);
    assert_disjointness(&b, b.result.constraints[0], "this/B", "this/C");
}

#[test]
fn inexact_child_upper_is_full_parent_pool_with_size_cap() {
    // Probe B6: `for 4 A, 2 B` (B extends A). B's upper is the *whole* 4-atom
    // parent pool (not capped at 2); the `#B <= 2` cap is a size FORMULA, never
    // a tighter bound — this is the corner where an off-by-one flips verdicts.
    let b = build("sig A {}\nsig B extends A {}\nrun {} for 4 A, 2 B\n");
    assert_eq!(b.upper("this/B"), unary(&["A$0", "A$1", "A$2", "A$3"]));
    assert_eq!(
        b.upper("this/A_remainder"),
        unary(&["A$0", "A$1", "A$2", "A$3"])
    );
    // Exactly one constraint: the `#B <= 2` size formula (n=2 form).
    assert_eq!(b.result.constraints.len(), 1);
    let f = &b.ir.formulas[b.result.constraints[0]].kind;
    assert!(
        matches!(f, FormulaKind::Or(v) if v.len() == 2),
        "size = `no B or (exists)`: {f:?}"
    );
}

#[test]
fn disjointness_emitted_even_for_disjoint_uppers() {
    // Probe B7: exact children mint separate atoms (disjoint uppers), yet the
    // jar still emits `no (B & C)` — disjointness is unconditional.
    let b = build(
        "abstract sig A {}\nsig B extends A {}\nsig C extends A {}\nrun {} for exactly 2 B, exactly 1 C\n",
    );
    assert_eq!(b.result.constraints.len(), 1);
    assert_disjointness(&b, b.result.constraints[0], "this/B", "this/C");
}

// ==================== §1.4 subset sigs ====================

#[test]
fn in_subset_sig_fresh_relation_and_containment() {
    // Probe B8: `sig B in A` → fresh this/B lower {} upper = A pool; `B in A`.
    let b = build("sig A {}\nsig B in A {}\nrun {} for 3\n");
    assert_eq!(b.lower("this/B"), Vec::<Vec<String>>::new());
    assert_eq!(b.upper("this/B"), unary(&["A$0", "A$1", "A$2"]));
    assert_eq!(b.result.constraints.len(), 1, "one containment formula");
    let f = &b.ir.formulas[b.result.constraints[0]].kind;
    let FormulaKind::RelCompare {
        op: RelCmpOp::Subset,
        lhs,
        rhs,
    } = f
    else {
        panic!("expected `B in A`: {f:?}");
    };
    assert!(matches!(b.ir.rel_exprs[*lhs].kind, RelExprKind::Relation(r) if r == b.rel("this/B")));
    // rhs = the parents' union; here a single parent A (leaf) ⇒ Relation(A).
    assert!(matches!(b.ir.rel_exprs[*rhs].kind, RelExprKind::Relation(r) if r == b.rel("this/A")));
}

#[test]
fn exact_subset_sig_is_parent_union_no_relation() {
    // Probe B9: `sig B = A + C` → NO this/B relation, NO formula; B denotes the
    // union A ∪ C.
    let b = build("sig A {}\nsig C {}\nsig B = A + C {}\nrun {} for 3\n");
    assert!(
        !b.has_rel("this/B"),
        "exact subset must not allocate a relation"
    );
    assert!(
        b.result.constraints.is_empty(),
        "exact subset adds no formula"
    );
    // B's denotation is `A + C` (a Union of the two parent relations).
    let denote = b.result.sig_denote[&b.sig("this/B")];
    let RelExprKind::Binary {
        op: RelBinOp::Union,
        lhs,
        rhs,
    } = &b.ir.rel_exprs[denote].kind
    else {
        panic!("B should denote a union");
    };
    assert!(matches!(b.ir.rel_exprs[*lhs].kind, RelExprKind::Relation(r) if r == b.rel("this/A")));
    assert!(matches!(b.ir.rel_exprs[*rhs].kind, RelExprKind::Relation(r) if r == b.rel("this/C")));
}

// ==================== §1.4 fields ====================

#[test]
fn ordinary_field_upper_is_product_of_column_uppers() {
    // Probe B10: `sig B { f: A }` → this/B.f arity 2, upper = B pool × A pool.
    let b = build("sig A {}\nsig B { f: A }\nrun {} for 3\n");
    assert_eq!(b.bound("this/B.f").upper().arity(), 2);
    let up = b.upper("this/B.f");
    assert_eq!(up.len(), 9, "3 B × 3 A");
    assert!(up.contains(&vec!["B$0".to_owned(), "A$0".to_owned()]));
    assert!(up.contains(&vec!["B$2".to_owned(), "A$2".to_owned()]));
    assert_eq!(b.lower("this/B.f"), Vec::<Vec<String>>::new());
}

#[test]
fn multi_column_field_products_all_columns() {
    // Probe B11: `sig B { f: A -> A }` at for 2 → this/B.f arity 3 = B×A×A.
    let b = build("sig A {}\nsig B { f: A -> A }\nrun {} for 2\n");
    assert_eq!(b.bound("this/B.f").upper().arity(), 3);
    assert_eq!(b.upper("this/B.f").len(), 2 * 2 * 2);
}

#[test]
fn int_field_column_is_all_int_atoms() {
    // Probe B12: `sig A { n: Int }` → this/A.n arity 2 upper = A × {all 16 ints}.
    let b = build("sig A { n: Int }\nrun {} for 3\n");
    assert_eq!(b.bound("this/A.n").upper().arity(), 2);
    let up = b.upper("this/A.n");
    assert_eq!(up.len(), 3 * 16, "3 A × 16 int atoms");
    assert!(up.contains(&vec!["A$0".to_owned(), "-8".to_owned()]));
    assert!(up.contains(&vec!["A$2".to_owned(), "7".to_owned()]));
}

#[test]
fn one_sig_field_strips_owner_column() {
    // Probe B13: `one sig B { f: A }` → this/B.f arity **1** (value only),
    // upper = A pool; the field denotes `B -> B.f`.
    let b = build("sig A {}\none sig B { f: A }\nrun {} for 3\n");
    assert_eq!(
        b.bound("this/B.f").upper().arity(),
        1,
        "owner column stripped"
    );
    assert_eq!(b.upper("this/B.f"), unary(&["A$0", "A$1", "A$2"]));
    // one sig B is exact-1 pinned.
    assert_eq!(b.lower("this/B"), unary(&["B$0"]));
    assert_eq!(b.upper("this/B"), unary(&["B$0"]));
    // Field denotation = owner -> stored (arity 2 in the IR).
    let fid = b.world.sigs[b.sig("this/B")].fields[0];
    let denote = b.result.field_denote[&fid];
    let RelExprKind::Binary {
        op: RelBinOp::Product,
        lhs,
        rhs,
    } = &b.ir.rel_exprs[denote].kind
    else {
        panic!("one-sig field must denote owner -> stored");
    };
    assert!(matches!(b.ir.rel_exprs[*lhs].kind, RelExprKind::Relation(r) if r == b.rel("this/B")));
    assert!(
        matches!(b.ir.rel_exprs[*rhs].kind, RelExprKind::Relation(r) if r == b.rel("this/B.f"))
    );
}

#[test]
fn lone_sig_field_keeps_owner_column() {
    // Probe B14: `lone sig B { f: A }` → the owner-column strip is `one`-only;
    // a lone sig's field stays arity 2 (B × A).
    let b = build("sig A {}\nlone sig B { f: A }\nrun {} for 3\n");
    assert_eq!(
        b.bound("this/B.f").upper().arity(),
        2,
        "lone does not strip"
    );
}

// ==================== §1.4 size & multiplicity ====================

#[test]
fn some_sig_gets_some_multiplicity_formula() {
    // Probe B15: `some sig A` (scope 3, upper == scope) → the ONLY formula is
    // `some A` (the size cap is guaranteed by the bound).
    let b = build("some sig A {}\nrun {} for 3\n");
    assert_eq!(b.result.constraints.len(), 1);
    let f = &b.ir.formulas[b.result.constraints[0]].kind;
    let FormulaKind::MultTest {
        test: MultTest::Some,
        expr,
    } = f
    else {
        panic!("expected `some A`: {f:?}");
    };
    assert!(matches!(b.ir.rel_exprs[*expr].kind, RelExprKind::Relation(r) if r == b.rel("this/A")));
}

#[test]
fn one_sig_no_multiplicity_formula_bound_pinned() {
    // Probe B13/one: a `one` sig is exact-1 pinned, so no `one A` formula.
    let b = build("one sig A {}\nrun {} for 3\n");
    assert!(b.result.constraints.is_empty(), "one sig is bound-pinned");
}

#[test]
fn lone_sig_that_grows_gets_lone_cap() {
    // Probe B16: `lone sig B extends A` (B grows into A's pool, scope 1) → the
    // `#B <= 1` cap is emitted as `lone B` (the n=1 size form).
    let b = build("sig A {}\nlone sig B extends A {}\nrun {} for 3\n");
    let lones: Vec<_> = b
        .result
        .constraints
        .iter()
        .filter(|&&f| {
            matches!(
                &b.ir.formulas[f].kind,
                FormulaKind::MultTest {
                    test: MultTest::Lone,
                    ..
                }
            )
        })
        .collect();
    assert_eq!(
        lones.len(),
        1,
        "one `lone B` cap; constraints: {:?}",
        b.constraint_kinds()
    );
}

// ==================== §1.4 builtin bounds ====================

#[test]
fn int_relation_bound_exactly_to_all_int_atoms() {
    // Probe B17: `Int` is bound exactly to the 16 int atoms (bitwidth 4).
    let b = build("sig A {}\nrun {} for 3\n");
    let ints: Vec<Vec<String>> = (-8..=7).map(|v: i64| vec![v.to_string()]).collect();
    assert_eq!(b.lower("Int"), ints);
    assert_eq!(b.upper("Int"), ints);
}

#[test]
fn seq_int_bound_to_first_maxseq_non_negatives() {
    // Probe B18: `for 3` ⇒ maxseq 3 ⇒ seq/Int = {0,1,2}; a command with no
    // overall (exactly-scope form) defaults maxseq 4 ⇒ {0,1,2,3}.
    let b3 = build("sig A {}\nrun {} for 3\n");
    assert_eq!(b3.lower("seq/Int"), unary(&["0", "1", "2"]));
    assert_eq!(b3.upper("seq/Int"), unary(&["0", "1", "2"]));
    let b4 = build("sig A {}\nrun {} for exactly 3 A\n");
    assert_eq!(b4.upper("seq/Int"), unary(&["0", "1", "2", "3"]));
}

#[test]
fn string_relation_bound_empty() {
    // Rung-4 deferral (module docs): String is bound exactly empty for now.
    let b = build("sig A {}\nrun {} for 3\n");
    assert_eq!(b.upper("String"), Vec::<Vec<String>>::new());
}

#[test]
fn univ_and_none_denote_constants_not_relations() {
    // univ/none are IR constants (RelConst), never allocated as relations.
    let b = build("sig A {}\nrun {} for 3\n");
    let univ = b.result.sig_denote[&b.world.builtins.univ];
    assert!(matches!(
        b.ir.rel_exprs[univ].kind,
        RelExprKind::Const(RelConst::Univ)
    ));
    let none = b.result.sig_denote[&b.world.builtins.none];
    assert!(matches!(
        b.ir.rel_exprs[none].kind,
        RelExprKind::Const(RelConst::None)
    ));
}

// ==================== determinism (STYLE D1/U4) ====================

#[test]
fn bounds_are_byte_stable_across_runs() {
    let src = "abstract sig A {}\nsig B extends A {}\none sig C {}\nsig D in A {}\nsig E { f: A }\nrun {} for 3\n";
    let a = build(src);
    let c = build(src);
    assert_eq!(
        a.result.bounds, c.result.bounds,
        "bounds must be deterministic"
    );
}

// ============================ helpers ============================

impl Built {
    fn constraint_kinds(&self) -> Vec<String> {
        self.result
            .constraints
            .iter()
            .map(|&f| format!("{:?}", self.ir.formulas[f].kind))
            .collect()
    }
}

/// Asserts `formula` is `no (relA & relB)` (order-insensitive on the operands).
fn assert_disjointness(b: &Built, formula: als_core::ir::FormulaId, ra: &str, rb: &str) {
    let FormulaKind::MultTest {
        test: MultTest::No,
        expr,
    } = &b.ir.formulas[formula].kind
    else {
        panic!("expected `no (..)`");
    };
    let RelExprKind::Binary {
        op: RelBinOp::Intersect,
        lhs,
        rhs,
    } = &b.ir.rel_exprs[*expr].kind
    else {
        panic!("expected an intersection");
    };
    let got = [relation_of(b, *lhs), relation_of(b, *rhs)];
    let want = [b.rel(ra), b.rel(rb)];
    assert!(
        got == want || got == [want[1], want[0]],
        "disjointness operands {got:?} != {want:?}"
    );
}

fn relation_of(b: &Built, e: RelExprId) -> RelId {
    match b.ir.rel_exprs[e].kind {
        RelExprKind::Relation(r) => r,
        ref other => panic!("expected a relation expr, got {other:?}"),
    }
}

// ================ §1.2 scope raise reaches the bounds (probe B19) ================

#[test]
fn raised_exact_parent_gets_no_size_formula() {
    // `for exactly 2 P, exactly 3 C` (C extends P): the scope phase raises P
    // to exactly 3 (translation-ref §1.2 scope raise), so P's upper (C's 3
    // atoms) equals its scope and no size formula is emitted — the jar's
    // Kodkod goal for this model is the bare reflexive list (jar-verified
    // 2026-07-16, probe B19; found in mt-030 review: without the raise this
    // model tripped the builder's exactness debug_assert).
    let b = build("sig P {}\nsig C extends P {}\nrun {} for exactly 2 P, exactly 3 C\n");
    assert_eq!(b.lower("this/C"), b.upper("this/C"), "C exact");
    assert_eq!(b.upper("this/C").len(), 3);
    assert!(
        b.upper("this/P_remainder").is_empty(),
        "no floating P atoms"
    );
    assert!(
        b.result.constraints.is_empty(),
        "no size/disjointness formulas: single child, bound-pinned"
    );
}
