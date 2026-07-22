//! Symmetry-breaking conformance (mt-048, translation-ref §16). Jar-free and
//! CI-safe: every pinned count was produced by running the reference jar
//! (`oracle/org.alloytools.alloy.dist.jar`) **at authoring time** on the probe
//! model quoted in each test, via the conform harness:
//!
//! ```text
//! cargo build -p als-conform
//! ./target/debug/conform <probe>.als --symmetry <N> --enumerate exhaustive
//! ```
//!
//! (each jar invocation under a hard `timeout`). The tests assert mettle's own
//! SB-quotiented enumeration count equals the jar's, at the same symmetry — never
//! calling the jar at test time (STYLE U3). Probe sources live inline; the
//! matching files are cached in `scratchpad/src794/sbprobes/` for re-pinning.
//!
//! The lex-leader predicate is **verdict-neutral** (§16): it only removes
//! isomorphic copies of satisfying assignments, so every probe is SAT at every
//! symmetry — only the enumerated count changes.

use als_core::ir::Ir;
use als_core::{compute_bounds, compute_universe, enumerate, lower_command, SolveOptions};
use als_types::{resolve, MapLoader, ModuleGraph};

/// Exhaustively enumerates command 0 of `src` at the given symmetry cap and
/// returns the count. `symmetry = 0` disables SBP (the raw SB-0 count); any
/// non-zero value is the lex-leader cap (translation-ref §16.3).
fn count_at(src: &str, symmetry: u32) -> usize {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let scoped = compute_universe(&world, &graph, &world.commands[0]).expect("universe");
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &scoped, &mut ir);
    let goal = lower_command(&world, &graph, &scoped, &bounds, &mut ir, 0).expect("lower");
    let opts = SolveOptions {
        symmetry,
        ..SolveOptions::default()
    };
    enumerate(&ir, &scoped, &goal, &bounds, &opts)
        .expect("enumerate")
        .count()
}

/// Y1 (translation-ref §16.3 worked example / §10.12): `run { some A } for 3`
/// enumerates the upward-closed non-empty subsets of a 3-atom set — **3** at
/// SB=20 (the symmetry quotient), **7** at SB=0 (the raw count = non-empty
/// subsets of {A0,A1,A2}). `usesInts` is false here (no `Int`/`#`/`sum`/`Int[·]`
/// in the goal), so the int atoms form one class no relation ranges over and
/// contribute no SBP bits. Probe: `sbprobes/y1.als`.
#[test]
fn y1_some_a_for_3() {
    let src = "sig A {}\nrun { some A } for 3\n";
    assert_eq!(count_at(src, 20), 3, "Y1 SB=20 = 3");
    assert_eq!(count_at(src, 0), 7, "Y1 SB=0 = 7 (raw)");
}

/// An int-using goal (translation-ref §16.1.1): `#` in the formula changes
/// nothing for symmetry — int atoms are singleton classes always, on both
/// sides. `run { #A = 2 } for 3` = **1** at SB=20, **3** at SB=0 (the three
/// 2-subsets of {A0,A1,A2}, quotiented to one). Probe:
/// `sbprobes/usesint_true.als`.
#[test]
fn uses_ints_true_card_two() {
    let src = "sig A {}\nrun { #A = 2 } for 3\n";
    assert_eq!(count_at(src, 20), 1, "#A=2 SB=20 = 1");
    assert_eq!(count_at(src, 0), 3, "#A=2 SB=0 = 3 (raw)");
}

/// Skolem participation (translation-ref §16.1/§16.3): a top-level `some x: A`
/// mints a `$show_x` skolem constant that **participates in SBP generation**
/// (skolems are added to the bounds and appear in `relParts`), and `$`-prefixed
/// skolems sort before `this/…`. `run show { some x: A | x = x } for 3` = **3**
/// at SB=20, **12** at SB=0. Probe: `sbprobes/skolem.als`.
#[test]
fn skolem_participates_in_sbp() {
    let src = "sig A {}\nrun show { some x: A | x = x } for 3\n";
    assert_eq!(count_at(src, 20), 3, "skolem SB=20 = 3");
    assert_eq!(count_at(src, 0), 12, "skolem SB=0 = 12 (raw)");
}

/// Cap truncation + relation-name ordering (translation-ref §16.3). A sig with
/// **two** binary fields `f`, `g` (relParts sorted by `(arity, name)` ⇒ `this/A.f`
/// before `this/A.g`); the per-`(class, pair)` bit list is truncated at the
/// symmetry cap. The counts move with the cap, proving mettle replicates the
/// jar's exact per-pair truncation: **1140** at SB=20 (full breaking), **1403**
/// at SB=2, **4182** at SB=1, **4352** at SB=0 (raw). Probe:
/// `sbprobes/twofield.als`.
#[test]
fn two_field_cap_truncation_and_name_order() {
    let src = "sig A { f: set A, g: set A }\n\
               fact { all a: A | lone a.f and lone a.g }\n\
               run { } for 3\n";
    assert_eq!(count_at(src, 20), 1140, "twofield SB=20 = 1140");
    assert_eq!(count_at(src, 2), 1403, "twofield SB=2 = 1403 (cap bites)");
    assert_eq!(
        count_at(src, 1),
        4182,
        "twofield SB=1 = 4182 (cap bites harder)"
    );
    assert_eq!(count_at(src, 0), 4352, "twofield SB=0 = 4352 (raw)");
}

/// `util/ordering` symmetry inertness (translation-ref §16.1 item 3, LEDGER-004).
/// `open util/ordering[A]` pins `first`/`next`/`last` to exact constants, so the
/// ordered atoms split into singleton classes and the ordering relations are
/// constant (skipped in `relParts`): there is nothing left to permute. The count
/// is **1** at both SB=20 and SB=0 — the uniqueness comes from the exact bounds,
/// not from symmetry breaking. Probe: `sbprobes/ordering.als`.
#[test]
fn util_ordering_symmetry_inert() {
    let src = "open util/ordering[A]\nsig A {}\nrun { } for 4\n";
    assert_eq!(count_at(src, 20), 1, "ordering SB=20 = 1");
    assert_eq!(count_at(src, 0), 1, "ordering SB=0 = 1");
}

/// Unmentioned-sig participation (tech-lead review probe, translation-ref
/// §16.1 item 1). The jar's `retainAll` is a **no-op for Alloy-generated
/// problems**: every sig relation is mentioned by Alloy's conjoined formula, so
/// a sig the *command* never references still enumerates freely **and**
/// participates in SBP generation. `sig A {} sig B {} run { some A } for 3`:
/// jar SB-0 = **56** (7 nonempty-A × 2³ free B), jar SB=20 = **12** (3
/// upward-closed nonempty A × 4 upward-closed B) — B eats SBP slots exactly
/// like A. Pins that mettle's full-bounds detection/relParts input set is the
/// jar's effective set. Probe: `sbprobes/review/unmentioned.als`.
#[test]
fn unmentioned_sig_participates() {
    let src = "sig A {}\nsig B {}\nrun { some A } for 3\n";
    assert_eq!(count_at(src, 20), 12, "unmentioned SB=20 = 12");
    assert_eq!(count_at(src, 0), 56, "unmentioned SB=0 = 56 (raw)");
}

// A `univ`-typed field probe (`sbprobes/review/univfield_small.als`) found a
// **pre-existing, symmetry-independent** SB-0 count divergence at mt-048 review:
// the jar's `univ` is `Int ∪ String ∪ (live union of top-level sigs)`
// (A4Solution.java:336–338/699 at `794226dd`), not the all-atoms constant mettle
// lowered. **Fixed in mt-053** (LEDGER-011): `univ`/`iden` in user-expression
// position now lower to that live union, so `sig A { f: A -> univ } run { some f }
// for 2 A, 1 Int` counts **65549** at SB-0 (was 65565) and **32902** at SB=20.
// The full jar-pinned probe matrix (rows 1–9 of `scratchpad/probe/mt053/NOTES.md`)
// lands as live tests in `crates/als-core/tests/univ_conformance.rs`.

/// String atoms are symmetry-inert, padding included (translation-ref §16.1.1,
/// probe fmrun — the mt-048-review root cause of the fm2cfs SB-20 family): the
/// jar mints a per-atom exact `s2k` singleton for **every** string atom
/// (A4Solution.java:391–400), so string atoms are never quotiented — only the
/// `Class` swap collapses the two bijective `name` functions.
/// `for exactly 2 Class, exactly 2 String` = **3** at SB=20, **4** at SB=0.
/// Probe: `sbprobes/review/fmrun.als`.
#[test]
fn string_atoms_symmetry_inert() {
    let src = "sig Class { name: one String }\n\
               run { some Class } for exactly 2 Class, exactly 2 String\n";
    assert_eq!(count_at(src, 20), 3, "fmrun SB=20 = 3");
    assert_eq!(count_at(src, 0), 4, "fmrun SB=0 = 4 (raw)");
}

/// The check-with-skolem variant of the same shape (probe fmstr): with string
/// atoms inert there are no string-class pairs at all, and the two constant
/// `name` functions are `Class`-swap-invariant — so SB=20 equals the raw
/// count. **2** at both SB=20 and SB=0. Probe: `sbprobes/review/fmstr.als`.
#[test]
fn string_check_skolem_no_quotient() {
    let src = "sig Class { name: one String }\n\
               check R { all n: String | some c: Class | c.name = n } \
               for exactly 2 Class, exactly 2 String\n";
    assert_eq!(count_at(src, 20), 2, "fmstr SB=20 = 2");
    assert_eq!(count_at(src, 0), 2, "fmstr SB=0 = 2 (raw)");
}

/// Int atoms are singletons even in a goal with zero int usage while a relation
/// ranges over them via `univ` (probe uf1-SB20): SB=20 equals SB-0 — no
/// quotient over the int columns. **7** at both.
/// (`univ` here is the live union since mt-053, but it coincides with all-atoms
/// on this model — `A` is exact-1, so no dead atoms — and both counts are
/// jar-pinned.) Probe: `sbprobes/review/uf1.als`.
#[test]
fn int_atoms_inert_under_univ_field() {
    let src = "sig A { f: A -> univ }\nrun { some f } for 1 A, 1 Int\n";
    assert_eq!(count_at(src, 20), 7, "uf1 SB=20 = 7");
    assert_eq!(count_at(src, 0), 7, "uf1 SB=0 = 7 (raw)");
}
