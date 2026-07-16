//! Adversarial correctness net for the CDCL solver (mt-032).
//!
//! SAT has no jar oracle — its oracle is exhaustive self-checking. This suite
//! is the solver's yardstick:
//!
//! 1. A **brute-force reference** ([`brute_force`]) — exhaustive over every
//!    assignment (≤ 20 vars): verdict, model count, and projected-model count.
//! 2. A **fuzz harness** over deterministic random CNFs across regimes (3-SAT
//!    around the ~4.26 phase transition, k-SAT for k∈{2,3,4}, unit-heavy, tiny),
//!    asserting for every instance: verdict agrees with brute force; every SAT
//!    model actually satisfies every clause (independent [`satisfies`] check);
//!    enumeration count equals the brute-force count when blocking over all vars
//!    (the SB-0 gauge foundation); enumeration over a random *subset* equals the
//!    brute-force distinct-projection count; and everything is bit-for-bit
//!    deterministic (solve twice, enumerate twice → identical).
//! 3. **Structured instances**: pigeonhole PHP(n+1, n) UNSAT (exercises
//!    learning/backjumping), graph coloring (SAT + UNSAT), and parity (SAT +
//!    UNSAT).
//!
//! # Determinism (STYLE D4/U5)
//! All randomness is a hand-rolled `SplitMix64` seeded from a named constant
//! (the mt-014 idiom), so two runs produce byte-identical instances and results.
//!
//! # Budget
//! The default budget finishes in a few seconds (debug). For a longer offline
//! run set `METTLE_SAT_FUZZ_ITERS=<n>`:
//! ```text
//! METTLE_SAT_FUZZ_ITERS=50000 cargo test -p als-solve --test conformance -- --nocapture
//! ```

use std::collections::BTreeSet;
use std::time::Instant;

use als_solve::{block, Assignment, Cnf, Lit, Outcome, Var};

// ---------------------------------------------------------------------------
// Hand-rolled PRNG (STYLE P1/P2: zero deps for a ~10-line generator; the mt-014
// SplitMix64 idiom, reused verbatim in spirit).
// ---------------------------------------------------------------------------

struct SplitMix64 {
    state: u64,
}

impl SplitMix64 {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A value in `0..bound` (bound must be nonzero).
    #[allow(
        clippy::cast_possible_truncation,
        reason = "`x % (bound as u64)` is always < bound, itself a usize, so the cast back \
                  to usize cannot lose information"
    )]
    fn below(&mut self, bound: usize) -> usize {
        assert!(bound > 0, "below called with bound 0");
        (self.next_u64() % bound as u64) as usize
    }

    /// An inclusive range `lo..=hi`.
    fn range(&mut self, lo: usize, hi: usize) -> usize {
        lo + self.below(hi - lo + 1)
    }

    fn bool(&mut self) -> bool {
        self.next_u64() & 1 == 0
    }
}

/// Base seed for every fuzz instance (named + greppable, STYLE D4). ASCII "mt032".
const FUZZ_BASE_SEED: u64 = 0x6D_7430_3332;

fn seed_for(iteration: usize) -> u64 {
    FUZZ_BASE_SEED
        ^ (iteration as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15)
        ^ (iteration as u64)
            .wrapping_mul(0xBF58_476D_1CE4_E5B9)
            .rotate_left(17)
}

// ---------------------------------------------------------------------------
// Independent satisfaction checker (STYLE I2 in test form).
// ---------------------------------------------------------------------------

/// Whether `values` (indexed by var) satisfies every clause of `cnf`. Written
/// independently of the solver so a wrong model is caught by construction.
fn satisfies(cnf: &Cnf, values: &[bool]) -> bool {
    cnf.clauses().iter().all(|clause| {
        clause
            .iter()
            .any(|lit| values[lit.var().index()] == lit.is_positive())
    })
}

/// Reads a solver [`Assignment`] into a dense `Vec<bool>` over `all_vars`.
fn model_values(assignment: &Assignment, all_vars: &[Var]) -> Vec<bool> {
    all_vars.iter().map(|&v| assignment.value(v)).collect()
}

// ---------------------------------------------------------------------------
// Brute-force reference (exhaustive, ≤ 20 vars).
// ---------------------------------------------------------------------------

struct BruteForce {
    sat: bool,
    /// Number of distinct total satisfying assignments.
    count: u64,
}

/// Exhaustively decides `cnf` over all `2^n` assignments (n ≤ 20).
fn brute_force(cnf: &Cnf) -> BruteForce {
    let n = cnf.num_vars() as usize;
    assert!(n <= 20, "brute force is exhaustive; keep n small");
    let mut count = 0u64;
    let mut values = vec![false; n];
    for mask in 0u64..(1u64 << n) {
        for (i, slot) in values.iter_mut().enumerate() {
            *slot = (mask >> i) & 1 == 1;
        }
        if satisfies(cnf, &values) {
            count += 1;
        }
    }
    BruteForce {
        sat: count > 0,
        count,
    }
}

/// The number of *distinct projections* onto `subset` among satisfying
/// assignments — the brute-force target for subset enumeration.
fn brute_force_projection_count(cnf: &Cnf, all_vars: &[Var], subset: &[Var]) -> u64 {
    let n = all_vars.len();
    let sub_idx: Vec<usize> = subset.iter().map(|v| v.index()).collect();
    let mut projections: BTreeSet<u64> = BTreeSet::new();
    let mut values = vec![false; n];
    for mask in 0u64..(1u64 << n) {
        for (i, slot) in values.iter_mut().enumerate() {
            *slot = (mask >> i) & 1 == 1;
        }
        if satisfies(cnf, &values) {
            let mut proj = 0u64;
            for (bit, &vi) in sub_idx.iter().enumerate() {
                if values[vi] {
                    proj |= 1 << bit;
                }
            }
            projections.insert(proj);
        }
    }
    projections.len() as u64
}

// ---------------------------------------------------------------------------
// Enumeration via the incremental solver (the mt-033 seam).
// ---------------------------------------------------------------------------

/// Enumerates all models, blocking each over `block_vars`, returning the full
/// model sequence. Blocking over all vars = raw model enumeration; over a subset
/// = distinct-projection enumeration.
fn enumerate(cnf: &Cnf, all_vars: &[Var], block_vars: &[Var]) -> Vec<Vec<bool>> {
    let mut solver = als_solve::CdclSolver::new(cnf);
    let mut models = Vec::new();
    while let Outcome::Sat(assignment) = solver.solve() {
        models.push(model_values(&assignment, all_vars));
        let clause = block(&assignment, block_vars);
        if clause.is_empty() {
            break; // no vars to distinguish ⇒ a single (empty-projection) model
        }
        solver.add_clause(clause);
    }
    models
}

/// One-shot verdict via the incremental solver from a fresh state.
fn solve_once(cnf: &Cnf) -> Outcome {
    als_solve::CdclSolver::new(cnf).solve()
}

// ---------------------------------------------------------------------------
// Random CNF generation across regimes.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug)]
enum Regime {
    /// Random 3-SAT at a chosen clause/var ratio (below/at/above ~4.26).
    ThreeSat(u32),
    /// Random k-SAT, k ∈ {2,3,4}.
    KSat(usize),
    /// Many unit clauses plus a few longer ones.
    UnitHeavy,
    /// Tiny (1–5 vars), lots of clauses — dense corner cases.
    Tiny,
}

/// Builds a random CNF for `regime`, returning it and its variable list.
fn random_cnf(rng: &mut SplitMix64, regime: Regime) -> (Cnf, Vec<Var>) {
    match regime {
        Regime::ThreeSat(ratio_x10) => {
            let n = rng.range(5, 12);
            let m = (n * ratio_x10 as usize) / 10;
            build_ksat(rng, n, m, 3)
        }
        Regime::KSat(k) => {
            let n = rng.range(k.max(4), 12);
            let m = rng.range(n, n * 5);
            build_ksat(rng, n, m, k)
        }
        Regime::UnitHeavy => {
            let n = rng.range(4, 14);
            let (mut cnf, vars) = fresh(n);
            let units = rng.range(1, n);
            for _ in 0..units {
                let v = vars[rng.below(n)];
                cnf.add_clause(vec![signed(rng, v)]);
            }
            let longs = rng.range(0, n);
            for _ in 0..longs {
                let k = rng.range(2, 3);
                add_random_clause(rng, &mut cnf, &vars, k);
            }
            (cnf, vars)
        }
        Regime::Tiny => {
            let n = rng.range(1, 5);
            let (mut cnf, vars) = fresh(n);
            let m = rng.range(1, 8);
            for _ in 0..m {
                let k = rng.range(1, n);
                add_random_clause(rng, &mut cnf, &vars, k);
            }
            (cnf, vars)
        }
    }
}

fn fresh(n: usize) -> (Cnf, Vec<Var>) {
    let mut cnf = Cnf::new();
    let vars: Vec<Var> = (0..n).map(|_| cnf.fresh_var()).collect();
    (cnf, vars)
}

fn signed(rng: &mut SplitMix64, v: Var) -> Lit {
    if rng.bool() {
        Lit::positive(v)
    } else {
        Lit::negative(v)
    }
}

/// Builds a random k-SAT instance with `n` vars and `m` clauses of `k` distinct
/// variables each.
fn build_ksat(rng: &mut SplitMix64, n: usize, m: usize, k: usize) -> (Cnf, Vec<Var>) {
    let (mut cnf, vars) = fresh(n);
    for _ in 0..m {
        add_random_clause(rng, &mut cnf, &vars, k.min(n));
    }
    (cnf, vars)
}

/// Adds one clause of `k` distinct random variables with random polarities.
fn add_random_clause(rng: &mut SplitMix64, cnf: &mut Cnf, vars: &[Var], k: usize) {
    let n = vars.len();
    let k = k.min(n).max(1);
    let mut chosen: Vec<usize> = Vec::with_capacity(k);
    while chosen.len() < k {
        let idx = rng.below(n);
        if !chosen.contains(&idx) {
            chosen.push(idx);
        }
    }
    let clause: Vec<Lit> = chosen.iter().map(|&i| signed(rng, vars[i])).collect();
    cnf.add_clause(clause);
}

// ---------------------------------------------------------------------------
// The fuzz harness.
// ---------------------------------------------------------------------------

/// Vars at/under this bound get the (expensive) full + subset enumeration cross
/// -check; larger instances still get verdict + model-satisfies + determinism.
const ENUM_MAX_VARS: usize = 10;

fn fuzz_iters() -> usize {
    std::env::var("METTLE_SAT_FUZZ_ITERS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(1200)
}

fn regime_for(rng: &mut SplitMix64) -> Regime {
    match rng.below(6) {
        0 => Regime::ThreeSat(30), // below phase transition (ratio 3.0)
        1 => Regime::ThreeSat(43), // at ~4.3
        2 => Regime::ThreeSat(52), // above (5.2)
        3 => Regime::KSat(2 + rng.below(3)),
        4 => Regime::UnitHeavy,
        _ => Regime::Tiny,
    }
}

#[test]
fn fuzz_against_brute_force() {
    let iters = fuzz_iters();
    for iter in 0..iters {
        let mut rng = SplitMix64::new(seed_for(iter));
        let regime = regime_for(&mut rng);
        let (cnf, vars) = random_cnf(&mut rng, regime);
        let n = vars.len();

        let bf = brute_force(&cnf);

        // (a) verdict agreement.
        let outcome = solve_once(&cnf);
        let solver_sat = matches!(outcome, Outcome::Sat(_));
        assert_eq!(
            solver_sat, bf.sat,
            "verdict mismatch on iter {iter} ({regime:?}, n={n}): solver={solver_sat} brute={}",
            bf.sat
        );

        // (b) every SAT model satisfies every clause (independent checker).
        if let Outcome::Sat(ref model) = outcome {
            let values = model_values(model, &vars);
            assert!(
                satisfies(&cnf, &values),
                "solver returned a non-satisfying model on iter {iter} ({regime:?})"
            );
        }

        // (d0) determinism: a fresh solve is bit-identical.
        assert_eq!(
            outcome,
            solve_once(&cnf),
            "non-deterministic verdict/model on iter {iter} ({regime:?})"
        );

        if n > ENUM_MAX_VARS {
            continue;
        }

        // (c) enumeration over ALL vars == brute-force model count.
        let all_models = enumerate(&cnf, &vars, &vars);
        assert_eq!(
            all_models.len() as u64,
            bf.count,
            "all-var enumeration count mismatch on iter {iter} ({regime:?}, n={n})"
        );
        // every enumerated model satisfies, and they are pairwise distinct.
        let mut seen: BTreeSet<Vec<bool>> = BTreeSet::new();
        for m in &all_models {
            assert!(satisfies(&cnf, m), "enumerated a non-model on iter {iter}");
            assert!(seen.insert(m.clone()), "duplicate model on iter {iter}");
        }

        // determinism of the enumeration SEQUENCE.
        assert_eq!(
            all_models,
            enumerate(&cnf, &vars, &vars),
            "non-deterministic enumeration sequence on iter {iter} ({regime:?})"
        );

        // (d) enumeration over a random SUBSET == distinct-projection count.
        if n >= 1 {
            let subset = random_subset(&mut rng, &vars);
            let proj_models = enumerate(&cnf, &vars, &subset);
            let expected = brute_force_projection_count(&cnf, &vars, &subset);
            assert_eq!(
                proj_models.len() as u64,
                expected,
                "subset enumeration count mismatch on iter {iter} ({regime:?}, \
                 subset_len={})",
                subset.len()
            );
            assert_eq!(
                proj_models,
                enumerate(&cnf, &vars, &subset),
                "non-deterministic subset enumeration on iter {iter}"
            );
        }
    }
}

/// A random non-empty subset of `vars` (preserving index order for a stable
/// projection encoding).
fn random_subset(rng: &mut SplitMix64, vars: &[Var]) -> Vec<Var> {
    loop {
        let subset: Vec<Var> = vars.iter().copied().filter(|_| rng.bool()).collect();
        if !subset.is_empty() {
            return subset;
        }
    }
}

// ---------------------------------------------------------------------------
// Structured instances.
// ---------------------------------------------------------------------------

/// Pigeonhole PHP(pigeons, holes): each pigeon in ≥ 1 hole, no two pigeons in
/// the same hole. UNSAT iff pigeons > holes.
fn pigeonhole(pigeons: usize, holes: usize) -> (Cnf, Vec<Var>) {
    let mut cnf = Cnf::new();
    // p[i][h] laid out row-major.
    let mut p: Vec<Vec<Var>> = Vec::with_capacity(pigeons);
    let mut all = Vec::new();
    for _ in 0..pigeons {
        let mut row = Vec::with_capacity(holes);
        for _ in 0..holes {
            let v = cnf.fresh_var();
            row.push(v);
            all.push(v);
        }
        p.push(row);
    }
    // Each pigeon occupies at least one hole.
    for row in &p {
        cnf.add_clause(row.iter().map(|&v| Lit::positive(v)).collect());
    }
    // No two pigeons share a hole.
    for i in 0..pigeons {
        for j in (i + 1)..pigeons {
            for (&pih, &pjh) in p[i].iter().zip(&p[j]) {
                cnf.add_clause(vec![Lit::negative(pih), Lit::negative(pjh)]);
            }
        }
    }
    (cnf, all)
}

#[test]
fn pigeonhole_unsat_and_sat() {
    // UNSAT: more pigeons than holes, for n = 1..=7 (n+1 pigeons, n holes).
    for n in 1..=7 {
        let (cnf, _) = pigeonhole(n + 1, n);
        assert_eq!(
            solve_once(&cnf),
            Outcome::Unsat,
            "PHP({}, {}) must be UNSAT",
            n + 1,
            n
        );
    }
    // SAT sanity: equal pigeons and holes is satisfiable (a permutation).
    let (cnf, vars) = pigeonhole(4, 4);
    match solve_once(&cnf) {
        Outcome::Sat(a) => assert!(satisfies(&cnf, &model_values(&a, &vars))),
        Outcome::Unsat => panic!("PHP(4,4) must be SAT"),
    }
}

/// Proper graph coloring: exactly-one color per vertex (at-least-one +
/// at-most-one) and adjacent vertices differ.
fn coloring(num_vertices: usize, colors: usize, edges: &[(usize, usize)]) -> (Cnf, Vec<Var>) {
    let mut cnf = Cnf::new();
    let mut c: Vec<Vec<Var>> = Vec::with_capacity(num_vertices);
    let mut all = Vec::new();
    for _ in 0..num_vertices {
        let mut row = Vec::with_capacity(colors);
        for _ in 0..colors {
            let v = cnf.fresh_var();
            row.push(v);
            all.push(v);
        }
        c.push(row);
    }
    for row in &c {
        // at least one color
        cnf.add_clause(row.iter().map(|&v| Lit::positive(v)).collect());
        // at most one color
        for a in 0..colors {
            for b in (a + 1)..colors {
                cnf.add_clause(vec![Lit::negative(row[a]), Lit::negative(row[b])]);
            }
        }
    }
    for &(u, w) in edges {
        for (&cu, &cw) in c[u].iter().zip(&c[w]) {
            cnf.add_clause(vec![Lit::negative(cu), Lit::negative(cw)]);
        }
    }
    (cnf, all)
}

#[test]
fn graph_coloring_sat_and_unsat() {
    // C5 (odd cycle) is 3-colorable ⇒ SAT.
    let c5 = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)];
    let (cnf, vars) = coloring(5, 3, &c5);
    match solve_once(&cnf) {
        Outcome::Sat(a) => assert!(satisfies(&cnf, &model_values(&a, &vars))),
        Outcome::Unsat => panic!("C5 with 3 colors must be SAT"),
    }
    // C5 needs > 2 colors ⇒ 2-coloring is UNSAT.
    let (cnf2, _) = coloring(5, 2, &c5);
    assert_eq!(
        solve_once(&cnf2),
        Outcome::Unsat,
        "C5 with 2 colors is UNSAT"
    );

    // K4 (complete on 4) needs 4 colors ⇒ 3-coloring is UNSAT.
    let k4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)];
    let (cnf3, _) = coloring(4, 3, &k4);
    assert_eq!(
        solve_once(&cnf3),
        Outcome::Unsat,
        "K4 with 3 colors is UNSAT"
    );
    // K4 with 4 colors is SAT.
    let (cnf4, vars4) = coloring(4, 4, &k4);
    match solve_once(&cnf4) {
        Outcome::Sat(a) => assert!(satisfies(&cnf4, &model_values(&a, &vars4))),
        Outcome::Unsat => panic!("K4 with 4 colors must be SAT"),
    }
}

/// XOR of two vars encoded in CNF: `a ⊕ b = value`.
fn add_xor2(cnf: &mut Cnf, a: Var, b: Var, value: bool) {
    let (pa, na) = (Lit::positive(a), Lit::negative(a));
    let (pb, nb) = (Lit::positive(b), Lit::negative(b));
    if value {
        // a ⊕ b = 1 ⇔ (a ∨ b) ∧ (¬a ∨ ¬b)
        cnf.add_clause(vec![pa, pb]);
        cnf.add_clause(vec![na, nb]);
    } else {
        // a ⊕ b = 0 ⇔ (a ∨ ¬b) ∧ (¬a ∨ b)
        cnf.add_clause(vec![pa, nb]);
        cnf.add_clause(vec![na, pb]);
    }
}

#[test]
fn parity_sat_and_unsat() {
    // SAT: a chain of XOR constraints has exactly the models consistent with it.
    let (mut cnf, vars) = fresh(3);
    add_xor2(&mut cnf, vars[0], vars[1], true);
    add_xor2(&mut cnf, vars[1], vars[2], false);
    let bf = brute_force(&cnf);
    assert!(bf.sat, "parity chain must be SAT");
    let models = enumerate(&cnf, &vars, &vars);
    assert_eq!(models.len() as u64, bf.count, "parity model count mismatch");
    for m in &models {
        assert!(satisfies(&cnf, m));
    }

    // UNSAT: contradictory parities x⊕y=1 and x⊕y=0.
    let (mut cnf2, vars2) = fresh(2);
    add_xor2(&mut cnf2, vars2[0], vars2[1], true);
    add_xor2(&mut cnf2, vars2[0], vars2[1], false);
    assert_eq!(
        solve_once(&cnf2),
        Outcome::Unsat,
        "contradictory parity is UNSAT"
    );
}

// ---------------------------------------------------------------------------
// Determinism across fresh processes is covered by the fuzz harness (solve /
// enumerate twice). This standalone test pins it on a fixed medium instance.
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Performance sanity (guardrails, not the gauge). Ignored by default so CI
// stays fast and non-flaky; run in release with:
//   cargo test -p als-solve --release --test conformance -- --ignored --nocapture
// ---------------------------------------------------------------------------

#[test]
#[ignore = "perf smoke: run with `cargo test -p als-solve --release --test conformance -- --ignored`"]
fn perf_smoke() {
    // PHP(8,7): UNSAT, exercises learning/backjumping hard.
    let (php, _) = pigeonhole(8, 7);
    let t0 = Instant::now();
    assert_eq!(solve_once(&php), Outcome::Unsat, "PHP(8,7) is UNSAT");
    let php_time = t0.elapsed();

    // 200-var / 850-clause random 3-SAT (near the phase transition).
    let mut rng = SplitMix64::new(0x5A17_5A17_5A17_5A17);
    let (cnf, _) = build_ksat(&mut rng, 200, 850, 3);
    let t1 = Instant::now();
    let _ = solve_once(&cnf);
    let sat_time = t1.elapsed();

    eprintln!("perf smoke: PHP(8,7)={php_time:?}, 200v/850c 3-SAT={sat_time:?}");
    // Generous bounds so the guardrail never flakes; real release times are far
    // under these (see the mt-032 report).
    assert!(
        php_time.as_secs() < 10,
        "PHP(8,7) exceeded 10s: {php_time:?}"
    );
    assert!(sat_time.as_secs() < 10, "3-SAT exceeded 10s: {sat_time:?}");
}

#[test]
fn determinism_on_fixed_instance() {
    let mut rng = SplitMix64::new(0xDEAD_BEEF);
    let (cnf, vars) = build_ksat(&mut rng, 9, 30, 3);
    let a = enumerate(&cnf, &vars, &vars);
    let b = enumerate(&cnf, &vars, &vars);
    assert_eq!(a, b, "enumeration must be reproducible");
    // And a fresh solve matches the first enumerated model (if any).
    if let Outcome::Sat(first) = solve_once(&cnf) {
        assert_eq!(
            model_values(&first, &vars),
            a[0],
            "first model must be stable"
        );
    }
}
