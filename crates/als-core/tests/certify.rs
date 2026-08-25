//! End-to-end proof certification (mt-123, [ADR-0027](../../../docs/adr/0027-cadical-only-solver.md)
//! decision 4): resolve → universe → bounds → lower → encode → DIMACS + DRAT,
//! and — when a checker is on the machine — the proof actually checked.
//!
//! The last test is the one that matters, and it is the reason the others are
//! not enough on their own: everything up to it verifies that mettle wrote
//! *files*, while only drat-trim verifies that what it wrote is a **proof**. It
//! skips cleanly when `tools/drat-trim/drat-trim` is absent (the same pattern the
//! jar-backed tests use — CI has no checker, and a skipped external check must
//! never look like a passing one).

use std::path::{Path, PathBuf};

use als_core::ir::Ir;
use als_core::{
    certify_goal, compute_bounds, compute_universe, lower_command, CertifyOutcome, SolveOptions,
};
use als_types::{resolve, MapLoader, ModuleGraph};

/// Certifies command 0 of `src`, writing artifacts named after `stem`, and
/// returns the outcome with the two paths so the caller can inspect and clean up
/// — deleting them is the *caller's* job (`backend-instrument --certify` does it
/// per row), which is exactly what these tests are standing in for.
fn certify(src: &str, stem: &str) -> (CertifyOutcome, PathBuf, PathBuf) {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let scoped = compute_universe(&world, &graph, &world.commands[0]).expect("universe");
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &scoped, &mut ir);
    let goal = lower_command(&world, &graph, &scoped, &bounds, &mut ir, 0).expect("lower");

    let dir = std::env::temp_dir();
    let unique = format!("{stem}-{}", std::process::id());
    let cnf = dir.join(format!("mettle-certify-{unique}.cnf"));
    let proof = dir.join(format!("mettle-certify-{unique}.drat"));
    let _ = std::fs::remove_file(&cnf);
    let _ = std::fs::remove_file(&proof);

    let outcome = certify_goal(
        &ir,
        &scoped,
        &goal,
        &bounds,
        &SolveOptions::default(),
        &cnf,
        &proof,
    )
    .expect("certify");
    (outcome, cnf, proof)
}

fn size_of(path: &Path) -> u64 {
    std::fs::metadata(path).map_or(0, |m| m.len())
}

/// An UNSAT command produces both halves of a certificate: the CNF that was
/// solved, and a non-empty DRAT proof refuting it.
#[test]
fn an_unsat_command_writes_a_cnf_and_a_proof() {
    let src = "sig A {} sig B extends A {} sig C extends A {} \
                run { some B and some C and #A = 1 } for 3";
    let (outcome, cnf, proof) = certify(src, "unsat");
    let CertifyOutcome::Unsat(m) = outcome else {
        panic!("expected UNSAT, got {}", outcome.name())
    };

    // The DIMACS header must describe the formula the solver was handed, not a
    // re-derivation of it: a proof checked against a differently-sized formula
    // proves nothing about this one.
    let text = std::fs::read_to_string(&cnf).expect("read cnf");
    let header = text.lines().next().expect("a header line");
    assert_eq!(header, format!("p cnf {} {}", m.num_vars, m.num_clauses));
    assert_eq!(
        text.lines().count(),
        m.num_clauses + 1,
        "one line per clause, plus the header"
    );
    assert!(size_of(&proof) > 0, "the DRAT proof is empty");

    let _ = std::fs::remove_file(&cnf);
    let _ = std::fs::remove_file(&proof);
}

/// A goal that folds to `false` while encoding is UNSAT by construction, and
/// says so as its own outcome — it never runs a solver, so it has no proof, and
/// dressing it up as a certified one would be a lie about what was checked.
#[test]
fn a_trivially_unsat_command_writes_nothing() {
    let src = "sig A {} run { some none } for 3";
    let (outcome, cnf, proof) = certify(src, "trivial");
    assert_eq!(outcome, CertifyOutcome::TriviallyUnsat);
    assert!(!cnf.exists(), "a trivial refutation wrote a CNF");
    assert!(!proof.exists(), "a trivial refutation wrote a proof");
}

/// A SAT command is reported, not certified: DRAT expresses unsatisfiability
/// and there is none to express. The files it did write are the caller's to
/// remove, and nothing is left behind once it does.
#[test]
fn a_sat_command_is_reported_rather_than_certified() {
    let src = "sig A {} run { some A } for 3";
    let (outcome, cnf, proof) = certify(src, "sat");
    assert!(
        matches!(outcome, CertifyOutcome::Sat(_)),
        "expected SAT, got {}",
        outcome.name()
    );
    let _ = std::fs::remove_file(&cnf);
    let _ = std::fs::remove_file(&proof);
    assert!(
        !cnf.exists() && !proof.exists(),
        "artifacts survived removal"
    );
}

/// The whole point, when the machine has a checker: drat-trim reads the CNF and
/// the proof mettle wrote and confirms the formula really is unsatisfiable.
///
/// Skipped — loudly, on stderr — when the checker is absent, which is CI's
/// normal state. It is built by `scripts/fetch-drat-trim.sh`.
#[test]
fn drat_trim_verifies_the_proof_when_a_checker_is_present() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("the workspace root is two levels above this crate")
        .to_path_buf();
    let checker = root.join("tools/drat-trim/drat-trim");
    if !checker.is_file() {
        eprintln!(
            "skipping: no DRAT checker at {} (build one with scripts/fetch-drat-trim.sh)",
            checker.display()
        );
        return;
    }

    let src = "sig A {} sig B extends A {} sig C extends A {} \
                run { some B and some C and #A = 1 } for 3";
    let (outcome, cnf, proof) = certify(src, "checked");
    assert!(
        matches!(outcome, CertifyOutcome::Unsat(_)),
        "expected UNSAT, got {}",
        outcome.name()
    );
    let out = std::process::Command::new(&checker)
        .arg(&cnf)
        .arg(&proof)
        .output()
        .expect("run drat-trim");
    let _ = std::fs::remove_file(&cnf);
    let _ = std::fs::remove_file(&proof);

    let said = String::from_utf8_lossy(&out.stdout);
    assert!(
        out.status.success()
            && said
                .split(['\n', '\r'])
                .any(|l| l.trim_end() == "s VERIFIED"),
        "drat-trim did not verify the proof (exit {}):\n{said}",
        out.status
    );
}
