//! Corpus end-to-end solve smoke test (mt-033): resolve → universe → bounds →
//! lower → encode → solve every root-module command of every vendored `.als`
//! model, under **deterministic effort budgets**, and:
//!
//! - report the bucket counts (solved SAT / solved UNSAT / lower-deferred /
//!   encode-deferred / too-large / over-budget / panic);
//! - check **determinism** on the small commands: a second independent solve
//!   gives the same verdict;
//! - where a solved command matches a `baselines/` jar verdict, tally
//!   **agreement** and print any disagreement with a first-glance classification
//!   (triage is mt-037's job — this test never fails on a disagreement).
//!
//! The test fails on a non-deterministic verdict, a self-check failure, or any
//! panic — every panic is caught **per command** and listed by name rather than
//! aborting the run, so one sweep inventories every latent encoder/lowering bug
//! instead of stopping at the first (see the `catch_unwind` note below). It
//! skips cleanly without `corpus/`.
//!
//! # Resource discipline (the mt-035 OOM lesson)
//! Everything runs **inline on this thread** with bounded effort — no worker
//! threads, no wall-clock. An earlier version spawned a worker per command and
//! abandoned it on `recv_timeout`; the abandoned solvers kept grounding and
//! learning (keep-all clause DB) forever, and enough of them OOM'd the machine.
//! The budgets that replace it are fixed functions of the input, so bucket
//! counts are byte-identical run to run and machine to machine:
//! - a cheap primary-variable pre-filter skips obviously huge problems
//!   (`too_large`) before any allocation;
//! - [`SolveOptions::encode_budget`] stops grounding-heavy goals whose var
//!   count is small but whose CNF is not (also `too_large`);
//! - [`SolveOptions::conflict_budget`] stops hard search (`over_budget`),
//!   freeing all interim state the moment it trips.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use als_core::bounds::Bounds;
use als_core::ir::Ir;
use als_core::{
    compute_bounds, compute_universe, lower_command, self_check, solve_goal, BoundsResult,
    LoweredGoal, ScopedUniverse, SolveOptions, SolveVerdict, TranslateError,
};
use als_types::{resolve, FilesystemLoader, ModuleGraph};

/// Per-command conflict budget (hard search only; most commands solve with a
/// handful of conflicts). The default keeps the everyday **debug** suite
/// affordable — a hard command's conflicts cost milliseconds each unoptimized
/// on a big CNF, so a few hundred keeps the worst commands to ~a second each
/// (the `over_budget` bucket just grows a little); set
/// `METTLE_SOLVE_CONFLICTS=200000` for a fuller sweep (the env-scaling idiom
/// of the mt-014 fuzzer).
fn conflict_budget() -> u64 {
    std::env::var("METTLE_SOLVE_CONFLICTS")
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
        .unwrap_or(500)
}

/// Per-command encode-effort budget (gate requests, folded or not; join
/// pair-scans; CNF clauses — scale with `METTLE_SOLVE_ENCODE_BUDGET`). Bounds
/// grounding-heavy goals deterministically on both *time* (each unit of effort
/// is counted once, whether or not it survives constant-folding) and memory:
/// at roughly 100 bytes per clause across the CNF and the solver's
/// arena/watches, the default keeps one command's encoding around 100 MB and
/// its encode time to ~a second unoptimized.
fn encode_budget() -> u64 {
    std::env::var("METTLE_SOLVE_ENCODE_BUDGET")
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
        .unwrap_or(1_000_000)
}

/// Skip encoding a command whose primary-variable count exceeds this (a huge
/// CNF is not what this smoke test measures; recorded as `too_large`).
const MAX_PRIMARY_VARS: usize = 6000;
/// Re-solve (determinism check) only commands at or below this var count.
const DETERMINISM_MAX_VARS: usize = 400;

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn collect_als_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_als_files(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "als") {
            out.push(path);
        }
    }
}

/// The number of primary variables the bounds imply (`Σ upper − lower`).
fn primary_var_count(bounds: &Bounds) -> usize {
    bounds
        .iter()
        .map(|(_, b)| b.upper().len() - b.lower().len())
        .sum()
}

/// One budgeted, inline solve of `(ir, scoped, goal, bounds)`.
///
/// `Solved(sat, self_check_failure)` carries the **checked-mode self-check**
/// result for a SAT instance (mt-034): the instance is re-evaluated against its
/// own goal and any failure is returned as a message (`None` = passed).
enum SolveOutcome {
    Solved(bool, Option<String>),
    /// The conflict budget ran out before a verdict.
    OverBudget,
    /// The clause cap stopped the encoding.
    TooLarge,
    /// Any other typed encode defer (Rung-3 slice gaps).
    EncodeDefer,
}

fn solve_budgeted(
    ir: &Ir,
    scoped: &ScopedUniverse,
    goal: &LoweredGoal,
    bounds: &BoundsResult,
) -> SolveOutcome {
    let opts = SolveOptions {
        conflict_budget: Some(conflict_budget()),
        encode_budget: Some(encode_budget()),
        ..SolveOptions::default()
    };
    match solve_goal(ir, scoped, goal, bounds, &opts) {
        Ok(SolveVerdict::Sat(inst)) => {
            let sc = self_check(ir, scoped, goal, &inst, &opts, &bounds.bounds)
                .err()
                .map(|f| f.to_string());
            SolveOutcome::Solved(true, sc)
        }
        Ok(SolveVerdict::Unsat) => SolveOutcome::Solved(false, None),
        Ok(SolveVerdict::Unknown) => SolveOutcome::OverBudget,
        Err(TranslateError::CapacityExceeded { .. }) => SolveOutcome::TooLarge,
        Err(_) => SolveOutcome::EncodeDefer,
    }
}

/// Parses `baselines/alloytools-models-verdict.txt` into `(relpath, idx) →
/// "SAT"/"UNSAT"`.
fn load_baseline(root: &Path) -> BTreeMap<(String, usize), String> {
    let mut map = BTreeMap::new();
    let Ok(text) = std::fs::read_to_string(root.join("baselines/alloytools-models-verdict.txt"))
    else {
        return map;
    };
    for line in text.lines().skip(1) {
        let cols: Vec<&str> = line.split_whitespace().collect();
        if cols.len() < 6 {
            continue;
        }
        let Ok(idx) = cols[1].parse::<usize>() else {
            continue;
        };
        if cols[5] == "SAT" || cols[5] == "UNSAT" {
            map.insert((cols[0].to_owned(), idx), cols[5].to_owned());
        }
    }
    map
}

#[test]
#[allow(
    clippy::too_many_lines,
    reason = "one cohesive corpus sweep: walk, bucket, determinism, baseline diff"
)]
fn corpus_solve() {
    let root = workspace_root();
    let corpora = [
        root.join("corpus/alloytools-models/models"),
        root.join("corpus/portus-63"),
    ];
    let present: Vec<&PathBuf> = corpora.iter().filter(|p| p.is_dir()).collect();
    if present.is_empty() {
        eprintln!("SKIP solve_corpus: no corpus directories");
        return;
    }
    let baseline = load_baseline(&root);

    let mut files = Vec::new();
    for dir in &present {
        collect_als_files(dir, &mut files);
    }
    files.sort();

    let loader = FilesystemLoader::new();
    let mut commands = 0usize;
    let mut buckets: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut agree = 0usize;
    let mut disagree = 0usize;
    let mut disagreements: Vec<String> = Vec::new();
    let mut nondet: Vec<String> = Vec::new();
    let mut selfcheck_failures: Vec<String> = Vec::new();
    let mut panics: Vec<String> = Vec::new();

    // The old worker-thread harness (the mt-039 incident) silently turned a
    // panicking command into an `over_budget` bucket entry: a worker panic
    // dropped its channel, and a dropped channel looks exactly like a
    // `recv_timeout` from the caller's side. `catch_unwind` around each
    // command instead surfaces every panic explicitly (bucketed `panic`,
    // listed by `file[idx]`), so one sweep inventories every latent bug in
    // one run rather than dying at the first — the sweep still fails (the
    // final `panics.is_empty()` assert), it just fails with a complete list.
    // The default panic hook prints a full backtrace-shaped message per
    // panic; with potentially hundreds of commands in this corpus that would
    // drown the bucket/baseline report, so it's silenced for the loop and
    // restored immediately after.
    let prev_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));

    for path in &files {
        let Ok(canon) = std::fs::canonicalize(path) else {
            continue;
        };
        let root_str = canon.to_string_lossy().replace('\\', "/");
        let Ok(graph) = ModuleGraph::load(&root_str, &loader) else {
            continue;
        };
        let Ok(resolved) = resolve(&graph) else {
            continue;
        };
        let world = resolved.world;
        let root_file = graph.modules[graph.root].file;
        let rel = path
            .strip_prefix(&root)
            .unwrap_or(path)
            .to_string_lossy()
            .replace('\\', "/");
        for (idx, _) in world
            .commands
            .iter()
            .enumerate()
            .filter(|(_, c)| c.span.file == root_file)
        {
            commands += 1;
            // Progress trace for debugging hangs: prints the command about to run
            // before any potentially-slow bounds/lower/solve work starts, so a
            // stuck sweep points at the offending command instead of just spinning.
            if std::env::var_os("METTLE_TRACE").is_some() {
                eprintln!("TRACE {rel}[{idx}]");
            }
            let Ok(scoped) = compute_universe(&world, &graph, &world.commands[idx]) else {
                *buckets.entry("scope_defer").or_default() += 1;
                continue;
            };

            // Everything from here down — build, solve, determinism re-solve,
            // baseline comparison — runs under `catch_unwind` (see the note
            // above the loop): a panic anywhere in lowering/bounds/encode/solve
            // for *this one command* must not take out the rest of the sweep.
            // `continue` cannot cross a closure boundary, so branches that used
            // to `continue` now `return` from the closure instead; control
            // returns to the `for` loop either way once the closure is done.
            let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                // Rebuild the (ir, bounds, goal) triple fresh for each solve —
                // the arena indices couple them and `Ir` is not `Clone`.
                let build = || -> Option<(Ir, BoundsResult, LoweredGoal)> {
                    let mut ir = Ir::default();
                    let bounds = compute_bounds(&world, &scoped, &mut ir);
                    let goal =
                        lower_command(&world, &graph, &scoped, &bounds, &mut ir, idx).ok()?;
                    Some((ir, bounds, goal))
                };
                let Some((ir, bounds, goal)) = build() else {
                    *buckets.entry("lower_defer").or_default() += 1;
                    return;
                };
                let nvars = primary_var_count(&bounds.bounds);
                if nvars > MAX_PRIMARY_VARS {
                    *buckets.entry("too_large").or_default() += 1;
                    return;
                }

                let sat = match solve_budgeted(&ir, &scoped, &goal, &bounds) {
                    SolveOutcome::OverBudget => {
                        *buckets.entry("over_budget").or_default() += 1;
                        return;
                    }
                    SolveOutcome::TooLarge => {
                        *buckets.entry("too_large").or_default() += 1;
                        return;
                    }
                    SolveOutcome::EncodeDefer => {
                        *buckets.entry("encode_defer").or_default() += 1;
                        return;
                    }
                    SolveOutcome::Solved(sat, self_check_fail) => {
                        if let Some(msg) = self_check_fail {
                            selfcheck_failures.push(format!("{rel}[{idx}]: {msg}"));
                        }
                        sat
                    }
                };
                *buckets
                    .entry(if sat { "solved_sat" } else { "solved_unsat" })
                    .or_default() += 1;

                // Determinism (small commands only, to bound cost). The budgets
                // are deterministic too, so re-solving cannot flip a verdict to
                // over-budget or back.
                if nvars <= DETERMINISM_MAX_VARS {
                    drop((ir, bounds, goal));
                    if let Some((ir2, bounds2, goal2)) = build() {
                        if let SolveOutcome::Solved(sat2, _) =
                            solve_budgeted(&ir2, &scoped, &goal2, &bounds2)
                        {
                            if sat2 != sat {
                                nondet.push(format!("{rel}[{idx}]"));
                            }
                        } else {
                            nondet.push(format!("{rel}[{idx}] (verdict became a non-verdict)"));
                        }
                    }
                }

                // Baseline agreement (alloytools-models only).
                if let Some(expected) = baseline.get(&(rel.clone(), idx)) {
                    let ours = if sat { "SAT" } else { "UNSAT" };
                    if ours == expected {
                        agree += 1;
                    } else {
                        disagree += 1;
                        disagreements.push(format!("{rel}[{idx}]: mettle={ours} jar={expected}"));
                    }
                }
            }));

            if let Err(payload) = outcome {
                let msg = payload
                    .downcast_ref::<&str>()
                    .map(|s| (*s).to_owned())
                    .or_else(|| payload.downcast_ref::<String>().cloned())
                    .unwrap_or_else(|| "non-string panic payload".to_owned());
                *buckets.entry("panic").or_default() += 1;
                panics.push(format!("{rel}[{idx}]: {msg}"));
            }
        }
    }

    std::panic::set_hook(prev_hook);

    eprintln!("solve_corpus: {commands} commands");
    for (b, n) in &buckets {
        eprintln!("  {b}: {n}");
    }
    eprintln!("baseline overlap: {agree} agree, {disagree} disagree");
    for d in &disagreements {
        eprintln!("  DISAGREE {d}");
    }
    for n in &nondet {
        eprintln!("  NON-DETERMINISTIC {n}");
    }
    eprintln!("self-check: {} failures", selfcheck_failures.len());
    for s in &selfcheck_failures {
        eprintln!("  SELF-CHECK-FAIL {s}");
    }
    eprintln!("panics: {}", panics.len());
    for p in &panics {
        eprintln!("  PANIC {p}");
    }

    assert!(nondet.is_empty(), "non-deterministic verdicts: {nondet:?}");
    // Every solved SAT instance must satisfy its own goal (mt-034, translation-ref
    // §6). The one baseline disagreement — `mediaAssets.als[3]` (`check
    // PasteNotAffectHidden`, jar UNSAT / mettle SAT) — is an *under-constrained
    // goal* (a dropped field-`disj`; §10.4), so its instance genuinely satisfies
    // mettle's own (too-weak) goal and self-checks clean: zero failures expected.
    assert!(
        selfcheck_failures.is_empty(),
        "self-check failures (mettle solver/encoder bugs): {selfcheck_failures:?}"
    );
    // Every panic is a mettle bug (lowering/bounds/encode/solve), never a user
    // error (STYLE E5) — the sweep stays red while any exist. The point of
    // catching them per-command (see the note above the loop) is that this one
    // run names ALL of them, not just the first, so triage has a complete list
    // instead of a moving target across re-runs.
    assert!(panics.is_empty(), "panics (mettle bugs): {panics:?}");
}
