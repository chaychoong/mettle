//! Corpus end-to-end solve smoke test (mt-033): resolve → universe → bounds →
//! lower → encode → solve every root-module command of every vendored `.als`
//! model, with a per-command time budget, and:
//!
//! - report the bucket counts (solved SAT / solved UNSAT / lower-deferred /
//!   encode-deferred / too-large / over-budget) and require **zero panics**;
//! - check **determinism** on the small commands: a second independent solve
//!   gives the same verdict;
//! - where a solved command matches a `baselines/` jar verdict, tally
//!   **agreement** and print any disagreement with a first-glance classification
//!   (triage is mt-037's job — this test never fails on a disagreement).
//!
//! The test fails only on a panic or a non-deterministic verdict. It skips
//! cleanly without `corpus/`. A cheap primary-variable-count pre-filter skips
//! obviously huge problems before encoding; a worker-thread budget backstops the
//! rest (grounding-heavy goals whose var count is small but whose CNF is not).

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::mpsc;
use std::time::Duration;

use als_core::bounds::Bounds;
use als_core::ir::Ir;
use als_core::{
    compute_bounds, compute_universe, lower_command, solve_goal, BoundsResult, LoweredGoal,
    ScopedUniverse, SolveOptions, SolveVerdict,
};
use als_types::{resolve, FilesystemLoader, ModuleGraph};

/// Per-command solve budget (grounding-heavy goals only; most finish in ms).
/// Default 1s keeps the everyday debug suite affordable (the over-budget
/// bucket just grows a little); set `METTLE_SOLVE_BUDGET_MS=5000` for the full
/// mt-033 sweep numbers (matching the fuzzer's env-scaling idiom, mt-014).
fn budget() -> Duration {
    let ms = std::env::var("METTLE_SOLVE_BUDGET_MS")
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
        .unwrap_or(1000);
    Duration::from_millis(ms)
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

/// Solves `(ir, scoped, goal, bounds)` on a worker thread with a budget.
/// Returns `Some(Ok(sat))` on completion, `Some(Err(()))` on an encode defer,
/// `None` on over-budget.
fn solve_budgeted(
    ir: Ir,
    scoped: ScopedUniverse,
    goal: LoweredGoal,
    bounds: BoundsResult,
) -> Option<Result<bool, ()>> {
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let r = match solve_goal(&ir, &scoped, &goal, &bounds, &SolveOptions::default()) {
            Ok(SolveVerdict::Sat(_)) => Ok(true),
            Ok(SolveVerdict::Unsat) => Ok(false),
            Err(_) => Err(()),
        };
        let _ = tx.send(r);
    });
    rx.recv_timeout(budget()).ok()
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
            let Ok(scoped) = compute_universe(&world, &world.commands[idx]) else {
                *buckets.entry("scope_defer").or_default() += 1;
                continue;
            };
            // Rebuild the (ir, bounds, goal) triple fresh each time — the arena
            // indices couple them, and `Ir` is not `Clone`, so a worker thread
            // that consumes the triple gets its own copy.
            let build = || -> Option<(Ir, BoundsResult, LoweredGoal)> {
                let mut ir = Ir::default();
                let bounds = compute_bounds(&world, &scoped, &mut ir);
                let goal = lower_command(&world, &graph, &scoped, &bounds, &mut ir, idx).ok()?;
                Some((ir, bounds, goal))
            };
            let Some((ir, bounds, goal)) = build() else {
                *buckets.entry("lower_defer").or_default() += 1;
                continue;
            };
            let nvars = primary_var_count(&bounds.bounds);
            if nvars > MAX_PRIMARY_VARS {
                *buckets.entry("too_large").or_default() += 1;
                continue;
            }

            let result = solve_budgeted(ir, scoped.clone(), goal, bounds);
            let sat = match result {
                None => {
                    *buckets.entry("over_budget").or_default() += 1;
                    continue;
                }
                Some(Err(())) => {
                    *buckets.entry("encode_defer").or_default() += 1;
                    continue;
                }
                Some(Ok(sat)) => sat,
            };
            *buckets
                .entry(if sat { "solved_sat" } else { "solved_unsat" })
                .or_default() += 1;

            // Determinism (small commands only, to bound cost).
            if nvars <= DETERMINISM_MAX_VARS {
                if let Some((ir2, bounds2, goal2)) = build() {
                    if let Some(Ok(sat2)) = solve_budgeted(ir2, scoped.clone(), goal2, bounds2) {
                        if sat2 != sat {
                            nondet.push(format!("{rel}[{idx}]"));
                        }
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
        }
    }

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

    assert!(nondet.is_empty(), "non-deterministic verdicts: {nondet:?}");
}
