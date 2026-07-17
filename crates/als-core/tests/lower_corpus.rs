//! Corpus lowering smoke test (mt-031): every root-module command of every
//! vendored `.als` model must **lower** — resolve → universe → bounds → lower —
//! either to a goal or to one of the documented typed defer-errors
//! ([`TranslateError`]: temporal / string / not-yet-lowerable), with **zero
//! panics** and full determinism (two independent lowers → identical goal).
//!
//! This is the Rung-3 analogue of `bounds_corpus.rs`. It prints the success /
//! defer bucket counts (defers are expected — temporal models, `util/ordering`
//! `pred/totalOrder`, exotic field shapes — not failures); the test fails only
//! on a panic or a non-deterministic lower. Skips cleanly without `corpus/`.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use als_core::ir::Ir;
use als_core::{compute_bounds, compute_universe, lower_command, TranslateError};
use als_syntax::ArenaId;
use als_types::{resolve, FilesystemLoader, ModuleGraph};

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

/// The stable defer-bucket name for a `TranslateError` variant.
fn defer_bucket(e: &TranslateError) -> &'static str {
    match e {
        TranslateError::TemporalUnsupported { .. } => "temporal",
        TranslateError::StringUnsupported { .. } => "string",
        TranslateError::LoweringUnsupported { .. } => "not-yet-lowerable",
        TranslateError::HigherOrder { .. } => "higher-order",
        // Scope-phase errors cannot reach the lowerer (the universe already
        // succeeded) and the clause cap is an encode-phase guard, but keep the
        // match exhaustive.
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

/// A determinism signature of a lowered goal: the goal id, conjunct count, and
/// the arena sizes — identical across two independent, deterministic lowers.
fn signature(ir: &Ir, goal: &als_core::LoweredGoal) -> (usize, usize, usize, usize, usize) {
    (
        goal.goal.index(),
        goal.conjuncts.len(),
        ir.formulas.len(),
        ir.rel_exprs.len(),
        ir.int_exprs.len(),
    )
}

#[test]
fn corpus_lower() {
    let root = workspace_root();
    let corpora = [
        root.join("corpus/alloytools-models/models"),
        root.join("corpus/portus-63"),
    ];
    let present: Vec<&PathBuf> = corpora.iter().filter(|p| p.is_dir()).collect();
    if present.is_empty() {
        eprintln!("SKIP lower_corpus: no corpus directories");
        return;
    }

    let mut files = Vec::new();
    for dir in &present {
        collect_als_files(dir, &mut files);
    }
    files.sort();

    let loader = FilesystemLoader::new();
    let mut n_files = 0usize;
    let mut commands = 0usize;
    let mut ok = 0usize;
    let mut defers: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut defer_examples: BTreeMap<&'static str, String> = BTreeMap::new();
    let mut nondeterministic: Vec<(PathBuf, usize)> = Vec::new();

    for path in &files {
        let Ok(canon) = std::fs::canonicalize(path) else {
            continue;
        };
        let root_str = canon.to_string_lossy().replace('\\', "/");
        let Ok(graph) = ModuleGraph::load(&root_str, &loader) else {
            continue; // load/parse failures are mt-011/017's gauge
        };
        let Ok(resolved) = resolve(&graph) else {
            continue; // resolve failures are mt-018's gauge
        };
        let world = resolved.world;
        n_files += 1;
        let root_file = graph.modules[graph.root].file;
        for (i, cmd) in world
            .commands
            .iter()
            .enumerate()
            .filter(|(_, c)| c.span.file == root_file)
        {
            commands += 1;
            let Ok(scoped) = compute_universe(&world, cmd) else {
                continue; // scope rejects are scope_corpus.rs's gauge
            };
            let mut ir = Ir::default();
            let bounds = compute_bounds(&world, &scoped, &mut ir);
            // A panic here fails the test (zero-panic requirement).
            match lower_command(&world, &graph, &scoped, &bounds, &mut ir, i) {
                Ok(goal) => {
                    ok += 1;
                    // Determinism: a second, independent lower is identical.
                    let mut ir2 = Ir::default();
                    let bounds2 = compute_bounds(&world, &scoped, &mut ir2);
                    let goal2 = lower_command(&world, &graph, &scoped, &bounds2, &mut ir2, i)
                        .expect("second lower must also succeed");
                    if signature(&ir, &goal) != signature(&ir2, &goal2) {
                        nondeterministic.push((path.clone(), i));
                    }
                }
                Err(e) => {
                    let bucket = defer_bucket(&e);
                    *defers.entry(bucket).or_default() += 1;
                    defer_examples
                        .entry(bucket)
                        .or_insert_with(|| format!("{}[cmd {i}]: {e}", path.display()));
                }
            }
        }
    }

    let total_defers: usize = defers.values().sum();
    eprintln!(
        "lower_corpus: {n_files} files, {commands} commands → {ok} lowered, {total_defers} deferred"
    );
    for (bucket, n) in &defers {
        eprintln!(
            "  defer[{bucket}]: {n}  e.g. {}",
            defer_examples.get(bucket).map_or("", String::as_str)
        );
    }
    for (path, i) in &nondeterministic {
        eprintln!("  NON-DETERMINISTIC {}[cmd {i}]", path.display());
    }

    // The gate: every command either lowered or deferred with a typed error
    // (guaranteed by the exhaustive `match` above — no wrong verdict), and every
    // lower is deterministic.
    assert!(
        nondeterministic.is_empty(),
        "{} corpus commands lowered non-deterministically (see stderr)",
        nondeterministic.len()
    );
    assert!(commands > 0, "no root commands exercised");
}
