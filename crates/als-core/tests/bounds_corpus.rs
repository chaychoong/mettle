//! Corpus smoke test (mt-030): every root-module command of every vendored
//! `.als` model must compute a universe *and* bounds without panicking, the
//! per-relation `RelBound` invariants must hold (they self-assert on
//! construction: same arity, lower ⊆ upper), and the whole build must be
//! deterministic (two runs → equal bounds and equal constraint count). Skips
//! cleanly without `corpus/`.
//!
//! This is the Rung-3 analogue of `scope_corpus.rs`: it exercises the bounds
//! builder across the real 167-model corpus, catching any sig/field shape the
//! hand-written goldens miss.

use std::path::{Path, PathBuf};

use als_core::ir::Ir;
use als_core::{compute_bounds, compute_universe};
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

#[test]
fn corpus_bounds_compute() {
    let root = workspace_root();
    let corpora = [
        root.join("corpus/alloytools-models/models"),
        root.join("corpus/portus-63"),
    ];
    let present: Vec<&PathBuf> = corpora.iter().filter(|p| p.is_dir()).collect();
    if present.is_empty() {
        eprintln!("SKIP bounds_corpus: no corpus directories");
        return;
    }

    let mut files = Vec::new();
    for dir in &present {
        collect_als_files(dir, &mut files);
    }
    files.sort();

    let loader = FilesystemLoader::new();
    let mut clean_files = 0usize;
    let mut commands = 0usize;
    let mut relations = 0usize;
    // (file, command index, message) for any panic-free failure surfaced below.
    let mut failures: Vec<(PathBuf, usize, String)> = Vec::new();

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
        // Only the root module's commands run (mt-036 CLI surface), matching
        // scope_corpus.rs.
        let root_file = graph.modules[graph.root].file;
        let mut model_clean = true;
        for (i, cmd) in world
            .commands
            .iter()
            .enumerate()
            .filter(|(_, c)| c.span.file == root_file)
        {
            commands += 1;
            let Ok(scoped) = compute_universe(&world, &graph, cmd) else {
                // A scope reject is scope_corpus.rs's gauge; the corpus is clean
                // there, so this should not fire.
                model_clean = false;
                failures.push((path.clone(), i, "scope reject".to_owned()));
                continue;
            };
            // compute_bounds self-asserts the RelBound invariants (arity, lower
            // ⊆ upper) and Bounds::bind (no double-bind) on construction.
            let mut ir = Ir::default();
            let result = compute_bounds(&world, &scoped, &mut ir);
            relations += result.bounds.iter().count();

            // Determinism: a second, independent build is byte-identical.
            let mut ir2 = Ir::default();
            let again = compute_bounds(&world, &scoped, &mut ir2);
            if result.bounds != again.bounds {
                model_clean = false;
                failures.push((path.clone(), i, "non-deterministic bounds".to_owned()));
            }
            if result.constraints.len() != again.constraints.len() {
                model_clean = false;
                failures.push((
                    path.clone(),
                    i,
                    "non-deterministic constraint count".to_owned(),
                ));
            }
        }
        if model_clean {
            clean_files += 1;
        }
    }

    eprintln!(
        "bounds_corpus: {} files ({clean_files} clean), {commands} commands, {relations} relations bound, {} failures",
        files.len(),
        failures.len()
    );
    for (path, i, msg) in &failures {
        eprintln!("  FAIL {}[cmd {i}]: {msg}", path.display());
    }
    assert!(
        failures.is_empty(),
        "{} corpus commands failed bounds computation (see stderr)",
        failures.len()
    );
}
