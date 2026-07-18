//! Corpus smoke test (mt-029): every command of every vendored `.als` model
//! must compute a universe without panicking, and — since the whole corpus is
//! valid Alloy that resolves 167/167 (mt-018) — without a scope-phase reject.
//! Also asserts the universe is byte-stable across two runs (STYLE D1/U4).
//! Skips cleanly without `corpus/`.

use std::path::{Path, PathBuf};

use als_core::{compute_universe, TranslateError};
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
fn corpus_universes_compute() {
    let root = workspace_root();
    let corpora = [
        root.join("corpus/alloytools-models/models"),
        root.join("corpus/portus-63"),
    ];
    let present: Vec<&PathBuf> = corpora.iter().filter(|p| p.is_dir()).collect();
    if present.is_empty() {
        eprintln!("SKIP scope_corpus: no corpus directories");
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
    let mut string_defers = 0usize;
    // (file, command index, rendered error) for any scope-phase reject.
    let mut failures: Vec<(PathBuf, usize, String)> = Vec::new();

    for path in &files {
        let Ok(canon) = std::fs::canonicalize(path) else {
            continue;
        };
        let root_str = canon.to_string_lossy().replace('\\', "/");
        let Ok(graph) = ModuleGraph::load(&root_str, &loader) else {
            continue; // load/parse failures are mt-011/017's gauge, not this one
        };
        let Ok(resolved) = resolve(&graph) else {
            continue; // resolve failures are mt-018's gauge
        };
        let world = resolved.world;
        // The jar's `getAllCommands()` returns only the *root* module's
        // commands (verified: an opened util/ordering's test commands never
        // appear). mettle's `world.commands` collects every module's commands,
        // so restrict to the root file — the set the CLI (mt-036) will run.
        let root_file = graph.modules[graph.root].file;
        let mut model_clean = true;
        for (i, cmd) in world
            .commands
            .iter()
            .enumerate()
            .filter(|(_, c)| c.span.file == root_file)
        {
            commands += 1;
            match compute_universe(&world, cmd) {
                Ok(su) => {
                    // Determinism: a second run is byte-identical.
                    let again = compute_universe(&world, cmd).expect("second run");
                    assert_eq!(su.universe, again.universe, "non-deterministic universe");
                }
                // The one typed scope-phase defer the corpus legitimately hits:
                // a non-zero `String` scope (Rung 4 — mt-037's fm2cfs.als
                // wrong-verdict fix). Deterministic like any other outcome.
                Err(TranslateError::StringUnsupported { .. }) => {
                    string_defers += 1;
                    assert!(
                        matches!(
                            compute_universe(&world, cmd),
                            Err(TranslateError::StringUnsupported { .. })
                        ),
                        "non-deterministic scope defer"
                    );
                }
                Err(e) => {
                    model_clean = false;
                    failures.push((path.clone(), i, format!("{e:?}")));
                }
            }
        }
        if model_clean {
            clean_files += 1;
        }
    }

    eprintln!(
        "scope_corpus: {} files ({clean_files} clean), {commands} commands, {string_defers} String defers, {} scope rejects",
        files.len(),
        failures.len()
    );
    for (path, i, err) in &failures {
        eprintln!("  REJECT {}[cmd {i}]: {err}", path.display());
    }
    // The corpus is valid Alloy: apart from the typed String defer above, no
    // command should be rejected by the scope phase. If this ever fires, the
    // listed set is the exact out-of-Rung-3 surface to triage.
    assert!(
        failures.is_empty(),
        "{} corpus commands were rejected by the scope phase (see stderr)",
        failures.len()
    );
}
