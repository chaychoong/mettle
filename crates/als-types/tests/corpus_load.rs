//! Corpus smoke test for the module-graph loader: every vendored `.als` model
//! **loads fully** — every `open` resolves, either to a local disk copy
//! (`computeModulePath`; disk shadows the embedded stdlib) or to the wired
//! clean-room stdlib table (mt-015).
//!
//! Skips cleanly when `corpus/` is absent (the Rung-1 test precedent).

use std::path::{Path, PathBuf};

use als_types::{FilesystemLoader, ModuleGraph, ResolveError};

/// Workspace root, two levels up from this crate's manifest.
fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// Recursively collects `.als` files under `dir`, sorted for determinism.
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
fn corpus_models_load_fully() {
    let root = workspace_root();
    let corpora = [
        root.join("corpus/alloytools-models/models"),
        root.join("corpus/portus-63"),
    ];
    let present: Vec<&PathBuf> = corpora.iter().filter(|p| p.is_dir()).collect();
    if present.is_empty() {
        eprintln!(
            "SKIP corpus_load: no corpus directories under {} (fresh checkout; run the corpus \
             fetch script to enable this test)",
            root.display()
        );
        return;
    }

    let mut files = Vec::new();
    for dir in &present {
        collect_als_files(dir, &mut files);
    }
    files.sort();

    let loader = FilesystemLoader::new();
    let mut full = 0usize;
    let mut failures: Vec<(PathBuf, ResolveError)> = Vec::new();

    for path in &files {
        // Canonicalize so `computeModulePath` works with absolute paths and the
        // filesystem loader reads them verbatim (no implicit corpus search root).
        let Ok(canon) = std::fs::canonicalize(path) else {
            continue;
        };
        let root_str = canon.to_string_lossy().replace('\\', "/");
        match ModuleGraph::load(&root_str, &loader) {
            Ok(_) => full += 1,
            Err(err) => failures.push((path.clone(), err)),
        }
    }

    eprintln!(
        "corpus_load: {} files, {full} load fully, {} fail",
        files.len(),
        failures.len(),
    );
    for (path, err) in &failures {
        eprintln!("  FAIL {}: {err:?}", path.display());
    }
    assert!(
        failures.is_empty(),
        "{} corpus files failed to load (see stderr)",
        failures.len()
    );
}
