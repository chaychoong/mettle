//! Integration test: lexes every `.als` file in the vendored conformance
//! corpora and asserts zero lex errors.
//!
//! Skips cleanly (with an `eprintln!` note, not a failure) when the corpus
//! directories aren't present -- mirrors how `als-conform`'s oracle jar
//! tests skip when the jar isn't available, since the corpora are rebuilt
//! by `scripts/fetch-corpora.sh` (see `docs/reference/corpora.md`), not
//! guaranteed to exist in every checkout.

use std::path::{Path, PathBuf};

use als_syntax::{lex, ArenaId, FileId};

/// Workspace root, two levels up from this crate's manifest.
fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// Recursively collects `.als` files under `dir`, sorted (STYLE U5:
/// deterministic tests, no hashmap/readdir-order dependence).
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
fn corpus_files_lex_without_error() {
    let root = workspace_root();
    let corpora = [
        root.join("corpus/alloytools-models/models"),
        root.join("corpus/portus-63"),
    ];

    let present: Vec<&PathBuf> = corpora.iter().filter(|p| p.is_dir()).collect();
    if present.is_empty() {
        eprintln!(
            "SKIP corpus_lex::corpus_files_lex_without_error: no corpus directories found \
             under {} (expected for a fresh checkout; run the corpus fetch script to enable \
             this test)",
            root.display()
        );
        return;
    }

    let mut files = Vec::new();
    for dir in &present {
        collect_als_files(dir, &mut files);
    }
    files.sort();

    let mut failures = Vec::new();
    for path in &files {
        let Ok(source) = std::fs::read_to_string(path) else {
            failures.push((path.clone(), "could not read file as UTF-8".to_owned()));
            continue;
        };
        if let Err(err) = lex(&source, FileId::from_index(0)) {
            failures.push((path.clone(), err.to_string()));
        }
    }

    eprintln!(
        "corpus_lex: {} files, {} pass, {} fail",
        files.len(),
        files.len() - failures.len(),
        failures.len()
    );
    for (path, msg) in &failures {
        eprintln!("  FAIL {}: {msg}", path.display());
    }
    assert!(
        failures.is_empty(),
        "{} of {} corpus files failed to lex (see stderr above)",
        failures.len(),
        files.len()
    );
}
