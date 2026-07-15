//! Integration test: parses every `.als` file in the vendored conformance
//! corpora and asserts zero parse errors (the Rung-1 gauge, ADR-0007).
//!
//! Mirrors `corpus_lex.rs`: skips cleanly (with an `eprintln!` note, not a
//! failure) when the corpus directories aren't present, and iterates in
//! sorted order for determinism (STYLE U5).

use std::path::{Path, PathBuf};

use als_syntax::{parse, ArenaId, FileId};

/// Workspace root, two levels up from this crate's manifest.
fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// Recursively collects `.als` files under `dir`, sorted.
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
fn corpus_files_parse_without_error() {
    let root = workspace_root();
    let corpora = [
        root.join("corpus/alloytools-models/models"),
        root.join("corpus/portus-63"),
    ];

    let present: Vec<&PathBuf> = corpora.iter().filter(|p| p.is_dir()).collect();
    if present.is_empty() {
        eprintln!(
            "SKIP corpus_parse::corpus_files_parse_without_error: no corpus directories found \
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
        if let Err(err) = parse(&source, FileId::from_index(0)) {
            failures.push((path.clone(), format!("{err} @ {:?}", err.span())));
        }
    }

    eprintln!(
        "corpus_parse: {} files, {} pass, {} fail",
        files.len(),
        files.len() - failures.len(),
        failures.len()
    );
    for (path, msg) in &failures {
        eprintln!("  FAIL {}: {msg}", path.display());
    }
    assert!(
        failures.is_empty(),
        "{} of {} corpus files failed to parse (see stderr above)",
        failures.len(),
        files.len()
    );
}
