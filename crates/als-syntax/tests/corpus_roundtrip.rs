//! Integration test: for every `.als` file in the vendored corpora, checks
//! that parse → pretty-print → re-parse succeeds and yields a structurally
//! identical AST (dump-equal), and that pretty-printing is idempotent. This is
//! the strongest cheap parser oracle before solving lands (mt-012).
//!
//! Mirrors `corpus_parse.rs`: skips cleanly (with an `eprintln!` note, not a
//! failure) when the corpus directories aren't present, and iterates in sorted
//! order for determinism (STYLE U5).

use std::path::{Path, PathBuf};

use als_syntax::{dump, parse, ArenaId, FileId};

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

/// The first line where two multi-line dumps differ, for a compact failure
/// message (never the whole multi-megabyte dump).
fn first_diff(a: &str, b: &str) -> String {
    for (i, (la, lb)) in a.lines().zip(b.lines()).enumerate() {
        if la != lb {
            return format!("line {}: {la:?} != {lb:?}", i + 1);
        }
    }
    format!(
        "length differs: {} vs {} lines",
        a.lines().count(),
        b.lines().count()
    )
}

#[test]
fn corpus_files_roundtrip() {
    let root = workspace_root();
    let corpora = [
        root.join("corpus/alloytools-models/models"),
        root.join("corpus/portus-63"),
    ];

    let present: Vec<&PathBuf> = corpora.iter().filter(|p| p.is_dir()).collect();
    if present.is_empty() {
        eprintln!(
            "SKIP corpus_roundtrip::corpus_files_roundtrip: no corpus directories found under {} \
             (expected for a fresh checkout; run the corpus fetch script to enable this test)",
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
        let ast1 = match parse(&source, FileId::from_index(0)) {
            Ok(a) => a,
            Err(e) => {
                failures.push((path.clone(), format!("initial parse failed: {e}")));
                continue;
            }
        };
        let printed1 = als_syntax::print::pretty_to_string(&ast1);
        let ast2 = match parse(&printed1, FileId::from_index(0)) {
            Ok(a) => a,
            Err(e) => {
                failures.push((
                    path.clone(),
                    format!("re-parse of printed output failed: {e}"),
                ));
                continue;
            }
        };
        let (d1, d2) = (dump(&ast1), dump(&ast2));
        if d1 != d2 {
            failures.push((
                path.clone(),
                format!("structural mismatch — {}", first_diff(&d1, &d2)),
            ));
            continue;
        }
        let printed2 = als_syntax::print::pretty_to_string(&ast2);
        if printed1 != printed2 {
            failures.push((path.clone(), "pretty-printing is not idempotent".to_owned()));
        }
    }

    eprintln!(
        "corpus_roundtrip: {} files, {} pass, {} fail",
        files.len(),
        files.len() - failures.len(),
        failures.len()
    );
    for (path, msg) in &failures {
        eprintln!("  FAIL {}: {msg}", path.display());
    }
    assert!(
        failures.is_empty(),
        "{} of {} corpus files failed to round-trip (see stderr above)",
        failures.len(),
        files.len()
    );
}
