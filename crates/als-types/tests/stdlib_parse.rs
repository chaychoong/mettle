//! Parse + round-trip test for mettle's own clean-room `util/*` stdlib
//! (mt-015, ADR-0006). Reads each of the 11 bundled modules from disk via a
//! `CARGO_MANIFEST_DIR`-relative path (deliberately not `include_str!`, so
//! this stays a plain file-system check like the corpus tests) and asserts
//! each parses, then round-trips (parse -> pretty-print -> reparse ->
//! structural-dump equal), mirroring
//! `crates/als-syntax/tests/corpus_roundtrip.rs`.
//!
//! This test never reads anything under `corpus/`.

use std::path::{Path, PathBuf};

use als_syntax::{dump, parse, print::pretty_to_string, ArenaId, FileId};

/// The exact 11 modules the jar embeds under `models/util/`
/// (docs/reference/alloy6-resolution.md §7).
const STDLIB_MODULES: [&str; 11] = [
    "ordering", "integer", "boolean", "natural", "sequence", "sequniv", "seqrel", "relation",
    "graph", "ternary", "time",
];

fn stdlib_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("stdlib/util")
}

#[test]
fn stdlib_modules_parse_and_roundtrip() {
    let dir = stdlib_dir();
    let mut failures = Vec::new();

    for name in STDLIB_MODULES {
        let path = dir.join(format!("{name}.als"));
        let source = match std::fs::read_to_string(&path) {
            Ok(s) => s,
            Err(e) => {
                failures.push(format!("{}: could not read file: {e}", path.display()));
                continue;
            }
        };

        let ast1 = match parse(&source, FileId::from_index(0)) {
            Ok(a) => a,
            Err(e) => {
                failures.push(format!("{}: initial parse failed: {e}", path.display()));
                continue;
            }
        };

        let printed1 = pretty_to_string(&ast1);
        let ast2 = match parse(&printed1, FileId::from_index(0)) {
            Ok(a) => a,
            Err(e) => {
                failures.push(format!(
                    "{}: re-parse of printed output failed: {e}",
                    path.display()
                ));
                continue;
            }
        };

        let (d1, d2) = (dump(&ast1), dump(&ast2));
        if d1 != d2 {
            failures.push(format!(
                "{}: structural mismatch between original and reparsed dump",
                path.display()
            ));
            continue;
        }

        let printed2 = pretty_to_string(&ast2);
        if printed1 != printed2 {
            failures.push(format!(
                "{}: pretty-printing is not idempotent",
                path.display()
            ));
        }
    }

    assert!(
        failures.is_empty(),
        "{} of {} stdlib modules failed to parse/round-trip:\n{}",
        failures.len(),
        STDLIB_MODULES.len(),
        failures.join("\n")
    );
}

/// Sanity check that the 11-module set on disk is exactly the pinned set —
/// catches accidental extra/missing files independent of the fixed list
/// above.
#[test]
fn stdlib_dir_has_exactly_the_pinned_modules() {
    let dir = stdlib_dir();
    let mut on_disk: Vec<String> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("could not read {}: {e}", dir.display()))
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|p| p.extension().is_some_and(|ext| ext == "als"))
        .filter_map(|p| p.file_stem().map(|s| s.to_string_lossy().into_owned()))
        .collect();
    on_disk.sort();

    let mut expected: Vec<String> = STDLIB_MODULES.iter().map(ToString::to_string).collect();
    expected.sort();

    assert_eq!(
        on_disk, expected,
        "stdlib/util directory contents drifted from the pinned mt-015 module list"
    );
}
