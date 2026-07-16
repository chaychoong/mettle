//! Corpus acceptance test (mt-018): every vendored `.als` model must ACCEPT
//! end-to-end (load → resolve → typecheck), matching the jar's `resolveAll`
//! verdict on the known-good corpus. Skips cleanly without `corpus/`.

use std::path::{Path, PathBuf};

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
fn corpus_models_resolve() {
    let root = workspace_root();
    let corpora = [
        root.join("corpus/alloytools-models/models"),
        root.join("corpus/portus-63"),
    ];
    let present: Vec<&PathBuf> = corpora.iter().filter(|p| p.is_dir()).collect();
    if present.is_empty() {
        eprintln!("SKIP corpus_resolve: no corpus directories");
        return;
    }

    let mut files = Vec::new();
    for dir in &present {
        collect_als_files(dir, &mut files);
    }
    files.sort();

    let loader = FilesystemLoader::new();
    let mut accept = 0usize;
    let mut failures: Vec<(PathBuf, String)> = Vec::new();

    for path in &files {
        let Ok(canon) = std::fs::canonicalize(path) else {
            continue;
        };
        let root_str = canon.to_string_lossy().replace('\\', "/");
        match ModuleGraph::load(&root_str, &loader) {
            Ok(graph) => match resolve(&graph) {
                Ok(_) => accept += 1,
                Err(err) => failures.push((path.clone(), format!("{err:?}"))),
            },
            Err(err) => failures.push((path.clone(), format!("load: {err:?}"))),
        }
    }

    eprintln!(
        "corpus_resolve: {} files, {accept} accept, {} reject",
        files.len(),
        failures.len()
    );
    for (path, err) in &failures {
        eprintln!("  REJECT {}: {err}", path.display());
    }
    assert!(
        failures.is_empty(),
        "{} corpus files were rejected (see stderr)",
        failures.len()
    );
}
