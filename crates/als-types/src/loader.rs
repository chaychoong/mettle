//! Source-loading abstraction. The module graph asks a [`ModuleLoader`] for
//! the text at a computed file path; the loader is the only part of the layer
//! that touches the outside world, so tests inject sources deterministically
//! without a filesystem (STYLE D4/U5) and the CLI plugs in the real disk.
//!
//! The **search order** (resolution-doc §2.1 — computed path, verbatim,
//! disk, `.md` sibling, embedded stdlib) lives in the graph loader, not here:
//! a `ModuleLoader` answers exactly one question, "what text is at this path?"
//! (STYLE S1). The embedded-stdlib fallback (step 5) is [`crate::stdlib`],
//! tried by the graph loader after the loader returns `None`.

use std::collections::BTreeMap;
use std::path::PathBuf;

/// Resolves a filesystem-style path to source text.
///
/// Returns `None` when nothing is at that path (a miss the search order
/// continues past), `Some(text)` on a hit. Implementations must be
/// deterministic and side-effect-free with respect to mettle's pipeline.
pub trait ModuleLoader {
    /// The source text at `path`, or `None` if absent.
    fn load(&self, path: &str) -> Option<String>;
}

/// A filesystem loader: reads UTF-8 `.als`/`.md` sources from disk.
///
/// It reads paths **verbatim** as handed to it by the search order — it does
/// **not** add the corpus (or any other directory) as an implicit search root.
/// The parent-relative `computeModulePath` step already produces the correct
/// on-disk path, so a corpus model that opens `util/ordering` finds the local
/// `.../util/ordering.als` only when the path computation lands there
/// (resolution-doc §2.1 step 1) — never because this loader searches for it.
#[derive(Debug, Default, Clone)]
pub struct FilesystemLoader;

impl FilesystemLoader {
    /// Creates a filesystem loader.
    #[must_use]
    pub fn new() -> Self {
        Self
    }
}

impl ModuleLoader for FilesystemLoader {
    fn load(&self, path: &str) -> Option<String> {
        // A non-UTF-8 or unreadable file is treated as "absent" so the search
        // order continues; a genuinely-missing target surfaces as
        // `ModuleFileNotFound` once every step misses.
        std::fs::read_to_string(PathBuf::from(path)).ok()
    }
}

/// An in-memory loader backed by a path→source map. The test harness (and any
/// caller that already holds sources) injects modules through it, so unit
/// fixtures exercise `computeModulePath`, cycles, aliasing, and the `.md`
/// fallback with zero disk dependence.
#[derive(Debug, Default, Clone)]
pub struct MapLoader {
    sources: BTreeMap<String, String>,
}

impl MapLoader {
    /// Creates an empty map loader.
    #[must_use]
    pub fn new() -> Self {
        Self {
            sources: BTreeMap::new(),
        }
    }

    /// Inserts a source at a path (normalized by the graph loader before
    /// lookup, so insert paths in already-normalized form).
    #[must_use]
    pub fn with(mut self, path: &str, source: &str) -> Self {
        self.sources.insert(path.to_owned(), source.to_owned());
        self
    }

    /// Inserts a source at a path in place.
    pub fn insert(&mut self, path: &str, source: &str) {
        self.sources.insert(path.to_owned(), source.to_owned());
    }
}

impl ModuleLoader for MapLoader {
    fn load(&self, path: &str) -> Option<String> {
        self.sources.get(path).cloned()
    }
}
