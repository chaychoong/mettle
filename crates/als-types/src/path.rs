//! Module-path arithmetic: the `computeModulePath` search-order step and the
//! small path helpers it needs.
//!
//! Paths here are **normalized, forward-slash strings** — mettle does its own
//! lexical normalization (resolve `.`/`..`, collapse repeated separators)
//! rather than hitting the real filesystem, so path identity is deterministic
//! and testable (STYLE D4/U5) and does not depend on a file existing on disk.
//!
//! `computeModulePath` reproduces the reference's parent-relative resolution
//! (resolution-doc §2.1): an `open` target is resolved relative to the
//! directory the *parent* module resolved from, adjusted by how deep the
//! parent's own declared module path was. See [`compute_module_path`] for the
//! exact algorithm and the one corner-case caveat (resolution-doc §9).

/// Splits a normalized path into its non-empty components.
///
/// A leading `/` is reported via `absolute`; the returned components never
/// include empty segments or `.`.
fn split_components(path: &str) -> (bool, Vec<&str>) {
    let absolute = path.starts_with('/');
    let components = path
        .split('/')
        .filter(|seg| !seg.is_empty() && *seg != ".")
        .collect();
    (absolute, components)
}

/// Lexically normalizes a forward-slash path: resolves `.`/`..`, collapses
/// repeated separators, and preserves a leading `/` (absolute) marker.
///
/// A `..` that would climb above a relative root is preserved literally (there
/// is nothing above it to cancel), matching ordinary lexical path semantics.
#[must_use]
pub fn normalize(path: &str) -> String {
    let absolute = path.starts_with('/');
    let mut stack: Vec<&str> = Vec::new();
    for seg in path.split('/') {
        match seg {
            "" | "." => {}
            ".." => {
                // Pop a real segment; keep a leading `..` when nothing (or only
                // another `..`) is below it, unless the path is absolute (then
                // `..` at the root simply vanishes, as on a real filesystem).
                if matches!(stack.last(), Some(&top) if top != "..") {
                    stack.pop();
                } else if !absolute {
                    stack.push("..");
                }
            }
            other => stack.push(other),
        }
    }
    let joined = stack.join("/");
    if absolute {
        format!("/{joined}")
    } else if joined.is_empty() {
        ".".to_owned()
    } else {
        joined
    }
}

/// Returns the directory reached by removing the last `n` components of
/// `path` (the filename counts as the first component removed).
///
/// `up(".../a/b/c.als", 1)` is `.../a/b`; `up(_, 0)` is the path unchanged
/// (normalized). Climbing past the root yields the root (`/` or `.`).
#[must_use]
pub fn up(path: &str, n: usize) -> String {
    let (absolute, mut components) = split_components(path);
    let keep = components.len().saturating_sub(n);
    components.truncate(keep);
    let joined = components.join("/");
    if absolute {
        format!("/{joined}")
    } else if joined.is_empty() {
        ".".to_owned()
    } else {
        joined
    }
}

/// Resolves an `open` target to a candidate file path, the reference's
/// `computeModulePath` (resolution-doc §2.1, step 1).
///
/// - `parent_module_segs` — the parent module's *declared* module-name
///   segments (header name if present, else the path the parent was opened by;
///   empty for a header-less root). This is what determines how far up the
///   namespace root sits.
/// - `parent_file` — the parent's resolved file path (`.als`).
/// - `target` — the `open` target module path (`util/ordering`, `a/b/c`), no
///   extension.
///
/// Algorithm (the reference's `computeModulePath`):
/// 1. Strip the **common leading segments** shared by the parent's declared
///    module name and the target — the shared package prefix.
/// 2. The namespace root is `up(parentFile, slashCount + 1)`, where
///    `slashCount` is the number of `/` in what *remains* of the parent module
///    name: one climb for the parent's own filename, plus one per remaining
///    module segment beyond the first.
/// 3. Resolve the *remaining* target (with `.als`) against that root.
///
/// The declared name is measured by **depth**, not matched to on-disk
/// directory names — so `module hotel` in `book/appendixE/p300-hotel.als`
/// resolves `open util/ordering` relative to `book/appendixE/`, and a model
/// declared `zigbee_join/base/event` but located at `trunk/base/event.als`
/// still finds its sibling `open zigbee_join/base/types` at
/// `trunk/base/types.als` (the shared `zigbee_join/base` prefix cancels, so
/// only the differing tail is re-rooted at the file's own directory). A
/// header-less parent (empty segments) climbs exactly one level: its own
/// directory.
#[must_use]
pub fn compute_module_path(
    parent_module_segs: &[String],
    parent_file: &str,
    target: &str,
) -> String {
    let target_segs: Vec<&str> = target.split('/').filter(|s| !s.is_empty()).collect();

    // Step 1: cancel the common leading package prefix.
    let mut common = 0;
    while common < parent_module_segs.len()
        && common < target_segs.len()
        && parent_module_segs[common] == target_segs[common]
    {
        common += 1;
    }
    let remaining_module = parent_module_segs.len() - common;
    let remaining_target = target_segs[common..].join("/");

    // Step 2: slashCount = slashes in the remaining module name = one less than
    // its segment count (0 when it is empty or a single segment).
    let climb = remaining_module.saturating_sub(1) + 1;
    let root_dir = up(parent_file, climb);

    // Step 3: re-root the remaining target.
    normalize(&format!("{root_dir}/{remaining_target}.als"))
}

/// The `.als`→`.md` sibling of a candidate path (resolution-doc §2.1 step 4),
/// or `None` when the path does not end in `.als`.
#[must_use]
pub fn markdown_sibling(path: &str) -> Option<String> {
    path.strip_suffix(".als").map(|stem| format!("{stem}.md"))
}

/// Whether a string is a single legal Alloy identifier run: non-empty, no
/// path separator, no reserved sigils. Used for the plain-filename auto-alias
/// and the `open$N` basename rewrite (resolution-doc §2.4).
#[must_use]
pub fn is_plain_identifier(name: &str) -> bool {
    !name.is_empty()
        && !name.contains('/')
        && !name.contains('$')
        && !name.contains('@')
        && name
            .chars()
            .next()
            .is_some_and(|c| c.is_alphabetic() || c == '_')
        && name
            .chars()
            .all(|c| c.is_alphanumeric() || c == '_' || c == '\'' || c == '"')
}

#[cfg(test)]
mod tests {
    use super::*;

    fn segs(name: &str) -> Vec<String> {
        name.split('/').map(str::to_owned).collect()
    }

    #[test]
    fn normalize_resolves_dots() {
        assert_eq!(normalize("a/./b/../c"), "a/c");
        assert_eq!(normalize("a//b"), "a/b");
        assert_eq!(normalize("./a"), "a");
        assert_eq!(normalize("a/b/.."), "a");
        assert_eq!(normalize(""), ".");
        assert_eq!(normalize("/x/../y"), "/y");
    }

    #[test]
    fn up_removes_components() {
        assert_eq!(up("root/a/b/c.als", 1), "root/a/b");
        assert_eq!(up("root/a/b/c.als", 3), "root");
        assert_eq!(up("root/a/b/c.als", 0), "root/a/b/c.als");
        assert_eq!(up("a.als", 1), ".");
        assert_eq!(up("/x/y.als", 1), "/x");
    }

    #[test]
    fn compute_path_nested_wellformed() {
        // The corpus's deepest real case: a 3-segment module name under a
        // `book/` root opening a sibling by full module path.
        let got = compute_module_path(
            &segs("chapter6/memory/fixedSizeMemory_H"),
            "root/book/chapter6/memory/fixedSizeMemory_H.als",
            "chapter6/memory/fixedSizeMemory",
        );
        assert_eq!(got, "root/book/chapter6/memory/fixedSizeMemory.als");
    }

    #[test]
    fn compute_path_example_finds_sibling_util() {
        // `module examples/toys/numbering` at models/examples/toys/numbering.als
        // opening `util/relation` strips all three segments back to the models
        // root, landing on models/util/relation.als (disk shadows the stdlib).
        let got = compute_module_path(
            &segs("examples/toys/numbering"),
            "models/examples/toys/numbering.als",
            "util/relation",
        );
        assert_eq!(got, "models/util/relation.als");
    }

    #[test]
    fn compute_path_shallow_module_name_stays_local() {
        // `module hotel` at book/appendixE/p300-hotel.als opening util/ordering:
        // only one segment strips, so the root is the file's own directory and
        // the util target resolves locally (not on disk -> stdlib fallback).
        let got = compute_module_path(
            &segs("hotel"),
            "models/book/appendixE/p300-hotel.als",
            "util/ordering",
        );
        assert_eq!(got, "models/book/appendixE/util/ordering.als");
    }

    #[test]
    fn compute_path_common_prefix_relocated_dir() {
        // A model declared `zigbee_join/base/event` but living at
        // `trunk/base/event.als` opening a sibling `zigbee_join/base/types`:
        // the shared `zigbee_join/base` prefix cancels, so only `types` is
        // re-rooted at the file's own directory (`trunk/base/`).
        let got = compute_module_path(
            &segs("zigbee_join/base/event"),
            "root/trunk/base/event.als",
            "zigbee_join/base/types",
        );
        assert_eq!(got, "root/trunk/base/types.als");
    }

    #[test]
    fn compute_path_headerless_root_is_local() {
        // A header-less root (empty module-name segments) resolves opens
        // relative to its own directory.
        let got = compute_module_path(&[], "models/examples/temporal/leader.als", "util/ordering");
        assert_eq!(got, "models/examples/temporal/util/ordering.als");
    }

    #[test]
    fn markdown_and_plain_ident() {
        assert_eq!(markdown_sibling("a/b.als").as_deref(), Some("a/b.md"));
        assert_eq!(markdown_sibling("a/b.md"), None);
        assert!(is_plain_identifier("ordering"));
        assert!(!is_plain_identifier("util/ordering"));
        assert!(!is_plain_identifier(""));
        assert!(!is_plain_identifier("9x"));
    }
}
