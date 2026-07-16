//! The embedded standard-library fallback — the **last** resolver of an
//! `open` target (resolution-doc §2.1 step 5). A `util/*` module that is not
//! found on disk next to the user's model is served from this table; a
//! same-named file on disk *shadows* it.
//!
//! The table holds mettle's **clean-room** `util/*.als` modules (mt-015,
//! ADR-0006: written fresh from the resolution-doc §7 interface appendix,
//! never transcribed from upstream text). Do not repopulate this table from
//! `corpus/` copies or any upstream source.
//!
//! The reference's fallback serves everything the jar embeds under `models/`
//! (including book/example models); mettle deliberately embeds only `util/*`
//! — a model `open`ing a non-util jar-embedded module is a documented gap
//! (LIMITATIONS) until a real model needs it.

/// Embedded stdlib modules, keyed by `open` **target path** (`"util/ordering"`,
/// no extension), mapped to source text.
pub static MODULES: &[(&str, &str)] = &[
    ("util/boolean", include_str!("../stdlib/util/boolean.als")),
    ("util/graph", include_str!("../stdlib/util/graph.als")),
    ("util/integer", include_str!("../stdlib/util/integer.als")),
    ("util/natural", include_str!("../stdlib/util/natural.als")),
    ("util/ordering", include_str!("../stdlib/util/ordering.als")),
    ("util/relation", include_str!("../stdlib/util/relation.als")),
    ("util/seqrel", include_str!("../stdlib/util/seqrel.als")),
    ("util/sequence", include_str!("../stdlib/util/sequence.als")),
    ("util/sequniv", include_str!("../stdlib/util/sequniv.als")),
    ("util/ternary", include_str!("../stdlib/util/ternary.als")),
    ("util/time", include_str!("../stdlib/util/time.als")),
];

/// Looks up an embedded stdlib module's source by its `open` target path.
///
/// Deterministic: the table is a fixed slice searched linearly, never a hash
/// map (STYLE D2).
#[must_use]
pub fn source_for(target: &str) -> Option<&'static str> {
    MODULES
        .iter()
        .find(|(name, _)| *name == target)
        .map(|(_, source)| *source)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn table_holds_all_eleven_util_modules() {
        assert_eq!(MODULES.len(), 11);
        // Sorted by key: linear search stays deterministic and the table
        // reads as a manifest.
        assert!(MODULES.windows(2).all(|w| w[0].0 < w[1].0));
        assert!(source_for("util/ordering").is_some_and(|s| !s.is_empty()));
        assert_eq!(source_for("util/nonexistent"), None);
    }
}
