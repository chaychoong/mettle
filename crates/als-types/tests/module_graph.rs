//! Module-graph fixtures over the injected [`MapLoader`] — every rule in
//! resolution-doc §0–§2 the mt-017 layer implements, exercised without a
//! filesystem (STYLE U1/U5). Resolution-doc §9 explicitly asks for the nested
//! `computeModulePath` fixtures and the parametric-identity / alias / private
//! probes (24/25/26/27/31/64) that follow.

use als_types::{MapLoader, ModuleGraph, ResolveError};

/// Loads a graph from a set of `(path, source)` modules, rooted at `root`.
fn load(root: &str, modules: &[(&str, &str)]) -> Result<ModuleGraph, ResolveError> {
    let mut loader = MapLoader::new();
    for (path, source) in modules {
        loader.insert(path, source);
    }
    ModuleGraph::load(root, &loader)
}

#[test]
fn nested_opens_walk_compute_module_path() {
    // The corpus's real 3-deep case: a `book/` namespace root, each module
    // opening the next by full module path. computeModulePath must strip all
    // three declared segments back to `book/` at every hop.
    let g = load(
        "book/chapter6/memory/checkFixedSize.als",
        &[
            (
                "book/chapter6/memory/checkFixedSize.als",
                "module chapter6/memory/checkFixedSize [Addr, Data]\n\
                 open chapter6/memory/fixedSizeMemory_H [Addr, Data] as fmemory\n",
            ),
            (
                "book/chapter6/memory/fixedSizeMemory_H.als",
                "module chapter6/memory/fixedSizeMemory_H [Addr, Data]\n\
                 open chapter6/memory/fixedSizeMemory [Addr, Data] as memory\n",
            ),
            (
                "book/chapter6/memory/fixedSizeMemory.als",
                "module chapter6/memory/fixedSizeMemory [Addr, Data]\n",
            ),
        ],
    )
    .expect("nested opens resolve");

    // root + H + base = 3 instances, 3 files.
    assert_eq!(g.modules.len(), 3);
    assert_eq!(g.files.len(), 3);
    // The chain of aliases: root --fmemory--> H --memory--> base.
    let h = g
        .follow_alias(g.root, "fmemory", g.root)
        .expect("fmemory hop");
    let base = g.follow_alias(h, "memory", g.root).expect("memory hop");
    assert_ne!(h, base);
}

#[test]
fn example_module_finds_util_sibling_on_disk() {
    // `module examples/toys/numbering` strips three segments to the models
    // root, so `open util/relation` lands on models/util/relation.als — the
    // "disk shadows the embedded stdlib" contract (resolution-doc §2.1).
    let g = load(
        "models/examples/toys/numbering.als",
        &[
            (
                "models/examples/toys/numbering.als",
                "module examples/toys/numbering\nopen util/relation as rel\n",
            ),
            ("models/util/relation.als", "module util/relation\n"),
        ],
    )
    .expect("util sibling resolves on disk");
    assert_eq!(g.modules.len(), 2);
    assert!(g.follow_alias(g.root, "rel", g.root).is_some());
}

#[test]
fn circular_import_rejected_at_load() {
    let err = load(
        "a.als",
        &[
            ("a.als", "module a\nopen b\n"),
            ("b.als", "module b\nopen a\n"),
        ],
    )
    .unwrap_err();
    assert!(
        matches!(err, ResolveError::CircularImport { .. }),
        "got {err:?}"
    );
}

#[test]
fn self_cycle_rejected() {
    let err = load("a.als", &[("a.als", "module a\nopen a\n")]).unwrap_err();
    assert!(
        matches!(err, ResolveError::CircularImport { .. }),
        "got {err:?}"
    );
}

#[test]
fn identical_parametric_opens_merge_probe_24() {
    // Two `open ordering[A]` are one *instance* (same file + same args merge,
    // probe 24) — not a duplicate-alias clash. Without an explicit `as`, each
    // gets its own placeholder-derived alias (`ordering`, then `open$1` since
    // the basename is taken), both pointing at the single merged instance,
    // exactly as the reference keeps them.
    let g = load(
        "root.als",
        &[
            ("root.als", "open ordering[A]\nopen ordering[A]\nsig A {}\n"),
            ("ordering.als", "module ordering[exactly elem]\n"),
        ],
    )
    .expect("identical re-opens allowed");
    assert_eq!(g.modules.len(), 2, "root + one merged ordering instance");
    let edges = &g.modules[g.root].opens;
    assert_eq!(edges.len(), 2, "both opens kept");
    assert_eq!(
        edges[0].target, edges[1].target,
        "both point at the merged instance"
    );
}

#[test]
fn identical_aliased_reopen_is_deduped_probe_seq() {
    // The `util/sequniv as seq` case: same alias + same (file, args) is a
    // silently-allowed re-open, collapsed to one edge, never a clash.
    let g = load(
        "root.als",
        &[
            ("root.als", "open sequniv as sq\nopen sequniv as sq\n"),
            ("sequniv.als", "module sequniv\n"),
        ],
    )
    .expect("identical aliased re-open allowed");
    assert_eq!(
        g.modules[g.root].opens.len(),
        1,
        "identical re-open deduped"
    );
}

#[test]
fn distinct_parametric_args_are_distinct_instances_probe_25() {
    let g = load(
        "root.als",
        &[
            (
                "root.als",
                "open ordering[A] as oa\nopen ordering[B] as ob\nsig A {}\nsig B {}\n",
            ),
            ("ordering.als", "module ordering[exactly elem]\n"),
        ],
    )
    .expect("distinct args, distinct instances");
    assert_eq!(g.modules.len(), 3, "root + ordering[A] + ordering[B]");
    let oa = g.follow_alias(g.root, "oa", g.root).unwrap();
    let ob = g.follow_alias(g.root, "ob", g.root).unwrap();
    assert_ne!(oa, ob);
    // Same file, different instances.
    assert_eq!(g.modules[oa].file, g.modules[ob].file);
}

#[test]
fn duplicate_alias_two_modules_rejected_probe_26() {
    let err = load(
        "root.als",
        &[
            (
                "root.als",
                "open ordering[A] as x\nopen other[A] as x\nsig A {}\n",
            ),
            ("ordering.als", "module ordering[exactly elem]\n"),
            ("other.als", "module other[exactly elem]\n"),
        ],
    )
    .unwrap_err();
    match err {
        ResolveError::DuplicateAlias { alias, .. } => assert_eq!(alias, "x"),
        other => panic!("expected DuplicateAlias, got {other:?}"),
    }
}

#[test]
fn auto_alias_is_target_basename() {
    // `open util/ordering[Color]` (no `as`) auto-aliases to `ordering`, not
    // `Color/…` (resolution-doc §2.4, probes 20/21).
    let g = load(
        "root.als",
        &[
            ("root.als", "open util/ordering[Color]\nsig Color {}\n"),
            ("util/ordering.als", "module util/ordering[exactly elem]\n"),
        ],
    )
    .expect("auto-alias resolves");
    assert!(g.follow_alias(g.root, "ordering", g.root).is_some());
    assert!(g.follow_alias(g.root, "Color", g.root).is_none());
}

#[test]
fn plain_filename_no_arg_auto_alias() {
    let g = load(
        "root.als",
        &[
            ("root.als", "open helper\n"),
            ("helper.als", "module helper\n"),
        ],
    )
    .expect("plain open resolves");
    assert!(g.follow_alias(g.root, "helper", g.root).is_some());
}

#[test]
fn private_open_blocks_foreign_qualified_hop() {
    let g = load(
        "root.als",
        &[
            ("root.als", "private open sub as s\nopen sib\n"),
            ("sub.als", "module sub\n"),
            ("sib.als", "module sib\n"),
        ],
    )
    .expect("private open loads");
    let sub = g
        .follow_alias(g.root, "s", g.root)
        .expect("owner sees private open");
    let sib = g.follow_alias(g.root, "sib", g.root).unwrap();
    // A foreign querying module cannot hop the private open.
    assert_eq!(
        g.follow_alias(g.root, "s", sib),
        None,
        "private blocks foreign hop"
    );
    // walk_prefix bottoms out early for the foreign querier.
    let (land, consumed) = g.walk_prefix(g.root, &["s", "first"], sib);
    assert_eq!((land, consumed), (g.root, 0));
    // The owner walks through and consumes the alias segment.
    let (land, consumed) = g.walk_prefix(g.root, &["s", "first"], g.root);
    assert_eq!((land, consumed), (sub, 1));
}

#[test]
fn markdown_literate_fallback() {
    // No `.als` on disk, only the `.md` sibling — resolution-doc §2.1 step 4.
    let g = load(
        "root.als",
        &[("root.als", "open lit\n"), ("lit.md", "module lit\n")],
    )
    .expect(".md fallback resolves");
    assert!(g.follow_alias(g.root, "lit", g.root).is_some());
}

#[test]
fn missing_module_file_reported() {
    let err = load("root.als", &[("root.als", "open ghost\n")]).unwrap_err();
    match err {
        ResolveError::ModuleFileNotFound { target, .. } => assert_eq!(target, "ghost"),
        other => panic!("expected ModuleFileNotFound, got {other:?}"),
    }
}

#[test]
fn open_arg_count_mismatch_probe_31() {
    // `ordering` needs one param; opening it with none is the probe-31 reject.
    let err = load(
        "root.als",
        &[
            ("root.als", "open ordering\n"),
            ("ordering.als", "module ordering[exactly elem]\n"),
        ],
    )
    .unwrap_err();
    match err {
        ResolveError::OpenArgCount {
            expected, found, ..
        } => {
            assert_eq!((expected, found), (1, 0));
        }
        other => panic!("expected OpenArgCount, got {other:?}"),
    }
}

#[test]
fn none_as_open_arg_probe_64() {
    let err = load(
        "root.als",
        &[
            ("root.als", "open ordering[none]\n"),
            ("ordering.als", "module ordering[exactly elem]\n"),
        ],
    )
    .unwrap_err();
    assert!(
        matches!(err, ResolveError::NoneAsOpenArg { .. }),
        "got {err:?}"
    );
}

#[test]
fn parameter_substitution_grounds_through_opener() {
    // root opens mid[Concrete]; mid opens leaf[elem] where `elem` is mid's own
    // parameter — it must ground to `Concrete`, so two such chains with the
    // same concrete arg merge to one leaf instance.
    let g = load(
        "root.als",
        &[
            (
                "root.als",
                "open mid[Concrete] as m1\nopen mid[Concrete] as m2\nsig Concrete {}\n",
            ),
            ("mid.als", "module mid[exactly elem]\nopen leaf[elem]\n"),
            ("leaf.als", "module leaf[exactly x]\n"),
        ],
    )
    .expect("parameter substitution resolves");
    // root + one mid (m1/m2 identical → merged) + one leaf.
    assert_eq!(g.modules.len(), 3);
    let mid = g.follow_alias(g.root, "m1", g.root).unwrap();
    let leaf = g.follow_alias(mid, "leaf", g.root).unwrap();
    // leaf's parameter is bound to the grounded concrete sig, not `elem`.
    assert_eq!(g.modules[leaf].params.len(), 1);
    assert_eq!(
        g.modules[leaf].params[0].arg.segments,
        vec!["Concrete".to_owned()]
    );
}

#[test]
fn load_is_deterministic() {
    let modules: &[(&str, &str)] = &[
        (
            "root.als",
            "open ordering[A] as oa\nopen ordering[B] as ob\nsig A {}\nsig B {}\n",
        ),
        ("ordering.als", "module ordering[exactly elem]\n"),
    ];
    let a = load("root.als", modules).unwrap();
    let b = load("root.als", modules).unwrap();
    assert_eq!(a.modules.len(), b.modules.len());
    // Instance arena is allocation-ordered; the two runs must agree edge-for-edge.
    assert_eq!(a.modules[a.root].opens, b.modules[b.root].opens);
}

#[test]
fn seen_dollar_gate() {
    let plain = load("root.als", &[("root.als", "sig A {}\n")]).unwrap();
    assert!(!plain.seen_dollar);
    let meta = load("root.als", &[("root.als", "fact { some sig$ }\n")]).unwrap();
    assert!(meta.seen_dollar, "a `sig$` reference sets the meta gate");
}
