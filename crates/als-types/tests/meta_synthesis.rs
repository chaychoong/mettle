//! The `$` metamodel synthesis probe suite (mt-107 P1, ADR-0024 phase 8).
//!
//! Every assertion here cites a cell of the mt-107 P0 wave
//! (`scratchpad/probe/mt107/`, 140 jar-verified cells): §M1 vocabulary, §M5
//! feature interaction, §M6 trigger negative space. The measured ground truth
//! the shape assertions are read off is `out/m1_base_dump.txt`,
//! `out/m5_02_dump.txt`, `out/m5_05_dump.txt` and `out/m3_09_dump.txt` — the
//! jar's own post-resolution world dumps.
//!
//! P1 synthesizes; it does not expand quantifiers and it retires no leniency
//! site. So these tests assert the *world* the synthesis leaves behind, plus
//! the one resolution fact that is already reachable without expansion: one
//! join hop off a concrete `S$` narrows the four ambiguous relation names to a
//! single candidate.

use als_syntax::ast::{ExprKind, SigMult};
use als_syntax::ArenaId;
use als_types::{
    resolve, ExprChoice, MapLoader, MetaDef, ModuleGraph, NameChoice, ResolvedWorld, SigId, SigKind,
};

/// Loads + resolves `src` as `root.als`, panicking on a reject (every model
/// here is a jar-verified ACCEPT).
fn world(src: &str) -> ResolvedWorld {
    let loader = MapLoader::new().with("root.als", src);
    let graph = match ModuleGraph::load("root.als", &loader) {
        Ok(g) => g,
        Err(e) => panic!("load failed: {e:?}\n--- src ---\n{src}"),
    };
    match resolve(&graph) {
        Ok(r) => r.world,
        Err(e) => panic!("expected ACCEPT, got REJECT: {e:?}\n--- src ---\n{src}"),
    }
}

/// The `SigId` of the sig whose **bare** label is `name`.
fn sig(w: &ResolvedWorld, name: &str) -> SigId {
    w.sigs
        .iter()
        .find(|(_, s)| s.name == name)
        .map_or_else(|| panic!("no sig named {name}"), |(id, _)| id)
}

/// The bare labels of `ids`, in order.
fn labels(w: &ResolvedWorld, ids: &[SigId]) -> Vec<String> {
    ids.iter().map(|&i| w.sigs[i].name.clone()).collect()
}

/// The field labels a sig declares, in declaration order.
fn field_labels(w: &ResolvedWorld, s: SigId) -> Vec<String> {
    w.sigs[s]
        .fields
        .iter()
        .map(|&f| w.fields[f].name.clone())
        .collect()
}

/// The [`MetaDef`] of `sig`'s field named `field`.
fn def(w: &ResolvedWorld, s: SigId, field: &str) -> MetaDef {
    let fid = w.sigs[s]
        .fields
        .iter()
        .copied()
        .find(|&f| w.fields[f].name == field)
        .unwrap_or_else(|| panic!("{} has no field {field}", w.sigs[s].name));
    w.fields[fid]
        .meta_def
        .clone()
        .unwrap_or_else(|| panic!("{}.{field} is not a meta relation", w.sigs[s].name))
}

/// The bare labels a `MetaDef::MetaSigs` unions, in order.
fn union_labels(w: &ResolvedWorld, d: &MetaDef) -> Vec<String> {
    match d {
        MetaDef::MetaSigs(ms) => labels(w, ms),
        other @ (MetaDef::Sig(_) | MetaDef::Field(_)) => {
            panic!("expected a meta-sig union, got {other:?}")
        }
    }
}

/// The mt-107 P0 §M1 base model: an abstract sig with two fields, an extending
/// sig with one, and a fieldless sig.
const M1_BASE: &str = "abstract sig V { f: lone V, g: lone V }\n\
                       sig W extends V { h: lone W }\n\
                       sig Z {}\n\
                       run { some V$ } for 3\n";

// ---- M1: vocabulary shape (`out/m1_base_dump.txt`) ----

/// `sig$` and `field$` are abstract top-level prim sigs; every `S$` is a `one`
/// sig under `sig$` and every `S$f` a `one` sig under `field$`, and they are
/// minted in the reference's synthesis order — `V$, V$f, V$g, W$, W$h, Z$`.
#[test]
fn meta_vocabulary_shape_m1() {
    let w = world(M1_BASE);
    let m = w
        .meta
        .as_ref()
        .expect("the gate fired, so a metamodel exists");

    // `sig$` / `field$`: abstract, META, parent univ.
    for &top in &[m.sig_meta, m.field_meta] {
        let s = &w.sigs[top];
        assert!(s.is_meta && s.is_abstract, "{}: {s:?}", s.name);
        assert_eq!(s.mult, None, "{} is not a multiplicity sig", s.name);
        assert!(
            matches!(s.kind, SigKind::Prim { parent: Some(p) } if p == w.builtins.univ),
            "{} is top-level: {:?}",
            s.name,
            s.kind
        );
    }
    assert_eq!(w.sigs[m.sig_meta].name, "sig$");
    assert_eq!(w.sigs[m.field_meta].name, "field$");
    assert_eq!(w.sigs[m.sig_meta].qualified_name, "this/sig$");

    // Synthesis order: `S$` immediately followed by its own `S$f`s.
    assert_eq!(
        labels(&w, &m.atoms),
        ["V$", "V$f", "V$g", "W$", "W$h", "Z$"]
    );
    assert_eq!(labels(&w, &m.sig_atoms), ["V$", "W$", "Z$"]);
    assert_eq!(labels(&w, &m.field_atoms), ["V$f", "V$g", "W$h"]);

    // Every meta sig is a `one` sig under the right abstract parent.
    for &s in &m.sig_atoms {
        assert_eq!(w.sigs[s].mult, Some(SigMult::One), "{}", w.sigs[s].name);
        assert!(
            matches!(w.sigs[s].kind, SigKind::Prim { parent: Some(p) } if p == m.sig_meta),
            "{} sits under sig$",
            w.sigs[s].name
        );
    }
    for &s in &m.field_atoms {
        assert_eq!(w.sigs[s].mult, Some(SigMult::One), "{}", w.sigs[s].name);
        assert!(
            matches!(w.sigs[s].kind, SigKind::Prim { parent: Some(p) } if p == m.field_meta),
            "{} sits under field$",
            w.sigs[s].name
        );
    }
    assert_eq!(w.sigs[sig(&w, "V$f")].qualified_name, "this/V$f");
}

/// The four relations of an `S$` are declared `value, fields, parent,
/// subfields` — the order `resolveMeta` adds them and the order `writeXML`
/// emits them. An `S$f` declares only `value`.
#[test]
fn four_relations_in_declaration_order_m1() {
    let w = world(M1_BASE);
    for name in ["V$", "W$", "Z$"] {
        assert_eq!(
            field_labels(&w, sig(&w, name)),
            ["value", "fields", "parent", "subfields"],
            "{name}"
        );
    }
    for name in ["V$f", "V$g", "W$h"] {
        assert_eq!(field_labels(&w, sig(&w, name)), ["value"], "{name}");
    }
    // Every one of them is a defined (`=`) field carrying its definition, not a
    // free relation with an AST bound.
    for (_, f) in w.fields.iter() {
        if f.is_meta {
            assert!(f.is_defined && f.meta_def.is_some(), "{f:?}");
        } else {
            assert!(f.meta_def.is_none(), "{f:?}");
        }
    }
}

/// The definitions themselves: `value` is the concrete sig/field relation,
/// `fields` the sig's **own** meta-field sigs, `subfields` those plus every
/// descendant's, `parent` the parent's meta sig or nothing. `#V$.subfields = 3`
/// vs `#V$.fields = 2` is the P0 discriminator (cells `m1_01`/`m1_02`).
#[test]
fn relation_definitions_m1() {
    let w = world(M1_BASE);
    let (v, w_, z) = (sig(&w, "V"), sig(&w, "W"), sig(&w, "Z"));
    let (vm, wm, zm) = (sig(&w, "V$"), sig(&w, "W$"), sig(&w, "Z$"));

    assert_eq!(def(&w, vm, "value"), MetaDef::Sig(v));
    assert_eq!(def(&w, wm, "value"), MetaDef::Sig(w_));
    assert_eq!(def(&w, zm, "value"), MetaDef::Sig(z));

    // `S$f <: value` is the concrete field relation.
    let f = w.sigs[v].fields[0];
    assert_eq!(def(&w, sig(&w, "V$f"), "value"), MetaDef::Field(f));

    // `fields` vs `subfields` — the decisive P0 discriminator.
    assert_eq!(union_labels(&w, &def(&w, vm, "fields")), ["V$f", "V$g"]);
    assert_eq!(
        union_labels(&w, &def(&w, vm, "subfields")),
        ["V$f", "V$g", "W$h"]
    );
    assert_eq!(union_labels(&w, &def(&w, wm, "fields")), ["W$h"]);
    assert_eq!(union_labels(&w, &def(&w, wm, "subfields")), ["W$h"]);

    // `parent`: `W$.parent = V$`, `no V$.parent` (cells `m1_21`, `m1_31`).
    assert_eq!(union_labels(&w, &def(&w, wm, "parent")), ["V$"]);
    assert!(union_labels(&w, &def(&w, vm, "parent")).is_empty());

    // A fieldless sig: `no Z$.fields and no Z$.subfields` (cell `m1_30`).
    assert!(union_labels(&w, &def(&w, zm, "fields")).is_empty());
    assert!(union_labels(&w, &def(&w, zm, "subfields")).is_empty());
}

/// An empty definition types as `{S$ -> univ}`, not `{S$ -> none}` — the
/// reference's `ExprConstant.EMPTYNESS` carries a `univ` right column, which is
/// what makes `Z$ in V$.parent` a well-typed UNSAT rather than a type-disjoint
/// comparison (cell `m1_31`).
#[test]
fn empty_definition_types_against_univ_m1() {
    let w = world(M1_BASE);
    let vm = sig(&w, "V$");
    let parent = w.sigs[vm]
        .fields
        .iter()
        .copied()
        .find(|&f| w.fields[f].name == "parent")
        .expect("V$ declares parent");
    assert_eq!(w.fields[parent].ty.entries.len(), 1);
    assert_eq!(w.fields[parent].ty.entries[0].0, vec![vm, w.builtins.univ]);
}

/// `static$` is an **exact** subset over the static meta sigs in synthesis
/// order; an empty `var$` falls back to a non-exact subset of `univ` plus the
/// `var$fact` emptiness fact — the shape every static model's dump shows.
#[test]
fn static_and_var_membership_m1() {
    let w = world(M1_BASE);
    let m = w.meta.as_ref().expect("metamodel");
    match &w.sigs[m.static_meta].kind {
        SigKind::Subset { parents, exact } => {
            assert!(exact, "static$ is exact when non-empty");
            assert_eq!(
                labels(&w, parents),
                ["V$", "V$f", "V$g", "W$", "W$h", "Z$"],
                "interleaved synthesis order"
            );
        }
        k @ SigKind::Prim { .. } => panic!("static$ is a subset sig, got {k:?}"),
    }
    match &w.sigs[m.var_meta].kind {
        SigKind::Subset { parents, exact } => {
            assert!(!exact, "an empty var$ is not exact");
            assert_eq!(parents, &vec![w.builtins.univ]);
        }
        k @ SigKind::Prim { .. } => panic!("var$ is a subset sig, got {k:?}"),
    }
    let facts: Vec<&str> = m.empty_facts.iter().map(|f| f.name.as_str()).collect();
    assert_eq!(facts, ["var$fact"]);
}

// ---- M5: feature interaction ----

/// A `var` sig's meta sig goes into `var$` and its `value` is `var`; the meta
/// sig itself is not (cell `m5_01`).
#[test]
fn var_sig_family_m5_01() {
    let w = world("var sig A {}\nsig B {}\nrun { some A$ } for 2\n");
    let m = w.meta.as_ref().expect("metamodel");
    let (am, bm) = (sig(&w, "A$"), sig(&w, "B$"));
    assert!(!w.sigs[am].is_var, "the meta sig itself is never var");
    assert_eq!(members(&w, m.var_meta), vec![am]);
    assert_eq!(members(&w, m.static_meta), vec![bm]);
    assert!(field_is_var(&w, am, "value"), "A$.value inherits var");
    assert!(!field_is_var(&w, bm, "value"));
    assert!(m.empty_facts.is_empty(), "both buckets are non-empty");
}

/// SURPRISE 6 — the reference's var-inheritance is inconsistent and mettle
/// copies both halves: `sig B { var s }` buckets `B$s` into `var$` (the
/// **field's** variability) while declaring `B$s.value` **non**-`var` (the
/// **sig's**). Jar-verified verbatim in `out/m5_02_dump.txt`.
#[test]
fn split_var_inheritance_m5_02() {
    let w = world("sig B { var s: lone B }\nrun { some B$ } for 2\n");
    let m = w.meta.as_ref().expect("metamodel");
    let (bm, bsm) = (sig(&w, "B$"), sig(&w, "B$s"));
    assert_eq!(members(&w, m.var_meta), vec![bsm], "bucketed by the field");
    assert_eq!(members(&w, m.static_meta), vec![bm]);
    assert!(
        !field_is_var(&w, bsm, "value"),
        "declared by the sig's variability — the reference's own inconsistency"
    );
    let s = w.sigs[sig(&w, "B")].fields[0];
    assert!(
        w.fields[s].is_var,
        "while the underlying field really is var"
    );
}

/// `enum` members are ordinary sigs, so they mint their own meta family — and
/// the desugaring's silent `open util/ordering` mints one nobody wrote
/// (cell `m5_05`).
#[test]
fn enum_mints_its_own_family_m5_05() {
    let w =
        world("enum Color { Red, Green }\nsig A { c: lone Color }\nrun { some Color$ } for 2\n");
    let m = w.meta.as_ref().expect("metamodel");
    assert_eq!(
        labels(&w, &m.sig_atoms),
        ["Color$", "Red$", "Green$", "A$", "Ord$"]
    );
    assert_eq!(labels(&w, &m.field_atoms), ["A$c", "Ord$First", "Ord$Next"]);
    assert_eq!(
        union_labels(&w, &def(&w, sig(&w, "Red$"), "parent")),
        ["Color$"]
    );
    // The auto-opened ordering family carries its module's alias path.
    assert_eq!(w.sigs[sig(&w, "Ord$")].qualified_name, "ordering/Ord$");
}

/// `util/ordering` mints a meta family per instance, private because `Ord` is
/// (cells `m3_09`, `m5_06`, `m5_07`).
#[test]
fn ordering_mints_a_private_family_m3_09() {
    let w = world("open util/ordering[A] as ao\nsig A { r: lone A }\nrun { some A$ } for 3\n");
    let m = w.meta.as_ref().expect("metamodel");
    assert_eq!(labels(&w, &m.sig_atoms), ["A$", "Ord$"]);
    assert_eq!(labels(&w, &m.field_atoms), ["A$r", "Ord$First", "Ord$Next"]);
    let ord = sig(&w, "Ord$");
    assert_eq!(w.sigs[ord].qualified_name, "ao/Ord$");
    assert!(w.sigs[ord].is_private, "privacy propagates from Ord");
    assert!(w.sigs[sig(&w, "Ord$First")].is_private);
    // The user sig's own family stays public.
    assert!(!w.sigs[sig(&w, "A$")].is_private);
}

/// Field privacy falls back to the sig's, and a private field's meta sig is
/// private without making the owner's family private (cell `m5_08`).
#[test]
fn privacy_propagation_m5_08() {
    let w =
        world("private sig P { q: lone P }\nsig R { private t: lone R }\nrun { some P$ } for 2\n");
    assert!(w.sigs[sig(&w, "P$")].is_private);
    assert!(w.sigs[sig(&w, "P$q")].is_private, "falls back to the sig's");
    assert!(!w.sigs[sig(&w, "R$")].is_private);
    assert!(w.sigs[sig(&w, "R$t")].is_private);
    for f in &w.sigs[sig(&w, "R$")].fields {
        assert!(
            !w.fields[*f].is_private,
            "R$'s own four relations are public"
        );
    }
}

/// Builtins have no meta sigs: `resolveMeta` reflects the *user* sig map only,
/// so `Int$` / `String$` / `univ$` / `none$` name nothing (cells `m5_09a`–`m5_09d`).
#[test]
fn builtins_get_no_meta_sigs_m5_09() {
    let w = world("sig A {}\nrun { some A$ } for 2\n");
    let m = w.meta.as_ref().expect("metamodel");
    assert_eq!(labels(&w, &m.sig_atoms), ["A$"]);
    for banned in ["Int$", "String$", "univ$", "none$", "seq/Int$"] {
        assert!(
            w.sigs.iter().all(|(_, s)| s.name != banned),
            "no meta sig named {banned}"
        );
    }
}

// ---- M6: the trigger's negative space ----

/// A `$` that is only a comment character or a string literal mints nothing
/// (cells `m6_01`, `m6_02`) — and neither does a model with no `$` at all, which is
/// the P1 behavior gate: every non-meta model is untouched.
#[test]
fn trigger_negative_space_m6() {
    for src in [
        "sig A { f: lone A }\nrun {} -- costs $5\n",
        "sig A { f: lone A }\nfact { \"a$b\" = \"a$b\" }\nrun {}\n",
        "sig A { f: lone A }\nrun {}\n",
    ] {
        let w = world(src);
        assert!(w.meta.is_none(), "no metamodel for:\n{src}");
        assert!(w.sigs.iter().all(|(_, s)| !s.is_meta), "{src}");
        assert!(w.fields.iter().all(|(_, f)| !f.is_meta), "{src}");
    }
}

/// A `$` in an **opened** module triggers the synthesis for the whole world,
/// root's own sigs included (cell `m6_08`) — mettle's gate is graph-wide by
/// design (ADR-0024 addendum).
#[test]
fn opened_module_dollar_triggers_the_world_m6_08() {
    let loader = MapLoader::new()
        .with("root.als", "open lib\nsig A {}\nrun {} for 2\n")
        .with("lib.als", "module lib\nsig L {}\nfact { some L$ }\n");
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let w = resolve(&graph).expect("accept").world;
    let m = w.meta.as_ref().expect("the whole world gets a metamodel");
    assert_eq!(labels(&w, &m.sig_atoms), ["A$", "L$"]);
    assert_eq!(
        w.sigs[m.sig_meta].module, graph.root,
        "sig$ lives at the root"
    );
}

/// A user field named `value` or `subfields` coexists with the synthesized ones
/// — `rejectNameClash` (phase 9, which runs *after* synthesis) does not fire,
/// because the meta sigs are pairwise-disjoint one-sigs under an abstract
/// parent (cells `m6_11`, `m6_12`).
#[test]
fn user_field_named_like_a_meta_relation_m6_11() {
    world("sig A { value: lone A }\nrun { some A$ } for 2\n");
    world("sig A { subfields: lone A }\nrun { some A$ } for 2\n");
}

// ---- resolution through the synthesized names ----

/// One join hop off a concrete `S$` narrows the N-way ambiguous `subfields`
/// name to that sig's own field — the shape both corpus rows use
/// (`Vertex$.subfields`, `House$.subfields`) and the reason P0's SURPRISE 1
/// does not block them.
#[test]
fn one_hop_off_a_concrete_meta_sig_narrows() {
    let src =
        "sig V { f: lone V }\nsig W { g: lone W }\nsig Z {}\nrun { some V$.subfields } for 3\n";
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let w = resolve(&graph).expect("accept").world;
    let root = graph.root;
    let ast = graph.files.file(graph.modules[root].file).ast_ref();

    // Three sigs ⇒ three same-named `subfields` fields; without narrowing the
    // name is 3-way ambiguous (P0 SURPRISE 1).
    assert_eq!(
        w.fields
            .iter()
            .filter(|(_, f)| f.name == "subfields")
            .count(),
        3
    );

    let mut found = false;
    for (id, e) in ast.exprs.iter() {
        let ExprKind::Name(qn) = &e.kind else {
            continue;
        };
        if qn.segments.last().map(|s| s.text.as_str()) != Some("subfields") {
            continue;
        }
        found = true;
        match w.choices.get(root, id) {
            Some(ExprChoice::Name(NameChoice::Field { field, .. })) => {
                assert_eq!(
                    w.sigs[w.fields[*field].owner].name, "V$",
                    "narrowed to the receiver's own relation"
                );
            }
            other => panic!("expected a narrowed field choice, got {other:?}"),
        }
    }
    assert!(found, "the model does contain a `subfields` name node");
}

// ---- helpers that need the world ----

/// The members of a subset meta sig, in declaration order.
fn members(w: &ResolvedWorld, subset: SigId) -> Vec<SigId> {
    match &w.sigs[subset].kind {
        SigKind::Subset { parents, .. } => parents.clone(),
        k @ SigKind::Prim { .. } => {
            panic!("{} is not a subset sig: {k:?}", w.sigs[subset].name)
        }
    }
}

/// Whether `sig`'s field named `field` is `var`.
fn field_is_var(w: &ResolvedWorld, s: SigId, field: &str) -> bool {
    w.sigs[s]
        .fields
        .iter()
        .copied()
        .find(|&f| w.fields[f].name == field)
        .map_or_else(
            || panic!("{} has no field {field}", w.sigs[s].name),
            |f| w.fields[f].is_var,
        )
}

/// Keeps `ArenaId` referenced (the `SigId::index` uses above are inside
/// helpers that the compiler can see through).
#[allow(dead_code)]
fn _touch(id: SigId) -> usize {
    id.index()
}
