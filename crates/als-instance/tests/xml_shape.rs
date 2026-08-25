//! Jar-free **shape goldens** for the instance-XML writer (mt-071).
//!
//! Each case is one of the mt-070 probe fixtures whose reference-jar output is
//! transcribed verbatim in `docs/reference/alloy6-instance-xml.md`; the golden
//! files under `tests/golden/` pin mettle's own bytes for the same model, so a
//! regression in the element order, the lazy touch-order ID scheme, the
//! interleaved fields, the attribute inventory, the `m<i>` macro namespace, the
//! `<types>` shape, or the block count shows up as a diff rather than as a
//! surprise at the Sterling end.
//!
//! **What a golden covers, and what it deliberately does not.** The *shape* is
//! the jar's exactly (compare any golden here with the corresponding
//! `X-NN` transcript in the reference doc: identical element order, identical
//! ID numbering). The *atom names* and *tuple contents* are mettle's own live
//! solve — mettle mints subsig atoms out of the parent's pool where the jar
//! mints fresh ones, and tuple order is mettle's `TupleSet` order (the standing
//! LEDGER-012 posture). Neither is scorecard-visible, and the jar's own reader
//! accepts both (the mt-071 differential).
//!
//! The `<source>` section is stripped from the goldens (every model drags the
//! embedded `util/integer` text in, which would bury the interesting bytes);
//! [`sources_are_written_once_after_every_instance`] pins it separately.
//!
//! Regenerate after a deliberate change with `METTLE_UPDATE_GOLDEN=1 cargo test
//! -p als-instance`.

use std::path::PathBuf;

use als_core::ir::Ir;
use als_core::{
    compute_bounds, compute_universe, lower_command, solve_goal, solve_temporal_command,
    SolveOptions, SolveVerdict, TemporalSolveConfig, TemporalVerdict,
};
use als_instance::{write_instance_xml, XmlRequest, XmlSolution};
use als_types::{is_temporal_model, resolve, MapLoader, ModuleGraph};

/// The path every fixture is loaded at — it reaches the `filename=` attribute
/// and the root `<source filename=>`, so it is part of the golden.
const PATH: &str = "model.als";

/// Solves one command of `source` and returns the whole `<alloy>` document.
fn document(source: &str, command: usize) -> String {
    document_with(&MapLoader::new(), source, command)
}

/// [`document`], with the opened modules the fixture needs already loaded.
fn document_with(loader: &MapLoader, source: &str, command: usize) -> String {
    let graph = ModuleGraph::load_with_source(PATH, source.to_owned(), loader)
        .unwrap_or_else(|e| panic!("fixture failed to load: {e}"));
    let world = resolve(&graph)
        .unwrap_or_else(|e| panic!("fixture failed to resolve: {e}"))
        .world;
    let cmd = &world.commands[command];
    let scoped = compute_universe(&world, &graph, cmd).expect("universe");
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &scoped, &mut ir);
    let opts = SolveOptions::default();

    if is_temporal_model(&world, &graph, cmd) {
        let cfg = TemporalSolveConfig {
            opts,
            primary_var_cap: None,
            self_check: false,
        };
        let verdict =
            solve_temporal_command(&world, &graph, &scoped, &bounds, &mut ir, command, &cfg)
                .expect("temporal solve");
        let TemporalVerdict::Sat(trace) = verdict else {
            panic!("fixture command produced no trace: {verdict:?}");
        };
        let request = XmlRequest {
            world: &world,
            graph: &graph,
            scoped: &scoped,
            bounds: &bounds,
            command,
            filename: PATH,
            opts,
            solution: XmlSolution::Trace { trace: &trace },
        };
        write_instance_xml(&mut ir, &request).expect("write")
    } else {
        let goal =
            lower_command(&world, &graph, &scoped, &bounds, &mut ir, command).expect("lower");
        let verdict = solve_goal(&ir, &scoped, &goal, &bounds, &opts).expect("solve");
        let SolveVerdict::Sat(instance) = verdict else {
            panic!("fixture command produced no instance: {verdict:?}");
        };
        let request = XmlRequest {
            world: &world,
            graph: &graph,
            scoped: &scoped,
            bounds: &bounds,
            command,
            filename: PATH,
            opts,
            solution: XmlSolution::Static {
                instance: &instance,
                goal: &goal,
            },
        };
        write_instance_xml(&mut ir, &request).expect("write")
    }
}

/// The document with its `<source>` tail removed — everything from the first
/// `<source` on, which is bulk module text, not writer shape — and with the
/// workspace version in `builddate=` normalized, so bumping the version off
/// `0.0.0` at the Rung-5 exit gate does not invalidate ten goldens.
/// [`builddate_is_the_version_stamp`] pins the real value instead.
fn instances(document: &str) -> String {
    let trimmed = match document.find("\n<source ") {
        Some(at) => &document[..=at],
        None => document,
    };
    trimmed.replacen(
        concat!("builddate=\"mettle ", env!("CARGO_PKG_VERSION"), "\""),
        "builddate=\"mettle <version>\"",
        1,
    )
}

fn golden_path(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/golden")
        .join(format!("{name}.xml"))
}

/// Compares the instance section of `source`'s solved command against the named
/// golden (and returns it, so a test can assert on individual pins too), or
/// rewrites the golden under `METTLE_UPDATE_GOLDEN=1`.
fn assert_golden(name: &str, source: &str, command: usize) -> String {
    let doc = document(source, command);
    let actual = instances(&doc);
    let path = golden_path(name);
    if std::env::var_os("METTLE_UPDATE_GOLDEN").is_some() {
        std::fs::create_dir_all(path.parent().expect("golden dir")).expect("mkdir");
        std::fs::write(&path, &actual).expect("write golden");
        return actual;
    }
    let expected = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "missing golden {}: {e} (rerun with METTLE_UPDATE_GOLDEN=1)",
            path.display()
        )
    });
    assert_eq!(
        actual, expected,
        "instance XML drifted from golden `{name}`"
    );
    actual
}

// ---------------------------------------------------------------- fixtures

/// X-01: a plain sig / subsig / field model. Pins the whole `<instance>`
/// attribute inventory, the recursive children-before-parent print order, and —
/// the load-bearing one — the lazy touch-order ID numbering that gives `univ`
/// the third-lowest id despite printing last.
const BASIC: &str = "\
sig A {}
sig B extends A {}
sig C { f: B }
run { some C } for 3
";

/// X-02: every sig modifier the writer can print, plus a two-parent subset sig
/// (written outside the `univ` tree, `<type>` children, no `parentID`).
const MODIFIERS: &str = "\
abstract sig Root {}
sig A extends Root {}
sig B extends Root {}
one sig Sing extends Root {}
lone sig Optional extends Root {}
private sig Priv extends Root {}
sig SomeSub in A + B {}
run { some A and some B and some SomeSub } for 3
";

/// X-02b: `enum` desugaring — `abstract enum` parent, one `one sig` per value,
/// and the auto-injected private `ordering/Ord` sig with its private
/// `First`/`Next` fields. Also the first case where `util/ordering`'s own
/// zero-arg funs surface as `m<i>` macro skolems (§6).
const ENUM: &str = "\
enum Color { Red, Green, Blue }
run { some Color } for 3
";

/// X-07: the one builtin with `<atom>` children, and the escaping contract on
/// a user-influenced atom label.
const STRING_ATOM: &str = "\
one sig Holder { s: one String }
fact { Holder.s = \"a<b&c'd\" }
run {} for 3
";

/// X-04: arity-4 tuples (declared arity + 1 for the owner) alongside a field
/// forced empty, which prints `<types>` and no `<tuple>`.
const ARITY3: &str = "\
sig A {}
sig B {}
sig C {
    g: A -> B -> A,
    empty: A -> B
}
fact { no empty }
run { some g } for 3
";

/// X-06: a zero-arg relational `fun` becomes `<skolem ID=\"m0\">`; a zero-arg
/// `pred` (Boolean, no tuple) correctly produces nothing — negative space.
const MACRO_FUN: &str = "\
sig A {}
fun Best: one A { A }
pred trivial { some A }
run { some A } for 3
";

/// X-05: an anonymous `run`'s skolems are bare `$var`.
const SKOLEM_RUN: &str = "\
sig A {}
run { some x: A, y: A | x != y } for 3
";

/// X-05b: a named `check`'s skolems are `$cmd_var`, and `command=` carries the
/// `Check ` prefix.
const SKOLEM_CHECK: &str = "\
sig A {}
assert allSame { all x, y: A | x = y }
check allSame for 3
";

/// X-03's shape without the second module: a `var` sig over a forced 3-state
/// trace — three `<instance>` blocks, `var=\"yes\"`, `mintrace`/`maxtrace` from
/// the resolved `steps` range, `looplength = tracelength - loopState`.
const TEMPORAL: &str = "\
var sig A {}
sig Fixed {}
fact { always (some A => after no A) and always (no A => after some A) }
fact { some A }
run { some Fixed } for 3 but exactly 3 steps
";

/// X-06b, the wave's most load-bearing finding: a reachable zero-arg `fun`
/// whose body nests a past operator makes the physical block count
/// `tracelength + extra*(tracelength - loopState)` — strictly more than
/// `tracelength`, while every block still self-reports the same
/// `tracelength=`/`looplength=`.
const MACRO_PAST_DEPTH: &str = "\
var sig A {}
fact { always (some A => after no A) and always (no A => after some A) }
fact { some A }
fun PastWitness: set A { {x: A | once x in A} }
run { some A } for 3 but exactly 3 steps
";

#[test]
fn basic_sig_field_and_lazy_id_order() {
    let doc = assert_golden("basic", BASIC, 0);
    // The X-01 headline, asserted independently of the golden bytes so a
    // regeneration cannot quietly bless a broken ID scheme: `univ` prints last
    // but is numbered before `String`.
    let univ = doc.find("<sig label=\"univ\" ID=\"2\"").expect("univ id 2");
    let string = doc
        .find("<sig label=\"String\" ID=\"3\"")
        .expect("String id 3");
    assert!(string < univ, "String must print before univ");
    // Fields interleave: `f` sits between `this/C`'s `</sig>` and `univ`'s tag.
    let field = doc.find("<field label=\"f\"").expect("field f");
    assert!(
        field < univ,
        "fields interleave, they are not batched at the end"
    );
}

#[test]
fn sig_modifiers_and_subset_sigs() {
    let doc = assert_golden("modifiers", MODIFIERS, 0);
    // A subset sig is written outside the `univ` recursion, with no `parentID`
    // and one `<type>` child per parent.
    let subset = doc
        .find("<sig label=\"this/SomeSub\"")
        .expect("subset sig present");
    assert!(
        doc.find("<sig label=\"univ\"").expect("univ") < subset,
        "subset sigs follow the whole univ tree"
    );
    let tail = &doc[subset..];
    let end = tail.find("</sig>").expect("subset closes");
    assert!(
        !tail[..end].contains("parentID"),
        "a subset sig has no parentID"
    );
    assert_eq!(
        tail[..end].matches("<type ID=").count(),
        2,
        "one type per parent"
    );
}

#[test]
fn enum_desugars_with_the_injected_ordering_sig() {
    let doc = assert_golden("enum", ENUM, 0);
    assert!(doc.contains("abstract=\"yes\" enum=\"yes\""));
    assert!(doc.contains("<sig label=\"ordering/Ord\""));
    assert!(doc.contains("<field label=\"First\""));
    assert!(doc.contains("<field label=\"Next\""));
    // `util/ordering`'s own zero-arg funs are reachable macros (§6).
    assert!(doc.contains("<skolem label=\"$ordering/first\" ID=\"m0\""));
}

#[test]
fn string_atoms_and_escaping() {
    let doc = assert_golden("string_atom", STRING_ATOM, 0);
    // §8: the atom label is the literal's own quoted spelling, XML-escaped.
    assert!(doc.contains("<atom label=\"&quot;a&lt;b&amp;c&apos;d&quot;\"/>"));
}

#[test]
fn field_arity_and_the_empty_field_shape() {
    let doc = assert_golden("arity3", ARITY3, 0);
    // `g: A -> B -> A` on `C` is four columns wide (declared arity + owner).
    assert!(doc.contains(
        "<types> <type ID=\"6\"/> <type ID=\"4\"/> <type ID=\"5\"/> <type ID=\"4\"/> </types>"
    ));
    // The empty field prints `<types>` and no `<tuple>`.
    let empty = doc.find("<field label=\"empty\"").expect("empty field");
    let tail = &doc[empty..];
    let end = tail.find("</field>").expect("field closes");
    assert!(!tail[..end].contains("<tuple>"));
    assert!(tail[..end].contains("<types>"));
}

#[test]
fn macro_skolems_use_their_own_namespace() {
    let doc = assert_golden("macro_fun", MACRO_FUN, 0);
    assert!(doc.contains("<skolem label=\"$this/Best\" ID=\"m0\""));
    // Negative space: a zero-arg *pred* is Boolean, so it gets no entry.
    assert!(!doc.contains("trivial"));
}

#[test]
fn anonymous_command_skolem_naming() {
    let doc = assert_golden("skolem_run", SKOLEM_RUN, 0);
    assert!(doc.contains("<skolem label=\"$x\""));
    assert!(doc.contains("<skolem label=\"$y\""));
    assert!(doc.contains("command=\"Run run$1 for 3\""));
}

#[test]
fn named_command_skolem_naming() {
    let doc = assert_golden("skolem_check", SKOLEM_CHECK, 0);
    assert!(doc.contains("<skolem label=\"$allSame_x\""));
    assert!(doc.contains("<skolem label=\"$allSame_y\""));
    assert!(doc.contains("command=\"Check allSame for 3\""));
}

/// §1.2: a per-sig scope clause in `command=` names the sig by its **bare**
/// declared name, whatever module it came from and however the scope target was
/// written. Jar-measured on all three shapes (mt-132,
/// `scratchpad/probe/mt132/Cmd1..Cmd3`): `2 P`, not `2 this/P`; `2 S`, not
/// `2 sub/S`; `1 T`, not `1 dm/T`. The reference doc reads the bytecode's
/// `sig.label` as the qualified label; the live jar disagrees.
#[test]
fn a_scope_clause_names_its_sig_bare() {
    let loader = MapLoader::new().with("sub.als", "module sub\nsig S {}\n");
    let doc = document_with(
        &loader,
        "\
open sub

sig P {}
run {} for 3 but exactly 1 this/P, 2 sub/S
",
        0,
    );
    assert!(
        doc.contains("command=\"Run run$1 for 3 but exactly 1 P, 2 S\""),
        "scope clauses name sigs bare: {doc}"
    );
}

#[test]
fn temporal_trace_blocks_and_loop_encoding() {
    let doc = assert_golden("temporal", TEMPORAL, 0);
    assert_eq!(doc.matches("<instance ").count(), 3, "one block per state");
    assert!(doc.contains("var=\"yes\""));
    assert!(doc.contains("mintrace=\"3\" maxtrace=\"3\""));
    assert!(doc.contains("tracelength=\"3\" looplength=\""));
    assert!(doc.contains("command=\"Run run$1 for 3 but 3..3 steps\""));
}

#[test]
fn a_past_depth_macro_adds_instance_blocks() {
    let doc = assert_golden("macro_past_depth", MACRO_PAST_DEPTH, 0);
    // §7: `3 + 1*(3 - 1) = 5` physical blocks, each still self-reporting
    // `tracelength="3"`. This is exactly the count the reference jar emits for
    // the same fixture (probe X-06b).
    assert_eq!(doc.matches("<instance ").count(), 5);
    assert_eq!(doc.matches("tracelength=\"3\"").count(), 5);
    assert_eq!(doc.matches("looplength=\"2\"").count(), 5);
    assert_eq!(
        doc.matches("ID=\"m0\"").count(),
        5,
        "one macro skolem per block"
    );
}

// -------------------------------------------------------- the source tail

/// §9: `<source>` entries come once per loaded file, **after** every
/// `<instance>` block and immediately before `</alloy>` — never interleaved,
/// never duplicated per block — with the module text XML-escaped.
#[test]
fn sources_are_written_once_after_every_instance() {
    let source = "\
// a comment with < > & ' \" in it
sig A {}
run { some A } for 3
";
    let doc = document(source, 0);
    let first_source = doc.find("\n<source ").expect("a source element");
    assert!(
        doc.rfind("</instance>").expect("an instance") < first_source,
        "sources follow every instance block"
    );
    assert!(doc.ends_with("\"/>\n\n</alloy>\n"));
    // Exactly one entry per loaded file: the model plus the always-loaded
    // `util/integer` (§9's surprise, which mettle reproduces).
    assert_eq!(doc.matches("\n<source filename=").count(), 2);
    assert!(doc.contains("content=\"// a comment with &lt; &gt; &amp; &apos; &quot; in it&#x000a;"));
}

/// §1/§12: `builddate=` is a **fixed** stamp, never a clock. The reference
/// writes its jar's build-time string; mettle writes its own version, so two
/// runs of the same binary are byte-identical.
#[test]
fn builddate_is_the_version_stamp() {
    let doc = document(BASIC, 0);
    assert!(doc.starts_with(concat!(
        "<alloy builddate=\"mettle ",
        env!("CARGO_PKG_VERSION"),
        "\">\n\n"
    )));
}

/// §12: writing the same solved artifacts twice is byte-identical, and so is a
/// second independent solve of the same command.
#[test]
fn output_is_deterministic() {
    assert_eq!(document(BASIC, 0), document(BASIC, 0));
    assert_eq!(document(TEMPORAL, 0), document(TEMPORAL, 0));
}
