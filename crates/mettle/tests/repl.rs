//! The mt-061 probe battery, reproduced end-to-end through `mettle exec
//! --eval` / `--repl` (mt-062).
//!
//! Every `E-NN` below is a cell of the pinned contract's §6 probe log
//! (`docs/reference/alloy6-evaluator.md`), each recorded against the reference
//! Alloy 6.2.0 jar. The fixtures under `tests/fixtures/repl/` are the probe's
//! own models with their scopes tightened so the solved instance is pinned by
//! the model rather than by which satisfying assignment the solver reaches
//! first — otherwise the *value* of `B` or `f` would be a property of mettle's
//! SAT search, not of the evaluator.
//!
//! Where the reference's console renders in a different **order** (its `univ`
//! and `Int` come back through an XML round-trip that reshuffles atoms),
//! mettle's live solve order is pinned here instead, per **LEDGER-012** — the
//! sets are equal; only the order differs, deliberately.

use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/repl")
        .join(name)
}

/// A fixture the `exec` suite owns — the trace-rendering models double as
/// per-state evaluation subjects, so they are shared rather than copied.
fn exec_fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/exec")
        .join(name)
}

/// Runs `mettle exec <fixture> [args] --eval <expr>…`, returning the raw
/// process output.
fn exec_eval(name: &str, args: &[&str], exprs: &[&str]) -> Output {
    exec_eval_path(&fixture(name), args, exprs)
}

fn exec_eval_path(path: &Path, args: &[&str], exprs: &[&str]) -> Output {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_mettle"));
    cmd.arg("exec").arg(path).args(args);
    for expr in exprs {
        cmd.arg("--eval").arg(expr);
    }
    cmd.output().expect("failed to spawn mettle")
}

fn stdout(out: &Output) -> String {
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn stderr(out: &Output) -> String {
    String::from_utf8_lossy(&out.stderr).into_owned()
}

/// The `--eval` result lines only: the instance block `exec` always prints
/// first ends at its blank line, and every line after it is one result.
fn results(out: &Output) -> Vec<String> {
    let text = stdout(out);
    let (_, tail) = text.split_once("\n\n").unwrap_or(("", text.as_str()));
    tail.lines().map(str::to_owned).collect()
}

/// Evaluates each expression against `name`'s single command and asserts the
/// rendered result lines, cell by cell.
#[track_caller]
fn assert_cells(name: &str, args: &[&str], cells: &[(&str, &str)]) {
    assert_cells_at(&fixture(name), args, cells);
}

#[track_caller]
fn assert_cells_at(path: &Path, args: &[&str], cells: &[(&str, &str)]) {
    let exprs: Vec<&str> = cells.iter().map(|(e, _)| *e).collect();
    let out = exec_eval_path(path, args, &exprs);
    assert!(
        out.status.success(),
        "`{}` {args:?} failed\nstderr: {}",
        path.display(),
        stderr(&out)
    );
    let got = results(&out);
    let want: Vec<&str> = cells.iter().map(|(_, w)| *w).collect();
    assert_eq!(got, want, "\nstdout was:\n{}", stdout(&out));
}

/// Evaluates one expression expected to be *rejected*, returning stderr.
fn eval_error(name: &str, args: &[&str], expr: &str) -> String {
    let out = exec_eval(name, args, &[expr]);
    assert!(
        !out.status.success(),
        "`{expr}` was expected to fail but succeeded: {}",
        stdout(&out)
    );
    stderr(&out)
}

// ============================ (a) input surface ============================

/// E-01 through E-14: the whole input surface reaching the one grammar slot —
/// atom names, the built-in relations, quantifiers, comprehensions, `let`,
/// cardinality, and both arithmetic call syntaxes.
#[test]
fn input_surface_and_rendering() {
    assert_cells(
        "base.als",
        &[],
        &[
            // E-01 a literal instance atom name is an ordinary global.
            ("A$0", "{A$0}"),
            // E-02 reflexivity control.
            ("A$0 = A$0", "true"),
            // E-03 `univ`. LEDGER-012: mettle's live solve order (sig atoms in
            // declaration order, then ascending ints) — the reference's console
            // renders the same set as `-1..-8, 0..7` after its XML round-trip.
            // This order is exactly what the contract's own live-object
            // reconciliation probe (§3, `LiveEval.java`) reproduces.
            (
                "univ",
                "{A$0, B$0, B$1, B$2, C$0, C$1, C$2, -8, -7, -6, -5, -4, -3, -2, -1, \
                 0, 1, 2, 3, 4, 5, 6, 7}",
            ),
            // E-04 `iden` — pairs in the same atom order as E-03.
            (
                "iden",
                "{A$0->A$0, B$0->B$0, B$1->B$1, B$2->B$2, C$0->C$0, C$1->C$1, C$2->C$2, \
                 -8->-8, -7->-7, -6->-6, -5->-5, -4->-4, -3->-3, -2->-2, -1->-1, 0->0, \
                 1->1, 2->2, 3->3, 4->4, 5->5, 6->6, 7->7}",
            ),
            // E-05 all 16 int atoms (LEDGER-012 again: ascending, not the
            // console's `-1..-8, 0..7`).
            (
                "Int",
                "{-8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7}",
            ),
            // E-06 the empty set.
            ("none", "{}"),
            // E-07 no string atoms in this instance.
            ("String", "{}"),
            // E-08 a multiplicity test is a formula.
            ("some A", "true"),
            // E-09 a quantified formula.
            ("all x: A | x = x", "true"),
            // E-10 a comprehension.
            ("{x: A | some x}", "{A$0}"),
            // E-11 `let`.
            ("let x = A | x", "{A$0}"),
            // E-12 `#` is genuinely `int`-typed: a BARE numeral.
            ("#A", "1"),
            // E-13 `plus[…]` is `Int`-SET-typed: a singleton tuple set, not a
            // bare numeral. The load-bearing distinction of contract §1/§3.
            ("plus[3,4]", "{7}"),
            // E-14 the dot spelling of the same call.
            ("3.plus[4]", "{7}"),
            // E-19 `+` is set union, never arithmetic — the control that makes
            // E-13's reading unambiguous. (Order is LEDGER-012's.)
            ("3 + A", "{A$0, 3}"),
        ],
    );
}

/// E-37 through E-42: relations of each arity render as `{tuple, …}` with `->`
/// inside tuples, and a `seq` is an ordinary index->element binary relation.
#[test]
fn relations_of_every_arity_render_with_arrows() {
    assert_cells(
        "base.als",
        &[],
        &[
            // E-37 a unary relation with several atoms.
            ("B", "{B$0, B$1, B$2}"),
            // E-38 a binary relation.
            ("f", "{B$0->A$0, B$1->A$0, B$2->A$0}"),
            // E-39 a ternary relation.
            (
                "g",
                "{C$0->A$0->B$0, C$0->A$0->B$1, C$0->A$0->B$2, C$1->A$0->B$0, \
                 C$1->A$0->B$1, C$1->A$0->B$2, C$2->A$0->B$0, C$2->A$0->B$1, \
                 C$2->A$0->B$2}",
            ),
        ],
    );
    // E-40/E-41 a string atom renders WITH its quotes.
    assert_cells(
        "str.als",
        &[],
        &[
            ("\"hello\"", "{\"hello\"}"),
            ("A.label", "{\"hello\"}"),
            // E-46: the reference's console puts string atoms *first*; mettle's
            // live order trails them after the ints (LEDGER-012).
            (
                "univ",
                "{A$0, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, \"hello\"}",
            ),
        ],
    );
    // E-42 no special `seq` syntax — just the binary relation.
    assert_cells("seq.als", &[], &[("Holder.xs", "{0->A$0, 1->A$0}")]);
}

/// E-21 / E-23: a model's own pred and fun are callable from the prompt.
#[test]
fn model_preds_and_funs_are_callable() {
    assert_cells(
        "funcs.als",
        &[],
        &[("isEmpty[A]", "false"), ("double[3]", "{6}")],
    );
}

/// E-24: a skolem name (`$<cmd>_<var>`) is a resolvable global too, bound to
/// the relation the solve actually assigned.
#[test]
fn skolem_names_resolve_against_the_instance() {
    assert_cells("skolem.als", &[], &[("$foo_x", "{A$0}")]);
}

/// E-15 through E-18 and E-20: a declaration, a command, garbage tokens, an
/// unknown name and a comment-only line are all rejected. The reference rejects
/// the first four *identically* (its parser simply cannot start a pred-body
/// production with those tokens) and so does mettle — with mettle's own caret
/// diagnostic, not the reference's 38-token list, which is an artifact of its
/// generated parser rather than a fact about Alloy.
#[test]
fn declarations_commands_and_garbage_are_ordinary_parse_errors() {
    for input in ["sig Foo {}", "run {}", "+++"] {
        let err = eval_error("base.als", &[], input);
        assert!(
            err.contains("syntax error") && err.contains("<repl>:1:1"),
            "`{input}` gave: {err}"
        );
    }
    // E-18 an unknown name.
    let err = eval_error("base.als", &[], "NoSuchName");
    assert!(
        err.contains("`NoSuchName` cannot be found"),
        "unknown name gave: {err}"
    );
    // E-20 a comment-only line holds no expression at all.
    let err = eval_error("base.als", &[], "-- just a comment");
    assert!(
        err.contains("does not correspond to an Alloy expression"),
        "comment-only line gave: {err}"
    );
}

/// E-22, E-43, E-44: calls and joins that do not type-check are rejected, each
/// pointing at the input. (The reference's messages are longer; mettle keeps
/// its own diagnostics — only the two messages that state an *evaluator rule*
/// rather than a syntax fact are taken verbatim.)
#[test]
fn type_errors_point_at_the_input() {
    // E-22 a pred called with no arguments.
    let err = eval_error("funcs.als", &[], "isEmpty");
    assert!(
        err.contains("<repl>:1:1") && err.contains("isEmpty"),
        "{err}"
    );
    // E-43 a call whose arguments do not fit.
    let err = eval_error("base.als", &[], "plus[A,3]");
    assert!(err.contains("plus") && err.contains("<repl>:1:1"), "{err}");
    // E-44 an illegal relational join.
    let err = eval_error("base.als", &[], "A[B]");
    assert!(
        err.contains("relational join") && err.contains("<repl>:1:1"),
        "{err}"
    );
}

/// E-49: a string literal the solved command never referenced has no atom in
/// this universe. An *eval-state* error, so it carries the reference's wording.
#[test]
fn a_string_literal_absent_from_the_instance_is_rejected() {
    let err = eval_error("base.als", &[], "\"hello\"");
    assert!(
        err.contains("String literal \"hello\" does not exist in this instance."),
        "{err}"
    );
}

/// Contract §0 step 10: input whose evaluation would need higher-order
/// quantification is refused, in the reference's own words.
#[test]
fn higher_order_quantification_is_refused_verbatim() {
    let err = eval_error("base.als", &[], "some s: set A | no s");
    assert!(
        err.contains("Higher-order quantification is not allowed in the evaluator."),
        "{err}"
    );
}

// ========================= (b) evaluation context =========================

/// E-25 / E-26 (with E-28 / E-29): bitwidth is inherited from the **solved
/// command**, not from any global default. The same two expressions, against
/// the same model's two commands, give different answers — `3+4` fits a 4-bit
/// range and wraps to `-1` in a 3-bit one.
#[test]
fn bitwidth_is_inherited_from_the_solved_command() {
    assert_cells(
        "bitwidth.als",
        &["--command", "0"],
        &[("plus[3,4]", "{7}"), ("sum x: A | 7", "7")],
    );
    assert_cells(
        "bitwidth.als",
        &["--command", "1"],
        &[("plus[3,4]", "{-1}"), ("sum x: A | 7", "-1")],
    );
}

/// E-31 (with E-27/E-32/E-33): overflow in eval position wraps silently, with
/// no marker — and does so identically whichever way the command was solved,
/// because `noOverflow` is a no-op in eval position (contract §2/§7).
#[test]
fn overflow_in_eval_position_wraps_silently() {
    for solve_mode in [&[][..], &["--allow-overflow"][..]] {
        assert_cells("overflow.als", solve_mode, &[("plus[7,7]", "{-2}")]);
    }
}

/// E-34 / E-35: a command with no instance is nothing to evaluate against. The
/// reference never even points its evaluator at one (its instance writer
/// refuses first); mettle can be asked directly, so it says so and exits
/// through `exec`'s normal failure code.
#[test]
fn a_command_with_no_instance_refuses_evaluation() {
    let out = exec_eval("unsat.als", &[], &["A"]);
    assert_eq!(out.status.code(), Some(1), "stdout: {}", stdout(&out));
    assert!(stdout(&out).contains("UNSAT (no instance)"), "{out:?}");
    assert!(
        stderr(&out).contains("no instance, so eval is not allowed"),
        "{}",
        stderr(&out)
    );
}

/// The evaluator attaches to exactly one instance, so a file with several
/// commands and no `--command` is a usage error that names the alternatives.
#[test]
fn several_commands_need_an_explicit_selection() {
    let out = exec_eval("bitwidth.als", &[], &["univ"]);
    assert_eq!(out.status.code(), Some(2));
    let err = stderr(&out);
    assert!(err.contains("this file has 2 commands"), "{err}");
    assert!(err.contains("[0] run Wide"), "{err}");
    assert!(err.contains("[1] run Narrow"), "{err}");
}

// =============== (c) the temporal edge — per-state (mt-068) ===============
//
// `fixtures/repl/trace.als` is mt-064's own probe model, whose facts force the
// whole trace (`alloy6-temporal.md` §(f)/§(h), probe T-13 captured it live from
// the jar: `traceLength=3 loopState=2`):
//
//     state 0: A={}          B={}
//     state 1: A={Counter$0} B={}
//     state 2: A={}          B={Counter$0}   <- the loop state
//
// so every cell below is checkable by hand against the trace, and the ones
// marked T-22/T-23/T-24 are the jar's own captured answers, reproduced jar-free.

/// A `var` relation's value is the value **at the current state** — mt-068's
/// whole point, and probe T-22's `eval("B", state)` column.
#[test]
fn a_var_relation_evaluates_at_the_current_state() {
    let trace = fixture("trace.als");
    // `--state` defaults to 0.
    assert_cells_at(&trace, &[], &[("A", "{}"), ("B", "{}")]);
    assert_cells_at(
        &trace,
        &["--state", "1"],
        &[("A", "{Counter$0}"), ("B", "{}")],
    );
    assert_cells_at(
        &trace,
        &["--state", "2"],
        &[("A", "{}"), ("B", "{Counter$0}")],
    );
    // A rigid relation is the same at every state (statics are re-emitted
    // verbatim per state — §(f)).
    for state in ["0", "1", "2"] {
        assert_cells_at(&trace, &["--state", state], &[("Counter", "{Counter$0}")]);
    }
}

/// T-22/T-23/T-25: a state index is **never an error**. Past the end it wraps
/// through the loop — `((state − l) % (k − l)) + l`, which for this trace
/// (`k=3, l=2`) sends every index `>= 3` to state 2, *not* to `state % 3` —
/// and a negative index clamps to state 0.
#[test]
fn a_state_index_wraps_through_the_loop_and_clamps_at_zero() {
    let trace = fixture("trace.als");
    for state in ["3", "4", "10", "99"] {
        assert_cells_at(
            &trace,
            &["--state", state],
            &[("B", "{Counter$0}"), ("A", "{}")],
        );
    }
    for state in ["-1", "-2", "-5"] {
        assert_cells_at(&trace, &["--state", state], &[("B", "{}"), ("A", "{}")]);
    }
}

/// T-24: every temporal operator is legal evaluator input, evaluated relative
/// to the current state. The state-0 and state-1 columns are the jar's captured
/// answers verbatim; state 2 (the self-looping loop state) extends the same
/// hand-checkable pattern.
#[test]
fn temporal_operators_are_legal_evaluator_input() {
    let trace = fixture("trace.als");
    assert_cells_at(
        &trace,
        &["--state", "0"],
        &[
            ("always no A", "false"),
            ("eventually some A", "true"),
            ("B'", "{}"),
            ("no A until some B", "false"),
            ("historically no B", "true"),
            ("after some B", "false"),
            ("once some A", "false"),
        ],
    );
    assert_cells_at(
        &trace,
        &["--state", "1"],
        &[
            ("always no A", "false"),
            ("eventually some A", "true"),
            ("B'", "{Counter$0}"),
            ("no A until some B", "false"),
            ("historically no B", "true"),
            ("after some B", "true"),
            // A is nonempty at state 1 itself, and `once` includes the present.
            ("once some A", "true"),
        ],
    );
    assert_cells_at(
        &trace,
        &["--state", "2"],
        &[
            // From the loop state the future is state 2 forever.
            ("always no A", "true"),
            ("eventually some A", "false"),
            ("no A until some B", "true"),
            ("after some B", "true"),
            // ...while the past is the honest prefix through states 0 and 1.
            ("historically no B", "false"),
            ("once some A", "true"),
        ],
    );
}

/// `'` is the expression one step later, and the step at the last state follows
/// the **back-loop** (§(h)): on the alternation fixture (`k=2`, looping back to
/// state 0) `A'` at state 1 is `A` at state 0, which is a different value —
/// not the "last state has no successor" edge case it looks like.
#[test]
fn prime_at_the_last_state_wraps_into_the_loop() {
    let alternating = exec_fixture("trace_alt.als");
    assert_cells_at(
        &alternating,
        &["--state", "1"],
        &[("A", "{A$0}"), ("A'", "{}"), ("after no A", "true")],
    );
    assert_cells_at(
        &alternating,
        &["--state", "0"],
        &[("A", "{}"), ("A'", "{A$0}"), ("A''", "{}")],
    );
    // The same rule on a trace whose loop is a self-loop on the last state:
    // priming there stays put.
    assert_cells_at(
        &fixture("trace.als"),
        &["--state", "2"],
        &[("B", "{Counter$0}"), ("B'", "{Counter$0}")],
    );
}

/// **P-068-1** (this bead's own probe, `scratchpad/probe/mt068/NOTES.md`): a
/// state index is a **time index on the infinite trace**, so an index past the
/// end is a later pass through the loop — its present-tense value is the wrapped
/// state and its future is pass-invariant, but its **past** contains the earlier
/// passes. On this fixture the trace loops back to state 0, so state 0 is
/// revisited: `once some A` is false at state 0 and true at state 2, and
/// `before some A` alternates with the index's parity rather than with the
/// state's. Every cell below is the jar's captured answer.
#[test]
fn past_operators_at_a_revisited_state_see_the_real_history() {
    let alternating = exec_fixture("trace_alt.als");
    // (state, `some A`, `once some A`, `historically no A`, `before some A`)
    let jar = [
        (0, "false", "false", "true", "false"),
        (1, "true", "true", "false", "false"),
        (2, "false", "true", "false", "true"),
        (3, "true", "true", "false", "false"),
        (4, "false", "true", "false", "true"),
        // Past pass 1 every deeper pass agrees — the fixpoint the implementation
        // caps at, checked rather than assumed.
        (5, "true", "true", "false", "false"),
        (6, "false", "true", "false", "true"),
        (7, "true", "true", "false", "false"),
        (8, "false", "true", "false", "true"),
    ];
    for (state, present, once, historically, before) in jar {
        assert_cells_at(
            &alternating,
            &["--state", &state.to_string()],
            &[
                ("some A", present),
                ("once some A", once),
                ("historically no A", historically),
                ("before some A", before),
                // Future operators are the same from every pass through a state.
                ("eventually some A", "true"),
                ("always some A", "false"),
            ],
        );
    }
    // A negative index clamps, so it is state 0 in every respect — including
    // having no past at all.
    assert_cells_at(
        &alternating,
        &["--state", "-3"],
        &[("once some A", "false"), ("before some A", "false")],
    );
}

/// The degenerate one-state trace is not a special case anywhere: every index
/// normalizes to 0, `'` follows the self-loop back to the same state, and
/// `before` is still false at the start of time (P-A1/A2).
#[test]
fn a_one_state_trace_evaluates_like_any_other() {
    let single = exec_fixture("temporal.als");
    for state in ["0", "1", "7", "-3"] {
        assert_cells_at(
            &single,
            &["--state", state],
            &[
                ("A", "{}"),
                ("A'", "{}"),
                ("always no A", "true"),
                ("before some A", "false"),
            ],
        );
    }
}

/// A temporal command's skolem is an ordinary evaluator global (E-24) whose
/// value is **rigid** — the same at every state (§(l), probes P-F1/F2) — while
/// the `var` sig it constrains is not. Also covers the seam that makes it work:
/// the REPL binds the relations the *solve* minted, not freshly-lowered ones.
#[test]
fn a_temporal_skolem_is_a_rigid_global() {
    let skolem = fixture("trace_skolem.als");
    assert_cells_at(
        &skolem,
        &["--state", "0"],
        &[("$witness_n", "{P$0}"), ("A", "{}")],
    );
    assert_cells_at(
        &skolem,
        &["--state", "1"],
        &[("$witness_n", "{P$0}"), ("A", "{Q$0}")],
    );
    // ...and the wrap keeps both of them consistent past the end of the trace.
    assert_cells_at(
        &skolem,
        &["--state", "3"],
        &[("$witness_n", "{P$0}"), ("A", "{Q$0}")],
    );
}

/// A temporal `--repl` says what the trace is and where it is standing (users
/// need `k` and the loop target to read a wrapped index), and `:state N` moves —
/// client-side, exactly like the reference GUI's `<`/`>` arrows. Nothing here
/// re-solves or enumerates: mettle ships no trace enumeration, and the surface
/// promises none (§(g) is classification only).
#[test]
fn the_repl_reports_its_trace_and_moves_between_states() {
    let out = repl_session_at(
        &fixture("trace.als"),
        &[],
        "B\n:state 1\nA\n:state 5\nB\n:state -3\n:state\n:q\n",
    );
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    let text = stdout(&out);
    let (_, session) = text.split_once("\n\n").expect("trace block");
    assert_eq!(
        session,
        "trace: 3 states, loop -> state 2; evaluating at state 0 (`:state N` to move)\n\
         > {}\n\
         > evaluating at state 1\n\
         > {Counter$0}\n\
         > evaluating at state 5 (trace state 2, a later pass through the loop)\n\
         > {Counter$0}\n\
         > evaluating at state 0 (-3 clamps to 0)\n\
         > evaluating at state 0\n\
         > ",
        "{text}"
    );
}

/// `--state`/`:state` are about a trace, and a static command has none: the
/// prompt says so rather than pretending state 7 means something.
#[test]
fn the_state_command_is_refused_on_a_static_command() {
    let out = repl_session("base.als", ":state 2\n:q\n");
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    let text = stdout(&out);
    assert!(
        text.contains("this command is not temporal, so its instance has a single state."),
        "{text}"
    );
    // A static session's banner stays empty — nothing to say about a trace.
    assert!(!text.contains("trace:"), "{text}");
}

/// A non-numeric `:state` argument is a usage error at the prompt, not a
/// silently ignored line.
#[test]
fn the_state_command_rejects_a_non_numeric_argument() {
    let out = repl_session_at(&fixture("trace.als"), &[], ":state two\n:q\n");
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    assert!(
        stdout(&out).contains("`:state` expects an integer state index, got `two`."),
        "{}",
        stdout(&out)
    );
}

/// STYLE U4, on the temporal path too: same session, byte-identical output.
#[test]
fn a_temporal_session_is_deterministic() {
    let script = "B\n:state 1\nB'\nalways no A\n:state 9\nA\n:q\n";
    let first = repl_session_at(&fixture("trace.als"), &[], script);
    let second = repl_session_at(&fixture("trace.als"), &[], script);
    assert_eq!(stdout(&first), stdout(&second));
    assert_eq!(stderr(&first), stderr(&second));
}

/// A *static* command's evaluator still refuses temporal operators, typed and
/// with a caret: there is no trace to evaluate `after` against, and answering
/// at "the only state" is not a pinned behavior (unpinned corner, mt-069).
#[test]
fn a_static_command_still_defers_temporal_operators() {
    let err = eval_error("base.als", &[], "after some A");
    assert!(
        err.contains("temporal operators are parsed but not yet solvable") && err.contains("after"),
        "{err}"
    );
}

// ============================ the interactive loop ============================

/// Feeds `input` to `mettle exec --repl` on stdin and returns its output.
fn repl_session(name: &str, input: &str) -> Output {
    repl_session_at(&fixture(name), &[], input)
}

fn repl_session_at(path: &Path, args: &[&str], input: &str) -> Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_mettle"))
        .arg("exec")
        .arg(path)
        .args(args)
        .arg("--repl")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn mettle");
    child
        .stdin
        .take()
        .expect("stdin piped")
        .write_all(input.as_bytes())
        .expect("failed to write stdin");
    child.wait_with_output().expect("failed to wait for mettle")
}

/// The loop prompts with exactly `> `, reprompts silently on blank input
/// (contract §0 step 1), prints one result line per expression, and exits
/// cleanly on `:q`.
#[test]
fn the_loop_prompts_reprompts_and_quits() {
    let out = repl_session("base.als", "A$0\n\n   \n#B\n:q\n");
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    let text = stdout(&out);
    let (_, session) = text.split_once("\n\n").expect("instance block");
    // Two blank inputs consumed two prompts and produced no result lines; the
    // prompt `:q` was typed at stays open, since the user's own Enter already
    // ended that line on a terminal.
    assert_eq!(session, "> {A$0}\n> > > 3\n> ", "{text}");
}

/// EOF ends the session as cleanly as `:q` does.
#[test]
fn eof_ends_the_session() {
    let out = repl_session("base.als", "#B\n");
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    let text = stdout(&out);
    let (_, session) = text.split_once("\n\n").expect("instance block");
    assert_eq!(session, "> 3\n> \n", "{text}");
}

/// STYLE U4: the same input sequence produces byte-identical output, run after
/// run — the REPL evaluates against the same instance the same way every time.
#[test]
fn a_session_is_deterministic() {
    let script = "univ\n#B\nf\nplus[3,4]\nNoSuchName\n:q\n";
    let first = repl_session("base.als", script);
    let second = repl_session("base.als", script);
    assert_eq!(stdout(&first), stdout(&second));
    assert_eq!(stderr(&first), stderr(&second));
}

/// The REPL is additive: asking `exec` to evaluate afterwards does not change
/// the verdict, instance, or diagnostics it prints for the command itself
/// (STYLE D1 — the REPL never perturbs how instances are produced).
#[test]
fn evaluating_leaves_the_command_output_untouched() {
    let plain = exec_eval("base.als", &[], &[]);
    let evaluated = exec_eval("base.als", &[], &["#A"]);
    let plain_text = stdout(&plain);
    assert!(
        stdout(&evaluated).starts_with(&plain_text),
        "instance block changed:\n{}\nvs\n{}",
        plain_text,
        stdout(&evaluated)
    );
    assert_eq!(stderr(&plain), stderr(&evaluated));
}
