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

/// Runs `mettle exec <fixture> [args] --eval <expr>…`, returning the raw
/// process output.
fn exec_eval(name: &str, args: &[&str], exprs: &[&str]) -> Output {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_mettle"));
    cmd.arg("exec").arg(fixture(name)).args(args);
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
    let exprs: Vec<&str> = cells.iter().map(|(e, _)| *e).collect();
    let out = exec_eval(name, args, &exprs);
    assert!(
        out.status.success(),
        "`{name}` {args:?} failed\nstderr: {}",
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

// ============================ the interactive loop ============================

/// Feeds `input` to `mettle exec --repl` on stdin and returns its output.
fn repl_session(name: &str, input: &str) -> Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_mettle"))
        .arg("exec")
        .arg(fixture(name))
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
