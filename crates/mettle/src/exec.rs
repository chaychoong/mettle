//! `mettle exec` (mt-036) — the Rung-3 human-testable build: execute every
//! `run`/`check` command of a model's root module end to end (`compute_universe`
//! → `compute_bounds` → `lower_command` → `solve_goal`) and print each verdict,
//! with the SAT instance / counterexample when there is one.
//!
//! This module renders (STYLE E3: diagnostics live only in the `mettle`
//! crate) but never re-derives pipeline logic — every phase is one call into
//! `als-core`/`als-types`, mirroring `als-core/tests/solve_corpus.rs`'s
//! canonical end-to-end flow. A typed [`als_core::TranslateError`] (temporal,
//! `String`, higher-order, or any other Rung-3 gap) is never hidden: it prints
//! as `CANNOT EXECUTE: <message>` and fails the run, exactly like an honest
//! defer should (STYLE E5 — never a wrong verdict).

use std::fmt::Write as _;
use std::process::ExitCode;

use als_core::ir::Ir;
use als_core::solve::Instance;
use als_core::{
    compute_bounds, compute_universe, lower_command, solve_goal, BoundsResult, LoweredGoal,
    ScopedUniverse, SolveOptions, SolveVerdict,
};
use als_syntax::ast::{CmdKind, Expect, ExprId, Para, ParaName};
use als_types::{
    resolve_session, CmdTargetResolved, FilesystemLoader, ModuleGraph, ModuleId, ResolvedCommand,
    ResolvedSession, ResolvedWorld,
};

use crate::repl::{self, ReplContext, SolvedCommand};

/// Parsed `mettle exec` invocation, or a bare help request.
enum ParsedArgs<'a> {
    /// `-h`/`--help` — usage already printed; caller exits 0.
    Help,
    Run {
        path: &'a str,
        command_sel: Option<&'a str>,
        opts: SolveOptions,
        /// `--eval <EXPR>`, in the order written.
        eval: Vec<&'a str>,
        /// `--repl`.
        repl: bool,
    },
}

/// `mettle exec <file.als> [--command <sel>] [--allow-overflow] [--conflicts N]
/// [--encode-budget N]` — hand-rolled arg parsing (no clap), the same idiom
/// `run_parse`/`run_check` use. Unlike those, several options take a value, so
/// this loop walks `args` by index rather than a plain `for`.
fn parse_args(args: &[String]) -> Result<ParsedArgs<'_>, ExitCode> {
    let mut path: Option<&str> = None;
    let mut command_sel: Option<&str> = None;
    let mut allow_overflow = false;
    let mut conflicts: Option<u64> = None;
    let mut encode_budget: Option<u64> = None;
    let mut eval: Vec<&str> = Vec::new();
    let mut repl = false;

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "-h" | "--help" => {
                crate::print_usage();
                return Ok(ParsedArgs::Help);
            }
            "--allow-overflow" => allow_overflow = true,
            "--repl" => repl = true,
            "--eval" => {
                i += 1;
                let Some(v) = args.get(i) else {
                    eprintln!("mettle exec: --eval requires an expression");
                    crate::print_usage();
                    return Err(ExitCode::from(2));
                };
                eval.push(v.as_str());
            }
            "--command" => {
                i += 1;
                let Some(v) = args.get(i) else {
                    eprintln!("mettle exec: --command requires a value");
                    crate::print_usage();
                    return Err(ExitCode::from(2));
                };
                command_sel = Some(v.as_str());
            }
            "--conflicts" => {
                i += 1;
                let Some(v) = args.get(i) else {
                    eprintln!("mettle exec: --conflicts requires a value");
                    crate::print_usage();
                    return Err(ExitCode::from(2));
                };
                let Ok(n) = v.parse::<u64>() else {
                    eprintln!("mettle exec: --conflicts expects a non-negative integer, got `{v}`");
                    return Err(ExitCode::from(2));
                };
                conflicts = Some(n);
            }
            "--encode-budget" => {
                i += 1;
                let Some(v) = args.get(i) else {
                    eprintln!("mettle exec: --encode-budget requires a value");
                    crate::print_usage();
                    return Err(ExitCode::from(2));
                };
                let Ok(n) = v.parse::<u64>() else {
                    eprintln!(
                        "mettle exec: --encode-budget expects a non-negative integer, got `{v}`"
                    );
                    return Err(ExitCode::from(2));
                };
                encode_budget = Some(n);
            }
            other if other.starts_with('-') => {
                eprintln!("mettle exec: unknown option `{other}`");
                crate::print_usage();
                return Err(ExitCode::from(2));
            }
            other => {
                if path.replace(other).is_some() {
                    eprintln!("mettle exec: expected exactly one input file");
                    crate::print_usage();
                    return Err(ExitCode::from(2));
                }
            }
        }
        i += 1;
    }

    let Some(path) = path else {
        eprintln!("mettle exec: missing <file.als>");
        crate::print_usage();
        return Err(ExitCode::from(2));
    };

    Ok(ParsedArgs::Run {
        path,
        command_sel,
        opts: SolveOptions {
            allow_overflow,
            conflict_budget: conflicts,
            encode_budget,
            ..SolveOptions::default()
        },
        eval,
        repl,
    })
}

pub(crate) fn run_exec(args: &[String]) -> Result<(), ExitCode> {
    let (path, command_sel, opts, eval, repl) = match parse_args(args)? {
        ParsedArgs::Help => return Ok(()),
        ParsedArgs::Run {
            path,
            command_sel,
            opts,
            eval,
            repl,
        } => (path, command_sel, opts, eval, repl),
    };

    let graph = load(path)?;
    let session = resolve_graph(&graph)?;
    let world = session.world();

    // Only root-module commands execute (opened-module commands are never
    // executed, matching the jar) — `(world index, command)` pairs, source
    // order; their position in this vec is the display/`--command` index.
    let root_file = graph.modules[graph.root].file;
    let root_cmds: Vec<(usize, &ResolvedCommand)> = world
        .commands
        .iter()
        .enumerate()
        .filter(|(_, c)| c.span.file == root_file)
        .collect();

    let selected: Vec<usize> = match command_sel {
        None => (0..root_cmds.len()).collect(),
        Some(sel) => match select_command(world, &graph, &root_cmds, sel) {
            Ok(pos) => vec![pos],
            Err(msg) => {
                eprintln!("mettle exec: {msg}");
                eprintln!("available commands:");
                for (pos, (_, cmd)) in root_cmds.iter().enumerate() {
                    eprintln!("  {}", command_header(world, &graph, pos, cmd));
                }
                return Err(ExitCode::from(2));
            }
        },
    };

    if repl || !eval.is_empty() {
        return run_evaluator(&session, &graph, &root_cmds, &selected, &opts, &eval, repl);
    }

    let mut out = String::new();
    let mut any_failure = false;
    for &pos in &selected {
        let (idx, cmd) = root_cmds[pos];
        let failed = run_one_command(world, &graph, pos, idx, cmd, &opts, &mut out);
        any_failure |= failed;
    }

    crate::write_stdout(out)?;
    if any_failure {
        Err(ExitCode::from(1))
    } else {
        Ok(())
    }
}

/// `--repl` / `--eval` (mt-062): solve **one** command, print its verdict and
/// instance exactly as a plain run would, then evaluate against that instance.
///
/// Attaching to exactly one command is the whole point — the evaluator answers
/// questions *about an instance*, and a file with several commands has several.
/// Any command that yields an instance works, a `check`'s counterexample
/// included.
#[allow(
    clippy::too_many_arguments,
    reason = "one call site; every argument is already-parsed state that would \
              only be re-bundled into a single-use struct"
)]
fn run_evaluator(
    session: &ResolvedSession<'_>,
    graph: &ModuleGraph,
    root_cmds: &[(usize, &ResolvedCommand)],
    selected: &[usize],
    opts: &SolveOptions,
    eval: &[&str],
    repl: bool,
) -> Result<(), ExitCode> {
    let world = session.world();
    let [pos] = selected else {
        eprintln!(
            "mettle exec: --repl/--eval evaluate against one command's instance, \
             but this file has {} commands",
            root_cmds.len()
        );
        eprintln!("select one with `--command <index|label|target>`:");
        for (pos, (_, cmd)) in root_cmds.iter().enumerate() {
            eprintln!("  {}", command_header(world, graph, pos, cmd));
        }
        return Err(ExitCode::from(2));
    };
    let (idx, cmd) = root_cmds[*pos];

    let mut out = String::new();
    let _ = writeln!(out, "{}", command_header(world, graph, *pos, cmd));
    let run = match run_pipeline(world, graph, cmd, idx, opts) {
        Ok(run) => run,
        Err(e) => {
            let _ = writeln!(out, "CANNOT EXECUTE: {e}\n");
            crate::write_stdout(out)?;
            return Err(ExitCode::from(1));
        }
    };
    let failed = render_verdict(cmd, &run, &mut out);
    crate::write_stdout(out)?;

    let SolveVerdict::Sat(instance) = run.verdict else {
        // The reference never even points its evaluator at a command with no
        // instance (its writer refuses first); mettle can be asked directly, so
        // it says so, in the reference's own words (contract §2, §5).
        eprintln!("mettle exec: this command has no instance, so eval is not allowed.");
        return Err(ExitCode::from(1));
    };

    let mut ctx = ReplContext::new(
        session,
        graph,
        graph.root,
        SolvedCommand {
            ir: run.ir,
            bounds: run.bounds,
            scoped: run.scoped,
            goal: run.goal,
            instance,
            opts: run.opts,
        },
    );

    let mut any_failure = failed;
    if !eval.is_empty() {
        let mut results = String::new();
        any_failure |= repl::eval_each(&mut ctx, eval, &mut results);
        crate::write_stdout(results)?;
    }
    if repl {
        if let Err(e) = repl::run_loop(&mut ctx) {
            if e.kind() == std::io::ErrorKind::BrokenPipe {
                return Err(ExitCode::from(141));
            }
            eprintln!("mettle exec: {e}");
            return Err(ExitCode::from(2));
        }
    }
    if any_failure {
        Err(ExitCode::from(1))
    } else {
        Ok(())
    }
}

/// Reads and loads (`open`s and all) `path` — the same error-rendering path
/// `run_check` uses (E3/E5): a lex/parse failure is never this command's
/// business to reinterpret, it's the same caret diagnostic `mettle check`
/// would print.
fn load(path: &str) -> Result<ModuleGraph, ExitCode> {
    let source = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("mettle exec: cannot read {path}: {e}");
            return Err(ExitCode::from(2));
        }
    };

    let loader = FilesystemLoader::new();
    match ModuleGraph::load_with_source(path, source.clone(), &loader) {
        Ok(graph) => Ok(graph),
        Err(err) => {
            crate::render_load_error(path, &source, &err);
            Err(ExitCode::from(1))
        }
    }
}

/// Resolves a loaded graph, rendering the reject (or the warnings) as
/// `mettle check` does.
///
/// Uses [`resolve_session`] rather than `resolve` so the resolver's symbol
/// tables outlive the pass — that is what lets `--repl`/`--eval` type-check an
/// expression typed at the prompt (mt-062). The pipeline it runs, and so the
/// verdict and warnings, are the same either way.
fn resolve_graph(graph: &ModuleGraph) -> Result<ResolvedSession<'_>, ExitCode> {
    let session = match resolve_session(graph) {
        Ok(session) => session,
        Err(err) => {
            let file = graph.files.file(err.span().file);
            eprint!(
                "{}",
                crate::diagnostics::render(&file.source, &file.path, err.span(), &err.to_string())
            );
            return Err(ExitCode::from(1));
        }
    };
    // Warnings are informational only (never affect a verdict) and print to
    // stderr exactly as `mettle check` prints them.
    for warning in session.warnings() {
        let file = graph.files.file(warning.span().file);
        eprint!(
            "{}",
            crate::diagnostics::render_label(
                &file.source,
                &file.path,
                warning.span(),
                "warning",
                &crate::diagnostics::warning_message(warning)
            )
        );
    }
    Ok(session)
}

/// Applies the `expect 1 ⇒ symmetry 0` override (translation-ref §3/§16.4) for a
/// command: an `expect 1` annotation forces symmetry breaking off (matching the
/// jar's `A4Solution`), so the enumerated count is the raw SB-0 count. Every other
/// `expect` (or none) leaves `opts` unchanged.
fn effective_opts(opts: &SolveOptions, cmd: &ResolvedCommand) -> SolveOptions {
    if matches!(cmd.expect, Some(Expect::Sat)) {
        SolveOptions {
            symmetry: 0,
            ..*opts
        }
    } else {
        *opts
    }
}

/// Everything one command's pipeline produced, kept rather than dropped: the
/// verdict *and* the `Ir`/universe/bounds/goal an evaluator needs to ask
/// further questions of the instance (mt-062).
struct CommandRun {
    ir: Ir,
    scoped: ScopedUniverse,
    bounds: BoundsResult,
    goal: LoweredGoal,
    verdict: SolveVerdict,
    /// The options the solve actually used (after the `expect 1` override).
    opts: SolveOptions,
}

/// Drives `compute_universe` → `compute_bounds` → `lower_command` →
/// `solve_goal` for one command. Every typed defer surfaces as the `Err` its
/// phase raised; the caller decides how to say so.
fn run_pipeline(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    cmd: &ResolvedCommand,
    idx: usize,
    opts: &SolveOptions,
) -> Result<CommandRun, als_core::TranslateError> {
    let scoped = compute_universe(world, graph, cmd)?;
    let mut ir = Ir::default();
    let bounds = compute_bounds(world, &scoped, &mut ir);
    let goal = lower_command(world, graph, &scoped, &bounds, &mut ir, idx)?;

    // `expect 1` forces symmetry breaking off (translation-ref §3/§16.4): the
    // jar's `A4Solution` does `sym = expected==1 ? 0 : opt.symmetry`, so a command
    // annotated `expect 1` is solved with no SBP (changing the enumerated count).
    // mettle mirrors that at the command boundary, where the resolved `expect` is
    // available, leaving the shared `opts` untouched.
    let opts = effective_opts(opts, cmd);
    let verdict = solve_goal(&ir, &scoped, &goal, &bounds, &opts)?;
    Ok(CommandRun {
        ir,
        scoped,
        bounds,
        goal,
        verdict,
        opts,
    })
}

/// Runs one command's full pipeline, appending its rendered block to `out`.
/// Returns whether this command counts as a failure for the process exit
/// code (a `CANNOT EXECUTE`, an `UNKNOWN`, or an `expect` mismatch).
fn run_one_command(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    pos: usize,
    idx: usize,
    cmd: &ResolvedCommand,
    opts: &SolveOptions,
    out: &mut String,
) -> bool {
    let _ = writeln!(out, "{}", command_header(world, graph, pos, cmd));
    match run_pipeline(world, graph, cmd, idx, opts) {
        Ok(run) => render_verdict(cmd, &run, out),
        Err(e) => {
            let _ = writeln!(out, "CANNOT EXECUTE: {e}\n");
            true
        }
    }
}

/// Renders one solved command's verdict block (and any `expect` check),
/// returning whether it counts as a failure.
fn render_verdict(cmd: &ResolvedCommand, run: &CommandRun, out: &mut String) -> bool {
    // Polarity (als-core/src/solve.rs module docs): a `check`'s goal is
    // already negated at lowering, so `Sat` there *is* a counterexample.
    let (is_sat, mut failed) = match &run.verdict {
        SolveVerdict::Sat(inst) => {
            let label = match cmd.kind {
                CmdKind::Run => "SAT",
                CmdKind::Check => "COUNTEREXAMPLE",
            };
            let _ = writeln!(out, "{label}");
            out.push_str(&render_instance(&run.ir, inst));
            (Some(true), false)
        }
        SolveVerdict::Unsat => {
            let label = match cmd.kind {
                CmdKind::Run => "UNSAT (no instance)",
                CmdKind::Check => "VALID (no counterexample)",
            };
            let _ = writeln!(out, "{label}");
            (Some(false), false)
        }
        SolveVerdict::Unknown => {
            let _ = writeln!(out, "UNKNOWN (conflict budget exhausted)");
            (None, true)
        }
    };

    if let (Some(sat), Some(expect)) = (is_sat, cmd.expect) {
        match expect {
            Expect::Sat if sat => {
                let _ = writeln!(out, "expect 1: ok");
            }
            Expect::Sat => {
                let _ = writeln!(out, "expect 1: MISMATCH (got UNSAT)");
                failed = true;
            }
            Expect::Unsat if !sat => {
                let _ = writeln!(out, "expect 0: ok");
            }
            Expect::Unsat => {
                let _ = writeln!(out, "expect 0: MISMATCH (got SAT)");
                failed = true;
            }
            // `expect N` for any other integer: accepted, never checked
            // (matches `als_syntax::ast::Expect::Other`'s own doc).
            Expect::Other(_) => {}
        }
    }

    let _ = writeln!(out);
    failed
}

/// Resolves `--command <sel>` against the executable (root-module) commands:
/// a valid `0`-based index wins outright (unambiguous by construction); else
/// the unique command whose label or target name equals `sel`. Zero or
/// multiple non-index matches are both errors — the caller lists every
/// available command either way.
fn select_command(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    root_cmds: &[(usize, &ResolvedCommand)],
    sel: &str,
) -> Result<usize, String> {
    if let Ok(idx) = sel.parse::<usize>() {
        return if idx < root_cmds.len() {
            Ok(idx)
        } else {
            Err(format!(
                "no command at index {idx} ({} command(s) available)",
                root_cmds.len()
            ))
        };
    }
    let matches: Vec<usize> = root_cmds
        .iter()
        .enumerate()
        .filter(|(_, (_, cmd))| {
            cmd.label.as_deref() == Some(sel)
                || target_name(world, graph, &cmd.target).as_deref() == Some(sel)
        })
        .map(|(pos, _)| pos)
        .collect();
    match matches.len() {
        0 => Err(format!("no command matches `{sel}`")),
        1 => Ok(matches[0]),
        _ => Err(format!(
            "`{sel}` is ambiguous: matches commands at indices {matches:?}"
        )),
    }
}

/// The one-line, stable header for a command: its display index, kind, name
/// (label if written, else the target's name), and scope text. Exact
/// formatting is this CLI's own choice (mt-036 spec) — not a jar transcript.
fn command_header(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    pos: usize,
    cmd: &ResolvedCommand,
) -> String {
    let kind = match cmd.kind {
        CmdKind::Run => "run",
        CmdKind::Check => "check",
    };
    let name = cmd
        .label
        .clone()
        .or_else(|| target_name(world, graph, &cmd.target))
        .unwrap_or_else(|| "{...}".to_owned());
    format!("[{pos}] {kind} {name}{}", scope_text(world, cmd))
}

/// The target's source name, when it has one: the pred/fun name(s) for
/// `Named`, the assert's declared name for `Assert` (recovered via
/// [`assert_name`] — resolution keeps only `(body, module)`, never the name
/// itself). An inline block or an unresolved target has no name.
fn target_name(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    target: &CmdTargetResolved,
) -> Option<String> {
    match target {
        CmdTargetResolved::Named(fids) => Some(
            fids.iter()
                .map(|f| world.funcs[*f].name.clone())
                .collect::<Vec<_>>()
                .join("/"),
        ),
        CmdTargetResolved::Assert { body, module } => assert_name(graph, *module, *body),
        CmdTargetResolved::Block { .. } | CmdTargetResolved::Unresolved => None,
    }
}

/// Recovers a `check`ed assert's declared name by walking its module's AST
/// paragraphs back to the `assert` whose body matches — the reverse of what
/// `als_types`'s resolver did forward (`find_assert`) when it matched the
/// command's target name to this body in the first place. `ResolvedCommand`
/// never stores the name itself (resolution-doc scope), so this is the one
/// place it gets recovered, straight from the `ModuleGraph` the CLI already
/// holds after `resolve`.
fn assert_name(graph: &ModuleGraph, module: ModuleId, body: ExprId) -> Option<String> {
    let file = graph.modules[module].file;
    let ast = graph.files.file(file).ast_ref();
    for &pid in &ast.paragraphs {
        if let Para::Assert(a) = &ast.paras[pid] {
            if a.body == body {
                return match &a.name {
                    Some(ParaName::Ident(id)) => Some(id.text.clone()),
                    Some(ParaName::Str { value, .. }) => Some(value.clone()),
                    None => None,
                };
            }
        }
    }
    None
}

/// The command's scope clauses folded into one concise `for ...` suffix
/// (overall default, per-sig scopes, `int`/`seq`/`String` scopes) — empty
/// when nothing was written. Not a reparse of the source; a rebuild from the
/// already-resolved [`ResolvedCommand`] fields, so it reflects exactly what
/// `compute_universe` will use.
fn scope_text(world: &ResolvedWorld, cmd: &ResolvedCommand) -> String {
    let mut parts = Vec::new();
    if let Some(n) = cmd.overall {
        parts.push(n.to_string());
    }
    for cs in &cmd.scopes {
        let exact = if cs.is_exact { "exactly " } else { "" };
        parts.push(format!("{exact}{} {}", cs.scope, world.sigs[cs.sig].name));
    }
    if let Some(n) = cmd.bitwidth {
        parts.push(format!("{n} int"));
    }
    if let Some(n) = cmd.maxseq {
        parts.push(format!("{n} seq"));
    }
    if let Some(n) = cmd.maxstring {
        let exact = if cmd.string_exact { "exactly " } else { "" };
        parts.push(format!("{exact}{n} String"));
    }
    if parts.is_empty() {
        String::new()
    } else {
        format!(" for {}", parts.join(", "))
    }
}

/// Renders a decoded [`Instance`]: one line per relation in `RelId` order
/// (sigs, fields, and skolem relations alike — `ir.relations[rel].name`
/// covers all three uniformly, no special-casing needed), tuples in Alloy's
/// own arrow syntax (`A$0->B$1`); an empty relation prints `{}`.
fn render_instance(ir: &Ir, inst: &Instance) -> String {
    let mut out = String::new();
    for (rel, tuples) in inst.iter() {
        let name = &ir.relations[rel].name;
        let rendered: Vec<String> = tuples
            .iter()
            .map(|t| {
                t.atoms()
                    .iter()
                    .map(|a| inst.universe.name(*a))
                    .collect::<Vec<_>>()
                    .join("->")
            })
            .collect();
        let _ = writeln!(out, "  {name} = {{{}}}", rendered.join(", "));
    }
    out
}
