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
//!
//! A **temporal** command takes the parallel Rung-6 path (mt-067/mt-068): the
//! same phases, but `solve_temporal_command` sweeps the `steps` range and the
//! verdict renders as a state-by-state lasso trace ([`render_trace`]), with
//! `--repl`/`--eval` evaluating at a state of it (`crate::repl`).

use std::fmt::Write as _;
use std::process::ExitCode;

use als_core::ir::Ir;
use als_core::solve::Instance;
use als_core::{
    compute_bounds, compute_universe, lower_command, solve_goal, solve_temporal_command,
    BoundsResult, LoweredGoal, ScopedUniverse, SolveOptions, SolveVerdict, TemporalSolveConfig,
    TemporalTrace, TemporalVerdict,
};
use als_instance::{write_instance_xml, XmlRequest, XmlSolution};
use als_syntax::ast::{CmdKind, Expect, ExprId, Para, ParaName};
use als_types::{
    is_temporal_model, resolve_session, CmdTargetResolved, FilesystemLoader, ModuleGraph, ModuleId,
    ResolvedCommand, ResolvedSession, ResolvedWorld, StepsMax,
};

use crate::repl::{self, ReplContext, SolvedCommand, SolvedTrace};

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
        /// `--xml <PATH>`: write the command's instance XML there (mt-071).
        /// Exclusive with `--repl`/`--eval`/`--state`: an export is a
        /// one-shot, non-interactive artifact, and pretending otherwise would
        /// leave a file whose contents depend on where a REPL session ended up.
        xml: Option<&'a str>,
        /// `--state N`: the trace state `--eval`/`--repl` start at (mt-068).
        /// Kept signed and unnormalized — the pinned rule wraps and clamps it
        /// against the *solved* trace rather than rejecting anything (§(h)) —
        /// and optional, so that naming a state where there is no trace to name
        /// one in can be said out loud instead of silently meaning zero.
        state: Option<i64>,
    },
}

/// The value of an option that takes one, advancing the loop's cursor past it.
/// A missing value is a usage error, the same shape for every such flag.
fn option_value<'a>(
    args: &'a [String],
    i: &mut usize,
    flag: &str,
    expected: &str,
) -> Result<&'a str, ExitCode> {
    *i += 1;
    let Some(value) = args.get(*i) else {
        eprintln!("mettle exec: {flag} requires {expected}");
        crate::print_usage();
        return Err(ExitCode::from(2));
    };
    Ok(value.as_str())
}

/// An option's numeric value, or the usage error naming what it wanted.
fn number<T: std::str::FromStr>(value: &str, flag: &str, expected: &str) -> Result<T, ExitCode> {
    value.parse::<T>().map_err(|_| {
        eprintln!("mettle exec: {flag} expects {expected}, got `{value}`");
        ExitCode::from(2)
    })
}

/// `mettle exec <file.als> [--command <sel>] [--allow-overflow] [--conflicts N]
/// [--encode-budget N] [--state N]` — hand-rolled arg parsing (no clap), the
/// same idiom `run_parse`/`run_check` use. Unlike those, several options take a
/// value, so this loop walks `args` by index rather than a plain `for`.
fn parse_args(args: &[String]) -> Result<ParsedArgs<'_>, ExitCode> {
    let mut path: Option<&str> = None;
    let mut command_sel: Option<&str> = None;
    let mut allow_overflow = false;
    let mut conflicts: Option<u64> = None;
    let mut encode_budget: Option<u64> = None;
    let mut eval: Vec<&str> = Vec::new();
    let mut repl = false;
    let mut state: Option<i64> = None;
    let mut xml: Option<&str> = None;
    let mut backend = als_core::Backend::default();

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "-h" | "--help" => {
                crate::print_usage();
                return Ok(ParsedArgs::Help);
            }
            "--allow-overflow" => allow_overflow = true,
            "--repl" => repl = true,
            "--eval" => eval.push(option_value(args, &mut i, "--eval", "an expression")?),
            "--state" => {
                let v = option_value(args, &mut i, "--state", "a state index")?;
                state = Some(number(v, "--state", "an integer")?);
            }
            "--xml" => xml = Some(option_value(args, &mut i, "--xml", "an output path")?),
            "--command" => command_sel = Some(option_value(args, &mut i, "--command", "a value")?),
            "--solver" => {
                let v = option_value(args, &mut i, "--solver", "a solver name")?;
                backend = crate::parse_solver("exec", v)?;
            }
            "--conflicts" => {
                let v = option_value(args, &mut i, "--conflicts", "a value")?;
                conflicts = Some(number(v, "--conflicts", "a non-negative integer")?);
            }
            "--encode-budget" => {
                let v = option_value(args, &mut i, "--encode-budget", "a value")?;
                encode_budget = Some(number(v, "--encode-budget", "a non-negative integer")?);
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
            backend,
            ..SolveOptions::default()
        },
        eval,
        repl,
        xml,
        state,
    })
}

pub(crate) fn run_exec(args: &[String]) -> Result<(), ExitCode> {
    let (path, command_sel, opts, eval, repl, xml, state) = match parse_args(args)? {
        ParsedArgs::Help => return Ok(()),
        ParsedArgs::Run {
            path,
            command_sel,
            opts,
            eval,
            repl,
            xml,
            state,
        } => (path, command_sel, opts, eval, repl, xml, state),
    };
    if xml.is_some() && (repl || !eval.is_empty() || state.is_some()) {
        eprintln!("mettle exec: --xml exports one solved command; it does not combine with --repl/--eval/--state");
        crate::print_usage();
        return Err(ExitCode::from(2));
    }

    let graph = load(path)?;
    let session = resolve_graph(&graph)?;
    let world = session.world();

    let root_cmds = root_commands(world, &graph);

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

    if let Some(xml_path) = xml {
        return run_xml(world, &graph, &root_cmds, &selected, &opts, path, xml_path);
    }
    if repl || !eval.is_empty() {
        return run_evaluator(
            &session,
            &graph,
            &root_cmds,
            &selected,
            &opts,
            &EvalRequest { eval, repl, state },
        );
    }
    // A state index only means something to an evaluator: silently accepting it
    // for a plain run would look like it had changed what gets printed.
    if state.is_some() {
        eprintln!("mettle exec: --state applies to --repl/--eval; a plain run prints every state");
        crate::print_usage();
        return Err(ExitCode::from(2));
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

/// The root module's executable commands, as `(world index, command)` pairs in
/// source order — a command's position in this vec is its display index and
/// what `--command <N>` selects.
///
/// Only root-module commands execute; an opened module's are never run
/// (matching the jar). Shared with [`crate::serve`], which selects exactly one
/// of them the same way `--xml` does.
pub(crate) fn root_commands<'a>(
    world: &'a ResolvedWorld,
    graph: &ModuleGraph,
) -> Vec<(usize, &'a ResolvedCommand)> {
    let root_file = graph.modules[graph.root].file;
    world
        .commands
        .iter()
        .enumerate()
        .filter(|(_, c)| c.span.file == root_file)
        .collect()
}

/// What `--repl`/`--eval`/`--state` asked for, as one bundle (the three travel
/// together everywhere below).
struct EvalRequest<'a> {
    /// `--eval <EXPR>`, in the order written.
    eval: Vec<&'a str>,
    /// `--repl`.
    repl: bool,
    /// `--state N`, unnormalized (see [`ParsedArgs::Run::state`]).
    state: Option<i64>,
}

/// `--repl` / `--eval` (mt-062, per-state since mt-068): solve **one** command,
/// print its verdict and instance/trace exactly as a plain run would, then
/// evaluate against it.
///
/// Attaching to exactly one command is the whole point — the evaluator answers
/// questions *about an instance*, and a file with several commands has several.
/// Any command that yields an instance works, a `check`'s counterexample and a
/// temporal command's lasso trace included.
fn run_evaluator(
    session: &ResolvedSession<'_>,
    graph: &ModuleGraph,
    root_cmds: &[(usize, &ResolvedCommand)],
    selected: &[usize],
    opts: &SolveOptions,
    request: &EvalRequest<'_>,
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

    // Rung-6 dispatch, the same discriminator the plain run uses: a temporal
    // command is solved as a lasso and evaluated at a state (§(h)).
    let temporal = is_temporal_model(world, graph, cmd);
    if !temporal && request.state.is_some() {
        // The reference *would* answer here (a static solve is internally a
        // one-state trace), but nothing pinned that combination, and quietly
        // reading `--state 3` as state 0 is exactly the silent surprise this
        // CLI does not do. Same wording the prompt's `:state` uses.
        eprintln!("mettle exec: this command is not temporal, so its instance has a single state.");
        return Err(ExitCode::from(2));
    }

    let mut out = String::new();
    let _ = writeln!(out, "{}", command_header(world, graph, *pos, cmd));
    let solved = if temporal {
        solve_for_temporal_eval(
            world,
            graph,
            cmd,
            idx,
            opts,
            request.state.unwrap_or(0),
            &mut out,
        )
    } else {
        solve_for_eval(world, graph, cmd, idx, opts, &mut out)
    };
    let (solved, failed) = match solved {
        Ok(solved) => solved,
        Err(failure) => {
            crate::write_stdout(out)?;
            if let Some(message) = failure.message {
                eprintln!("mettle exec: {message}");
            }
            return Err(ExitCode::from(1));
        }
    };
    crate::write_stdout(out)?;

    let mut ctx = ReplContext::new(session, graph, graph.root, solved);
    let mut any_failure = failed;
    if !request.eval.is_empty() {
        let mut results = String::new();
        any_failure |= repl::eval_each(&mut ctx, &request.eval, &mut results);
        crate::write_stdout(results)?;
    }
    if request.repl {
        if let Some(banner) = ctx.trace_banner() {
            crate::write_stdout(format!("{banner}\n"))?;
        }
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

/// `--xml <PATH>` (mt-071): solve **one** command, print its verdict block
/// exactly as a plain run would, then write that instance as Alloy instance XML
/// — the reference jar's own `A4Solution.writeXML` byte shape
/// (`docs/reference/alloy6-instance-xml.md`, via [`als_instance`]).
///
/// One command, like `--repl`/`--eval`: an instance XML file describes exactly
/// one solved command, so a file with several needs `--command <sel>`. A
/// command with **no** instance (UNSAT, a typed defer, an exhausted budget) is
/// a loud failure with nothing written — never an empty or stale file. That
/// matches the reference, whose writer throws `ErrorAPI("This solution is
/// unsatisfiable.")` before opening the `<alloy>` root (§11 / evaluator
/// contract §2).
///
/// A temporal command exports the whole lasso: one `<instance>` block per
/// state, plus the extra unrolled blocks the `macros` mechanism can add (§7).
fn run_xml(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    root_cmds: &[(usize, &ResolvedCommand)],
    selected: &[usize],
    opts: &SolveOptions,
    filename: &str,
    xml_path: &str,
) -> Result<(), ExitCode> {
    let [pos] = selected else {
        eprintln!(
            "mettle exec: --xml exports one command's instance, but this file has {} commands",
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
    let rendered = if is_temporal_model(world, graph, cmd) {
        temporal_xml(world, graph, cmd, idx, opts, filename, &mut out)
    } else {
        static_xml(world, graph, cmd, idx, opts, filename, &mut out)
    };
    crate::write_stdout(out)?;

    let xml = match rendered {
        Ok(xml) => xml,
        Err(failure) => {
            if let Some(message) = failure.message {
                eprintln!("mettle exec: {message}");
            }
            return Err(ExitCode::from(1));
        }
    };
    if let Err(e) = std::fs::write(xml_path, xml) {
        eprintln!("mettle exec: cannot write {xml_path}: {e}");
        return Err(ExitCode::from(2));
    }
    eprintln!("mettle exec: wrote {xml_path}");
    Ok(())
}

/// The static half of [`run_xml`]: solve, render the verdict block, export.
fn static_xml(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    cmd: &ResolvedCommand,
    idx: usize,
    opts: &SolveOptions,
    filename: &str,
    out: &mut String,
) -> Result<String, NoInstance> {
    let run = match run_pipeline(world, graph, cmd, idx, opts) {
        Ok(run) => run,
        Err(e) => {
            let _ = writeln!(out, "CANNOT EXECUTE: {e}\n");
            return Err(NoInstance { message: None });
        }
    };
    render_verdict(cmd, &run, out);
    let CommandRun {
        mut ir,
        scoped,
        bounds,
        goal,
        verdict,
        opts,
    } = run;
    let SolveVerdict::Sat(instance) = verdict else {
        return Err(NoInstance {
            message: Some(NO_XML_INSTANCE),
        });
    };
    let request = XmlRequest {
        world,
        graph,
        scoped: &scoped,
        bounds: &bounds,
        command: idx,
        filename,
        opts,
        solution: XmlSolution::Static {
            instance: &instance,
            goal: &goal,
        },
    };
    write_instance_xml(&mut ir, &request).map_err(|e| {
        let _ = writeln!(out, "CANNOT EXPORT: {e}");
        NoInstance { message: None }
    })
}

/// The temporal half of [`run_xml`]: sweep, render the trace block, export the
/// whole lasso.
fn temporal_xml(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    cmd: &ResolvedCommand,
    idx: usize,
    opts: &SolveOptions,
    filename: &str,
    out: &mut String,
) -> Result<String, NoInstance> {
    let run = match run_temporal_pipeline(world, graph, cmd, idx, opts) {
        Ok(run) => run,
        Err(e) => {
            let _ = writeln!(out, "CANNOT EXECUTE: {e}\n");
            return Err(NoInstance { message: None });
        }
    };
    render_temporal_verdict(cmd, &run, out);
    let TemporalRun {
        mut ir,
        scoped,
        bounds,
        verdict,
        opts,
    } = run;
    let TemporalVerdict::Sat(trace) = verdict else {
        return Err(NoInstance {
            message: Some(NO_XML_INSTANCE),
        });
    };
    let request = XmlRequest {
        world,
        graph,
        scoped: &scoped,
        bounds: &bounds,
        command: idx,
        filename,
        opts,
        solution: XmlSolution::Trace { trace: &trace },
    };
    write_instance_xml(&mut ir, &request).map_err(|e| {
        let _ = writeln!(out, "CANNOT EXPORT: {e}");
        NoInstance { message: None }
    })
}

/// Why a command reached no evaluable instance. The verdict block is already in
/// the caller's `out` either way; `message` is the extra stderr line a
/// no-instance verdict earns (a `CANNOT EXECUTE` has already said everything).
struct NoInstance {
    message: Option<&'static str>,
}

/// The reference never even points its evaluator at a command with no instance
/// (its writer refuses first); mettle can be asked directly, so it says so, in
/// the reference's own words (evaluator contract §2, §5).
const NO_INSTANCE: &str = "this command has no instance, so eval is not allowed.";

/// The `--xml` twin: the reference's own writer refuses an unsatisfiable
/// solution outright (`ErrorAPI("This solution is unsatisfiable.")`), so mettle
/// refuses too rather than writing an instance-less file.
const NO_XML_INSTANCE: &str = "this command has no instance, so there is nothing to export.";

/// Solves a **static** command for the evaluator, rendering its verdict block
/// into `out`. `Ok`'s flag is whether the verdict itself counts as a failure
/// (an `expect` mismatch).
fn solve_for_eval(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    cmd: &ResolvedCommand,
    idx: usize,
    opts: &SolveOptions,
    out: &mut String,
) -> Result<(SolvedCommand, bool), NoInstance> {
    let run = match run_pipeline(world, graph, cmd, idx, opts) {
        Ok(run) => run,
        Err(e) => {
            let _ = writeln!(out, "CANNOT EXECUTE: {e}\n");
            return Err(NoInstance { message: None });
        }
    };
    let failed = render_verdict(cmd, &run, out);
    let SolveVerdict::Sat(instance) = run.verdict else {
        return Err(NoInstance {
            message: Some(NO_INSTANCE),
        });
    };
    Ok((
        SolvedCommand {
            ir: run.ir,
            bounds: run.bounds,
            scoped: run.scoped,
            goal: run.goal,
            instance,
            opts: run.opts,
            trace: None,
        },
        failed,
    ))
}

/// Solves a **temporal** command for the evaluator (mt-068): the same lasso
/// sweep a plain run does, rendered the same way, plus the per-state evaluation
/// context sitting at `state` (normalized against the solved trace — §(h): a
/// state index is never an error).
fn solve_for_temporal_eval(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    cmd: &ResolvedCommand,
    idx: usize,
    opts: &SolveOptions,
    state: i64,
    out: &mut String,
) -> Result<(SolvedCommand, bool), NoInstance> {
    let run = match run_temporal_pipeline(world, graph, cmd, idx, opts) {
        Ok(run) => run,
        Err(e) => {
            let _ = writeln!(out, "CANNOT EXECUTE: {e}\n");
            return Err(NoInstance { message: None });
        }
    };
    let failed = render_temporal_verdict(cmd, &run, out);
    let TemporalVerdict::Sat(trace) = run.verdict else {
        return Err(NoInstance {
            message: Some(NO_INSTANCE),
        });
    };
    let artifacts = trace.artifacts;
    Ok((
        SolvedCommand {
            ir: run.ir,
            bounds: run.bounds,
            scoped: run.scoped,
            goal: artifacts.goal,
            instance: artifacts.instance,
            opts: run.opts,
            trace: Some(SolvedTrace {
                unrolled: artifacts.unrolled,
                loop_state: trace.loop_state,
                // Clamped, not wrapped: `--state 5` on a 2-state trace means
                // the *sixth* time step, which its past operators can tell from
                // state 1's first visit (§(h), probe P-068-1).
                state: state.max(0),
            }),
        },
        failed,
    ))
}

/// Reads and loads (`open`s and all) `path` — the same error-rendering path
/// `run_check` uses (E3/E5): a lex/parse failure is never this command's
/// business to reinterpret, it's the same caret diagnostic `mettle check`
/// would print.
pub(crate) fn load(path: &str) -> Result<ModuleGraph, ExitCode> {
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
pub(crate) fn resolve_graph(graph: &ModuleGraph) -> Result<ResolvedSession<'_>, ExitCode> {
    let session = match resolve_session(graph) {
        Ok(session) => session,
        Err(err) => {
            let file = graph.files.file(err.span().file);
            eprint!(
                "{}",
                crate::diagnostics::render_error(&file.source, &file.path, &err)
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

/// The three phases before the solver, for one command: everything
/// [`solve_goal`] (or [`als_core::enumerate`]) needs, and nothing about how the
/// answer is obtained.
///
/// Split out of [`run_pipeline`] so that `serve` — which enumerates rather than
/// solving once — shares the lowering instead of forking it.
pub(crate) struct LoweredCommand {
    pub(crate) scoped: ScopedUniverse,
    pub(crate) bounds: BoundsResult,
    pub(crate) goal: LoweredGoal,
    /// The options the solve should use (after the `expect 1` override).
    pub(crate) opts: SolveOptions,
}

/// Drives `compute_universe` → `compute_bounds` → `lower_command` for one
/// command, into the caller's `ir`.
///
/// # Errors
/// Whatever typed defer a phase raised; the caller decides how to say so.
pub(crate) fn lower_for_solve(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    cmd: &ResolvedCommand,
    idx: usize,
    opts: &SolveOptions,
    ir: &mut Ir,
) -> Result<LoweredCommand, als_core::TranslateError> {
    let scoped = compute_universe(world, graph, cmd)?;
    let bounds = compute_bounds(world, &scoped, ir);
    let goal = lower_command(world, graph, &scoped, &bounds, ir, idx)?;
    Ok(LoweredCommand {
        scoped,
        bounds,
        goal,
        // `expect 1` forces symmetry breaking off (translation-ref §3/§16.4):
        // the jar's `A4Solution` does `sym = expected==1 ? 0 : opt.symmetry`, so
        // a command annotated `expect 1` is solved with no SBP (changing the
        // enumerated count). mettle mirrors that at the command boundary, where
        // the resolved `expect` is available, leaving the shared `opts`
        // untouched.
        opts: effective_opts(opts, cmd),
    })
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
    let mut ir = Ir::default();
    let LoweredCommand {
        scoped,
        bounds,
        goal,
        opts,
    } = lower_for_solve(world, graph, cmd, idx, opts, &mut ir)?;
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
    // Rung-6 dispatch (mt-067): the pinned discriminator, exactly as jar-side
    // `CompUtil.isTemporalModel` gates `ScopeComputer`'s trace bounds.
    if is_temporal_model(world, graph, cmd) {
        return run_temporal_command(world, graph, cmd, idx, opts, out);
    }
    match run_pipeline(world, graph, cmd, idx, opts) {
        Ok(run) => render_verdict(cmd, &run, out),
        Err(e) => {
            let _ = writeln!(out, "CANNOT EXECUTE: {e}\n");
            true
        }
    }
}

/// Executes one **temporal** command: solve, render, blank line — the temporal
/// twin of the static [`run_pipeline`] + [`render_verdict`] pair.
fn run_temporal_command(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    cmd: &ResolvedCommand,
    idx: usize,
    opts: &SolveOptions,
    out: &mut String,
) -> bool {
    match run_temporal_pipeline(world, graph, cmd, idx, opts) {
        Ok(run) => render_temporal_verdict(cmd, &run, out),
        Err(e) => {
            let _ = writeln!(out, "CANNOT EXECUTE: {e}\n");
            true
        }
    }
}

/// Everything one temporal command's pipeline produced — the [`CommandRun`]
/// twin, kept for the same reason (the evaluator asks the trace further
/// questions, mt-068).
///
/// **No solve budgets are applied here, deliberately.** `exec` is the drop-in
/// surface: the reference jar runs a command until it answers, so mettle does
/// too, and a wide `steps` range on a big model can genuinely grind. Budgets
/// belong to the conformance gauge, which owns a sweep's cost
/// ([`TemporalSolveConfig::primary_var_cap`] and the `--conflicts` /
/// `--encode-budget` flags are the opt-ins).
pub(crate) struct TemporalRun {
    pub(crate) ir: Ir,
    pub(crate) scoped: ScopedUniverse,
    pub(crate) bounds: BoundsResult,
    pub(crate) verdict: TemporalVerdict,
    /// The options the sweep actually used (after the `expect 1` override).
    pub(crate) opts: SolveOptions,
}

/// Everything a temporal command needs **before** the sweep — universe, bounds,
/// arena and the `expect 1`-corrected options.
///
/// Split out for `serve` (mt-076), which drives the sweep itself through
/// `als_core`'s [`TraceEnumerator`](als_core::TraceEnumerator) rather than
/// calling [`run_temporal_pipeline`] and then re-solving: the trace it displays
/// must be the *enumerator's* first, or the first "New Trace" would show the
/// same one again.
pub(crate) struct TemporalSetup {
    pub(crate) ir: Ir,
    pub(crate) scoped: ScopedUniverse,
    pub(crate) bounds: BoundsResult,
    pub(crate) opts: SolveOptions,
}

/// The pre-solve phases of [`run_temporal_pipeline`], shared with `serve`.
pub(crate) fn setup_temporal(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    cmd: &ResolvedCommand,
    opts: &SolveOptions,
) -> Result<TemporalSetup, als_core::TranslateError> {
    let scoped = compute_universe(world, graph, cmd)?;
    let mut ir = Ir::default();
    let bounds = compute_bounds(world, &scoped, &mut ir);
    Ok(TemporalSetup {
        ir,
        scoped,
        bounds,
        opts: effective_opts(opts, cmd),
    })
}

/// The [`TemporalSolveConfig`] `exec` and `serve` both sweep with: no budgets
/// and no cap (see [`TemporalRun`]'s note), self-check left to the debug net.
pub(crate) fn temporal_cfg(opts: SolveOptions) -> TemporalSolveConfig {
    TemporalSolveConfig {
        opts,
        primary_var_cap: None,
        self_check: false,
    }
}

/// Sweeps one temporal command's `steps` range, first SAT wins
/// (`als_core::temporal_solve`), keeping the artifacts rather than dropping them.
pub(crate) fn run_temporal_pipeline(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    cmd: &ResolvedCommand,
    idx: usize,
    opts: &SolveOptions,
) -> Result<TemporalRun, als_core::TranslateError> {
    let mut setup = setup_temporal(world, graph, cmd, opts)?;
    let cfg = temporal_cfg(setup.opts);
    let verdict = solve_temporal_command(
        world,
        graph,
        &setup.scoped,
        &setup.bounds,
        &mut setup.ir,
        idx,
        &cfg,
    )?;
    Ok(TemporalRun {
        ir: setup.ir,
        scoped: setup.scoped,
        bounds: setup.bounds,
        verdict,
        opts: setup.opts,
    })
}

/// Renders one solved temporal command's verdict block (and any `expect`
/// check), returning whether it counts as a failure. Ends with the blank
/// separator line [`render_verdict`] ends with — one command, one block, either
/// way.
fn render_temporal_verdict(cmd: &ResolvedCommand, run: &TemporalRun, out: &mut String) -> bool {
    let (is_sat, mut failed) = match &run.verdict {
        TemporalVerdict::Sat(trace) => {
            let label = match cmd.kind {
                CmdKind::Run => "SAT",
                CmdKind::Check => "COUNTEREXAMPLE",
            };
            let _ = writeln!(out, "{label}");
            out.push_str(&render_trace(&run.ir, trace));
            (Some(true), false)
        }
        // UNSAT is bound-relative and says so: "no counterexample within this
        // many states", never "the assertion holds" (alloy6-temporal.md §(c),
        // probe T-10b).
        TemporalVerdict::Unsat => {
            let label = match cmd.kind {
                CmdKind::Run => "UNSAT (no instance",
                CmdKind::Check => "VALID (no counterexample",
            };
            let _ = writeln!(out, "{label} within {})", steps_bound_text(cmd));
            (Some(false), false)
        }
        TemporalVerdict::Unknown { k } => {
            let _ = writeln!(
                out,
                "UNKNOWN (conflict budget exhausted at trace length {k})"
            );
            (None, true)
        }
        TemporalVerdict::PrimaryVarCap { k, primaries } => {
            let _ = writeln!(
                out,
                "UNKNOWN (trace length {k} needs {primaries} primary variables)"
            );
            (None, true)
        }
    };

    failed |= render_expect(cmd, is_sat, out);
    let _ = writeln!(out);
    failed
}

/// The command's resolved trace bound, for the bound-relative UNSAT wording.
fn steps_bound_text(cmd: &ResolvedCommand) -> String {
    let range = cmd.steps_range();
    match range.max {
        StepsMax::Bounded(max) if range.min == max => format!("exactly {max} steps"),
        StepsMax::Bounded(max) => format!("{max} steps"),
        // Unreachable: an open range is a typed defer before any solving.
        StepsMax::Unbounded => format!("{}.. steps", range.min),
    }
}

/// Renders one solved command's verdict block (and any `expect` check),
/// returning whether it counts as a failure.
fn render_verdict(cmd: &ResolvedCommand, run: &CommandRun, out: &mut String) -> bool {
    // Polarity (als-core/src/solve.rs module docs): a `check`'s goal is
    // already negated at lowering, so `Sat` there *is* a counterexample.
    let (is_sat, failed) = match &run.verdict {
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

    let failed = failed | render_expect(cmd, is_sat, out);
    let _ = writeln!(out);
    failed
}

/// Renders the `expect` check for a solved command, returning whether it
/// mismatched. `is_sat` is `None` when no verdict was reached (nothing to
/// check). Shared by the static and temporal paths: `expect` handling is
/// identical under time (probe T-12 — the reference does not special-case it).
fn render_expect(cmd: &ResolvedCommand, is_sat: Option<bool>, out: &mut String) -> bool {
    let (Some(sat), Some(expect)) = (is_sat, cmd.expect) else {
        return false;
    };
    match expect {
        Expect::Sat if sat => {
            let _ = writeln!(out, "expect 1: ok");
            false
        }
        Expect::Sat => {
            let _ = writeln!(out, "expect 1: MISMATCH (got UNSAT)");
            true
        }
        Expect::Unsat if !sat => {
            let _ = writeln!(out, "expect 0: ok");
            false
        }
        Expect::Unsat => {
            let _ = writeln!(out, "expect 0: MISMATCH (got SAT)");
            true
        }
        // `expect N` for any other integer: accepted, never checked
        // (matches `als_syntax::ast::Expect::Other`'s own doc).
        Expect::Other(_) => false,
    }
}

/// Resolves `--command <sel>` against the executable (root-module) commands:
/// a valid `0`-based index wins outright (unambiguous by construction); else
/// the unique command whose label or target name equals `sel`. Zero or
/// multiple non-index matches are both errors — the caller lists every
/// available command either way.
pub(crate) fn select_command(
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
pub(crate) fn command_header(
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
    if let Some(steps) = cmd.steps {
        // Rendered as the jar's `Command.toString` does: a written range prints
        // as `N..M`, an open one as `N..`, a bare bound as `N`.
        let written = match (steps.min, steps.max) {
            (Some(min), StepsMax::Unbounded) => format!("{min}.."),
            (Some(min), StepsMax::Bounded(max)) => format!("{min}..{max}"),
            (None, StepsMax::Bounded(max)) => max.to_string(),
            (None, StepsMax::Unbounded) => "..".to_owned(),
        };
        parts.push(format!("{written} steps"));
    }
    if parts.is_empty() {
        String::new()
    } else {
        format!(" for {}", parts.join(", "))
    }
}

/// Renders a solved lasso [`TemporalTrace`] in the reference's own trace shape
/// (`A4Solution.toString(state)` with `state < 0`, source-pinned at
/// `scratchpad/src794/A4Solution.java:1767-1816` and jar-verified by probes
/// T-13/T-14; alloy6-temporal.md §(f)):
///
/// ```text
/// ---Trace---
/// ------State 0 (loop)-------
/// <every relation, at state 0>
/// ------State 1-------
/// <every relation, at state 1>
/// ```
///
/// The `(loop)` marker sits on the back-loop target — the state the trace
/// returns to — and **rigid content is re-emitted in full in every block**, with
/// no factoring-out: that is what the reference does (every non-`var` sig,
/// builtins included, appears byte-identically in each state), and
/// [`als_core::TemporalTrace::states`] already carries statics and skolems
/// verbatim per state, so it falls out of rendering each state's instance whole.
///
/// The block structure is the reference's exactly; the **lines inside** a block
/// are mettle's established instance rendering ([`render_instance`], unchanged
/// since mt-036) rather than the reference's `label=…` / `label<:field=…` /
/// `skolem …=…` line syntax, and tuple order is mettle's live solve order. Both
/// are the LEDGER-012 posture — shapes match, mettle's own naming and ordering
/// stand, and neither is scorecard-visible (ADR-0002 never diffs instance text).
pub(crate) fn render_trace(ir: &Ir, trace: &TemporalTrace) -> String {
    let mut out = String::from("---Trace---\n");
    for (state, instance) in trace.states.iter().enumerate() {
        let loop_marker = if state == trace.loop_state {
            " (loop)"
        } else {
            ""
        };
        let _ = writeln!(out, "------State {state}{loop_marker}-------");
        out.push_str(&render_instance(ir, instance));
    }
    out
}

/// Renders a decoded [`Instance`]: one line per relation in `RelId` order
/// (sigs, fields, and skolem relations alike — `ir.relations[rel].name`
/// covers all three uniformly, no special-casing needed), tuples in Alloy's
/// own arrow syntax (`A$0->B$1`); an empty relation prints `{}`.
pub(crate) fn render_instance(ir: &Ir, inst: &Instance) -> String {
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
