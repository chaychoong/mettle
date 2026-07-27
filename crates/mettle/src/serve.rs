//! `mettle serve` (mt-072) — the visualization entry point: solve one command,
//! then answer the Sterling provider protocol about it until Ctrl-C.
//!
//! Everything on the wire lives in [`als_sterling`]; everything about *what is
//! true of the solved command* lives here, behind that crate's
//! [`ServeSession`] trait. This module is therefore the third consumer of the
//! same machinery `exec` already drives, and re-derives none of it:
//!
//! - the pipeline is [`crate::exec::lower_for_solve`] /
//!   [`crate::exec::setup_temporal`], the same calls `--xml` makes (the
//!   temporal half stops before the sweep, because mt-076's enumerator *is*
//!   the sweep — see below);
//! - `data` is mt-071's [`als_instance::write_instance_xml`], with the same
//!   `filename=` the `--xml` export uses, so serve and export are
//!   byte-identical;
//! - `eval` is [`crate::repl::eval_line`], the REPL's own answer for one line
//!   of input — `:state` meta-command included, which is how a temporal
//!   session moves the state its expressions are evaluated at (the protocol has
//!   no state parameter of its own; see "Under-pinned corners" below);
//! - `click next` is `als_core`'s [`enumerate`] on a static command and
//!   [`TraceEnumerator`] on a temporal one (mt-076), whose orders *are* the
//!   enumeration orders the whole project is deterministic about.
//!
//! # The temporal session's five verbs (mt-076)
//!
//! `next`/`next-trace`, `next-config`, `new-init` and `new-fork` are the
//! reference GUI's own exploration buttons, with the semantics
//! [alloy6-temporal.md §(g)](../../../docs/reference/alloy6-temporal.md)'s
//! mt-076 probe wave pinned. Two consequences show up here rather than in
//! `als-core`:
//!
//! - **The displayed trace is the enumerator's first**, never a separately
//!   solved one — otherwise the first "New Trace" would redisplay it. That is
//!   why the temporal path calls [`crate::exec::setup_temporal`] and drives the
//!   sweep itself instead of calling `run_temporal_pipeline`.
//! - **"New Fork" needs a current state, and the protocol has none.** `click`
//!   carries only a verb string, so a client cannot say which state its graph
//!   view is showing. mettle reads it from the evaluator pane instead — which
//!   is the reference's own arrangement, since `VizGUI` and `OurConsole` share
//!   one `current` index. Today the only way to move it is the evaluator's
//!   `:state N`; a trace stepper (mt-075) should move the same index, and if it
//!   ever needs to do so without an evaluator round trip the protocol needs a
//!   payload the pinned shape does not have.
//!
//! # Why the artifacts are borrowed, not owned
//!
//! [`als_core::InstanceEnumerator`] borrows the `Ir`, universe and goal it was
//! built from, so a session that owned them *and* it would be
//! self-referential. The artifacts therefore live in [`run_serve`]'s frame and
//! the session borrows
//! them; the two consumers that need to *append* to the arena (the evaluator
//! lowering a fragment, the XML writer lowering a macro body) each take a clone
//! of it. That is what `Ir: Clone` is for, and it is why an advance costs one
//! incremental solve rather than re-enumerating from scratch.
//!
//! # Under-pinned corners, and the conservative reading taken
//!
//! - **Temporal eval posture.** The `eval` payload is `{id, datumId,
//!   expression}` — no state index anywhere (sterling.md §5), and Forge, the
//!   only reference provider, has no temporal state concept to compare against.
//!   A session therefore starts at **state 0** and moves only when the user
//!   says so, through the REPL's own `:state N` meta-command typed into the
//!   evaluator pane. No new protocol, no guessing.
//! - **Stale `datumId`.** Forge logs a mismatch and answers about its *current*
//!   instance anyway ("reporting back inaccurate data!", §5). mettle refuses
//!   instead and says which datum it is now on: an answer about a different
//!   instance is a wrong answer, and this project does not ship those (STYLE
//!   E5). Documented as a deliberate divergence from the only known provider.
//! - **`ProviderMeta.evaluator`'s type** (§10, upstream's own inconsistency) —
//!   sent as a boolean, following the `JSDoc` and Forge over the TypeScript
//!   annotation.

use std::net::TcpListener;
use std::process::ExitCode;
use std::sync::Mutex;

use als_core::ir::Ir;
use als_core::{enumerate, SolveOptions, TraceAdvance, TraceEnumerator, TraceStep, TranslateError};
use als_sterling::{stub_index_html, Provider, ServeEvent, ServeSession, StaticAssets};
use als_syntax::ast::CmdKind;
use als_types::{is_temporal_model, ModuleGraph, ResolvedCommand, ResolvedWorld};

mod session;

use crate::exec;
use session::{StaticArtifacts, StaticSession, TemporalArtifacts, TemporalSession};

/// The port `mettle serve` binds when `--port` is not given.
///
/// A fixed default (rather than an ephemeral one) so that the URL is the same
/// across restarts and a browser tab can simply be reloaded; `--port 0` asks
/// the OS for any free port when that is what is wanted. The number is
/// deliberately adjacent to Sterling's own 4000 convention and outside the
/// ranges a developer machine usually has spoken for.
const DEFAULT_PORT: u16 = 4030;

/// The request path mettle's own frontend opens its provider socket on. Any
/// path works (the server routes on the `Upgrade` header, not the path), so
/// this is a convention, not a requirement.
const WS_PATH: &str = "/ws";

/// What `mettle serve` was asked to do.
enum ParsedArgs<'a> {
    /// `-h`/`--help` — usage already printed.
    Help,
    Serve {
        path: &'a str,
        command_sel: Option<&'a str>,
        port: u16,
    },
}

fn parse_args(args: &[String]) -> Result<ParsedArgs<'_>, ExitCode> {
    let mut path: Option<&str> = None;
    let mut command_sel: Option<&str> = None;
    let mut port = DEFAULT_PORT;

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "-h" | "--help" => {
                crate::print_usage();
                return Ok(ParsedArgs::Help);
            }
            "--command" => command_sel = Some(option_value(args, &mut i, "--command", "a value")?),
            "--port" => {
                let value = option_value(args, &mut i, "--port", "a port number")?;
                let Ok(parsed) = value.parse::<u16>() else {
                    eprintln!(
                        "mettle serve: --port expects a number in 0..=65535, got `{value}` \
                         (0 asks the OS for any free port)"
                    );
                    return Err(ExitCode::from(2));
                };
                port = parsed;
            }
            other if other.starts_with('-') => {
                eprintln!("mettle serve: unknown option `{other}`");
                crate::print_usage();
                return Err(ExitCode::from(2));
            }
            other => {
                if path.replace(other).is_some() {
                    eprintln!("mettle serve: expected exactly one input file");
                    crate::print_usage();
                    return Err(ExitCode::from(2));
                }
            }
        }
        i += 1;
    }

    let Some(path) = path else {
        eprintln!("mettle serve: missing <file.als>");
        crate::print_usage();
        return Err(ExitCode::from(2));
    };
    Ok(ParsedArgs::Serve {
        path,
        command_sel,
        port,
    })
}

/// The value of an option that takes one (the `exec` idiom, reworded for this
/// subcommand's own error prefix).
fn option_value<'a>(
    args: &'a [String],
    i: &mut usize,
    flag: &str,
    expected: &str,
) -> Result<&'a str, ExitCode> {
    *i += 1;
    let Some(value) = args.get(*i) else {
        eprintln!("mettle serve: {flag} requires {expected}");
        crate::print_usage();
        return Err(ExitCode::from(2));
    };
    Ok(value.as_str())
}

/// `mettle serve <file.als> [--command <sel>] [--port N]`.
pub(crate) fn run_serve(args: &[String]) -> Result<(), ExitCode> {
    let (path, command_sel, port) = match parse_args(args)? {
        ParsedArgs::Help => return Ok(()),
        ParsedArgs::Serve {
            path,
            command_sel,
            port,
        } => (path, command_sel, port),
    };

    let graph = exec::load(path)?;
    let session = exec::resolve_graph(&graph)?;
    let world = session.world();
    let root_cmds = exec::root_commands(world, &graph);
    let pos = select_one(world, &graph, &root_cmds, command_sel)?;
    let (idx, cmd) = root_cmds[pos];
    let header = exec::command_header(world, &graph, pos, cmd);

    // Bind before solving: a port collision should be reported in the second it
    // takes to notice, not after a long solve.
    let listener = bind(port)?;

    let solved = SolveInputs {
        world,
        graph: &graph,
        cmd,
        idx,
        filename: path,
        header: &header,
    };
    // The two shapes differ only in what they own; from `serve` down they are
    // the same session behind the same trait.
    if is_temporal_model(world, &graph, cmd) {
        // As on the static side, the enumerator borrows the artifacts for as
        // long as it lives, so they are pinned to this frame first — and the
        // trace shown is the *enumerator's* first, never a separately-solved
        // one, or the first "New Trace" would redisplay it (mt-076).
        let artifacts = solved.setup_temporal()?;
        let mut enumerator = TraceEnumerator::new(
            world,
            &graph,
            &artifacts.scoped,
            &artifacts.bounds,
            &artifacts.ir,
            idx,
            &exec::temporal_cfg(artifacts.opts),
        )
        .map_err(|e| {
            eprintln!("mettle serve: CANNOT EXECUTE: {e}");
            ExitCode::from(1)
        })?;
        let trace = match enumerator.advance(TraceStep::NextPath).map_err(|e| {
            eprintln!("mettle serve: CANNOT EXECUTE: {e}");
            ExitCode::from(1)
        })? {
            TraceAdvance::Trace(trace) => trace,
            TraceAdvance::Exhausted => return Err(no_instance(cmd)),
            // Unreachable at today's defaults (`serve` applies no budgets, like
            // `exec`), but a search that stopped short has *not* shown there is
            // nothing to see, and must not be reported as if it had.
            other => {
                eprintln!(
                    "mettle serve: this command did not reach a verdict within its budget, \
                     so there is no trace to visualize ({other:?})."
                );
                return Err(ExitCode::from(1));
            }
        };
        let session =
            TemporalSession::new(&session, &graph, &solved, &artifacts, enumerator, &trace)
                .map_err(|e| report_export_failure(&e))?;
        serve(&listener, &header, path, session)
    } else {
        // The enumerator borrows the artifacts for as long as it lives, so
        // they are pinned to this frame before it is built (module docs).
        let (ir, lowered) = solved.lower()?;
        let artifacts = StaticArtifacts {
            ir,
            scoped: lowered.scoped,
            bounds: lowered.bounds,
            goal: lowered.goal,
            opts: lowered.opts,
        };
        let mut enumerator = enumerate(
            &artifacts.ir,
            &artifacts.scoped,
            &artifacts.goal,
            &artifacts.bounds,
            &artifacts.opts,
        )
        .map_err(|e| {
            eprintln!("mettle serve: CANNOT EXECUTE: {e}");
            ExitCode::from(1)
        })?;
        let Some(instance) = enumerator.next() else {
            return Err(no_instance(cmd));
        };
        let session =
            StaticSession::new(&session, &graph, &solved, &artifacts, enumerator, instance)
                .map_err(|e| report_export_failure(&e))?;
        serve(&listener, &header, path, session)
    }
}

/// Everything the two solve paths share, so neither re-reads the command.
struct SolveInputs<'a> {
    world: &'a ResolvedWorld,
    graph: &'a ModuleGraph,
    cmd: &'a ResolvedCommand,
    /// The command's index into [`ResolvedWorld::commands`].
    idx: usize,
    /// The model path exactly as written on the command line — the `filename=`
    /// attribute mt-071 writes, so serve's XML matches `--xml`'s byte for byte.
    filename: &'a str,
    header: &'a str,
}

impl SolveInputs<'_> {
    /// The three pre-solve phases, sharing `exec`'s implementation.
    fn lower(&self) -> Result<(Ir, exec::LoweredCommand), ExitCode> {
        let mut ir = Ir::default();
        let lowered = exec::lower_for_solve(
            self.world,
            self.graph,
            self.cmd,
            self.idx,
            &SolveOptions::default(),
            &mut ir,
        )
        .map_err(|e| {
            eprintln!("mettle serve: CANNOT EXECUTE: {e}");
            ExitCode::from(1)
        })?;
        Ok((ir, lowered))
    }

    /// The temporal command's pre-solve artifacts, sharing `exec`'s
    /// implementation. The sweep itself is the trace enumerator's (mt-076).
    fn setup_temporal(&self) -> Result<TemporalArtifacts, ExitCode> {
        let setup =
            exec::setup_temporal(self.world, self.graph, self.cmd, &SolveOptions::default())
                .map_err(|e| {
                    eprintln!("mettle serve: CANNOT EXECUTE: {e}");
                    ExitCode::from(1)
                })?;
        Ok(TemporalArtifacts {
            ir: setup.ir,
            scoped: setup.scoped,
            bounds: setup.bounds,
            opts: setup.opts,
        })
    }
}

/// The reference's own writer refuses an unsatisfiable solution outright, and
/// `--xml` refuses with it; there is even less to serve than to export.
fn no_instance(cmd: &ResolvedCommand) -> ExitCode {
    let what = match cmd.kind {
        CmdKind::Run => "no instance",
        CmdKind::Check => "no counterexample",
    };
    eprintln!("mettle serve: this command has {what}, so there is nothing to visualize.");
    ExitCode::from(1)
}

fn report_export_failure(error: &TranslateError) -> ExitCode {
    eprintln!("mettle serve: CANNOT EXPORT: {error}");
    ExitCode::from(1)
}

/// Resolves `--command`, insisting on exactly one: a session visualizes one
/// solved command, the same rule `--xml`/`--repl` follow.
fn select_one(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    root_cmds: &[(usize, &ResolvedCommand)],
    command_sel: Option<&str>,
) -> Result<usize, ExitCode> {
    let list = |problem: &str| {
        eprintln!("mettle serve: {problem}");
        eprintln!("select one with `--command <index|label|target>`:");
        for (pos, (_, cmd)) in root_cmds.iter().enumerate() {
            eprintln!("  {}", exec::command_header(world, graph, pos, cmd));
        }
        ExitCode::from(2)
    };
    match command_sel {
        Some(sel) => exec::select_command(world, graph, root_cmds, sel).map_err(|e| list(&e)),
        None if root_cmds.len() == 1 => Ok(0),
        None if root_cmds.is_empty() => {
            eprintln!("mettle serve: this file has no run/check command to visualize.");
            Err(ExitCode::from(2))
        }
        None => Err(list(&format!(
            "serve visualizes one command's instance, but this file has {} commands",
            root_cmds.len()
        ))),
    }
}

/// Binds localhost only. `mettle serve` hands an unauthenticated socket the
/// power to evaluate arbitrary expressions against a solved model; it is a
/// developer tool on one machine, and it says so by never listening on a
/// routable address.
fn bind(port: u16) -> Result<TcpListener, ExitCode> {
    TcpListener::bind(("127.0.0.1", port)).map_err(|e| {
        eprintln!("mettle serve: cannot listen on 127.0.0.1:{port}: {e}");
        if port != 0 {
            eprintln!(
                "mettle serve: pass `--port N` for another port, or `--port 0` for any free one"
            );
        }
        ExitCode::from(2)
    })
}

/// Prints where to go, then serves until the process is stopped.
fn serve<S: ServeSession + Send>(
    listener: &TcpListener,
    header: &str,
    model: &str,
    session: S,
) -> Result<(), ExitCode> {
    let address = listener.local_addr().map_err(|e| {
        eprintln!("mettle serve: cannot read the listening address: {e}");
        ExitCode::from(2)
    })?;

    let mut assets = StaticAssets::default();
    let index = stub_index_html(model, header);
    assets.add("/", HTML, index.clone().into_bytes());
    assets.add("/index.html", HTML, index.into_bytes());

    crate::write_stdout(format!(
        "mettle serve: listening on http://{address}\n\
         mettle serve: provider socket at ws://{address}{WS_PATH}\n\
         mettle serve: press Ctrl-C to stop\n"
    ))?;

    let session = Mutex::new(session);
    // Events go to stderr so that the URL above stays the only thing on stdout
    // a script has to parse (STYLE E3: this is the crate that renders).
    let report = |event: &ServeEvent<'_>| match event {
        ServeEvent::Connected => eprintln!("mettle serve: a client connected"),
        ServeEvent::Disconnected => eprintln!("mettle serve: a client disconnected"),
        ServeEvent::Served { target, status } if *status != 200 => {
            eprintln!("mettle serve: {status} {target}");
        }
        ServeEvent::Served { .. } => {}
        ServeEvent::Failed { context, detail } => {
            eprintln!("mettle serve: failure {context}: {detail}");
        }
    };
    Provider::new(&assets, &session, &report).accept_loop(listener);
    Ok(())
}

/// The one content type the stub page needs; mt-075 will add more.
const HTML: &str = "text/html; charset=utf-8";
