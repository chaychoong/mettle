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
    compute_bounds, compute_universe, lower_command, solve_goal, SolveOptions, SolveVerdict,
};
use als_syntax::ast::{CmdKind, Expect, ExprId, Para, ParaName};
use als_types::{
    resolve, CmdTargetResolved, FilesystemLoader, ModuleGraph, ModuleId, Resolved, ResolvedCommand,
    ResolvedWorld,
};

/// Parsed `mettle exec` invocation, or a bare help request.
enum ParsedArgs<'a> {
    /// `-h`/`--help` — usage already printed; caller exits 0.
    Help,
    Run {
        path: &'a str,
        command_sel: Option<&'a str>,
        opts: SolveOptions,
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

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "-h" | "--help" => {
                crate::print_usage();
                return Ok(ParsedArgs::Help);
            }
            "--allow-overflow" => allow_overflow = true,
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
    })
}

pub(crate) fn run_exec(args: &[String]) -> Result<(), ExitCode> {
    let (path, command_sel, opts) = match parse_args(args)? {
        ParsedArgs::Help => return Ok(()),
        ParsedArgs::Run {
            path,
            command_sel,
            opts,
        } => (path, command_sel, opts),
    };

    let (graph, resolved) = load_and_resolve(path)?;
    let world = &resolved.world;

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

/// Reads, loads (`open`s and all), and resolves `path` — the same
/// error-rendering path `run_check` uses (E3/E5): a lex/parse/resolve
/// failure is never this command's business to reinterpret, it's the same
/// caret diagnostic `mettle check` would print.
fn load_and_resolve(path: &str) -> Result<(ModuleGraph, Resolved), ExitCode> {
    let source = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("mettle exec: cannot read {path}: {e}");
            return Err(ExitCode::from(2));
        }
    };

    let loader = FilesystemLoader::new();
    let graph = match ModuleGraph::load_with_source(path, source.clone(), &loader) {
        Ok(graph) => graph,
        Err(err) => {
            crate::render_load_error(path, &source, &err);
            return Err(ExitCode::from(1));
        }
    };

    let resolved = match resolve(&graph) {
        Ok(resolved) => resolved,
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
    for warning in &resolved.warnings {
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
    Ok((graph, resolved))
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

    let scoped = match compute_universe(world, graph, cmd) {
        Ok(s) => s,
        Err(e) => {
            let _ = writeln!(out, "CANNOT EXECUTE: {e}\n");
            return true;
        }
    };

    let mut ir = Ir::default();
    let bounds = compute_bounds(world, &scoped, &mut ir);
    let goal = match lower_command(world, graph, &scoped, &bounds, &mut ir, idx) {
        Ok(g) => g,
        Err(e) => {
            let _ = writeln!(out, "CANNOT EXECUTE: {e}\n");
            return true;
        }
    };

    let verdict = match solve_goal(&ir, &scoped, &goal, &bounds, opts) {
        Ok(v) => v,
        Err(e) => {
            let _ = writeln!(out, "CANNOT EXECUTE: {e}\n");
            return true;
        }
    };

    // Polarity (als-core/src/solve.rs module docs): a `check`'s goal is
    // already negated at lowering, so `Sat` there *is* a counterexample.
    let (is_sat, mut failed) = match &verdict {
        SolveVerdict::Sat(inst) => {
            let label = match cmd.kind {
                CmdKind::Run => "SAT",
                CmdKind::Check => "COUNTEREXAMPLE",
            };
            let _ = writeln!(out, "{label}");
            out.push_str(&render_instance(&ir, inst));
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
