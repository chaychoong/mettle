//! `backend-instrument` — the ADR-0019 stage-1 instrument (mt-089).
//!
//! Runs a **named worklist of commands** through mettle's ordinary pipeline
//! (resolve → universe → bounds → lower → translate) and measures what deciding
//! each one costs, so "how much of the `over_budget` tail is genuinely hard"
//! becomes a measurement instead of a guess. Not shipped product: `dist = false`
//! like every other bin in this crate. It was also feature-gated until mt-121
//! (ADR-0027 retired the `cadical-instrument` feature with the optional
//! backend), so it now builds with the workspace.
//!
//! ```text
//! backend-instrument --rows worklist.txt \
//!     --conflicts 100000 --encode 64000000 --wall 600 --jobs 8 --out rows.json
//! backend-instrument --rows - --certify --jobs 8 --out certified.json
//! ```
//!
//! Two arms. The **measurement arm** (the default) solves each row under a
//! conflict budget and an optional `--wall` deadline — the one place a
//! wall-clock limit exists at all, and it can only produce a non-verdict, never
//! a verdict (STYLE D1/D4) — and reports CNF size, conflicts spent, and the time
//! each phase took, bucketed exactly as the solve gauge buckets it.
//!
//! `--certify` is the **proof-certification arm**
//! ([ADR-0027](../../../docs/adr/0027-cadical-only-solver.md) decision 4,
//! mt-123): each row is encoded, written out as DIMACS, and solved by CaDiCaL
//! logging a **DRAT proof**, which an external checker then verifies against
//! that exact CNF. A proof that does not check is stop-the-line — the run exits
//! nonzero and keeps the artifacts. What it certifies is precise: *this CNF is
//! unsatisfiable*. Whether the CNF is the right encoding of the Alloy command is
//! still the self-check's and the jar's job, and no proof can speak to it. It
//! replaced a cross-backend arm that ran every row on two solvers and failed on
//! any verdict difference — the check that caught the mt-090 latent wrong
//! verdict — which mt-124 deleted with the second solver.
//!
//! Neither arm handles a **temporal** command: the temporal pipeline is a
//! per-length sweep rather than one translate, so there is no single CNF a
//! single proof could refute, and no single solve to measure. Those rows are
//! screened out and reported as `temporal_out_of_scope` — typed, never silently
//! mismeasured.
//!
//! Three certify outcomes are visible in the report but are *not* failures, and
//! the distinction is deliberate. A `sat` row means the worklist named something
//! that is not UNSAT (a mispiped bucket, or drift since the sweep that produced
//! it) — a finding to look at, not a broken proof. An `unknown` row spent its
//! conflict budget, so there is no verdict to certify. A `checker_timeout` row
//! hit the checker deadline, which says nothing about the proof either way —
//! exactly like a spent budget. Only a proof the checker *refuses*, a checker
//! that cannot run, and a certificate that cannot be produced fail the run.
//!
//! A row is a gauge key: `<workspace-relative path>[<command index>]`. Each row
//! is classified into exactly one of the buckets the solve gauge uses, so the
//! table lines up with the mt-088 census it is measured against. `--rows -` reads
//! the worklist from stdin, so a slice can be piped straight out of a sweep
//! artifact (see CONTRIBUTING).
//!
//! Determinism: the report is sorted by row key and carries no wall-clock
//! **in the verdicts** — the `*_ms` fields are measurements, printed and
//! recorded as such (STYLE D1/D4).

#![allow(
    clippy::doc_markdown,
    reason = "\"CaDiCaL\" is the solver's own spelling — a proper noun with internal \
              capitals, which doc_markdown mistakes for an unlinked item path"
)]

use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

use std::time::Duration;

use als_conform::drat_check::{self, CheckerStatus};
use als_conform::solve_gauge::baseline::{load_baselines, Baseline, JarVerdict};
use als_core::instrument::{
    certify_goal, solve_goal_instrumented, CertifyError, CertifyOutcome, InstrumentOutcome,
    InstrumentVerdict,
};
use als_core::ir::Ir;
use als_core::{compute_bounds, compute_universe, lower_command, SolveOptions, TranslateError};
use als_types::{is_temporal_model, FilesystemLoader, ModuleGraph};

/// Everything one run needs, parsed from `argv`.
#[allow(
    clippy::struct_excessive_bools,
    reason = "these are CLI flags parsed one-for-one, not a state machine: `certify` \
              selects the arm, while `allow_overflow` and `keep_artifacts` are \
              independent knobs. Folding them into an enum would rename the flags in \
              the code without making any state unrepresentable"
)]
struct Config {
    rows: Vec<(String, usize)>,
    /// `--certify`: log a DRAT proof for each UNSAT verdict and have an external
    /// checker verify it, instead of only measuring the solve.
    certify: bool,
    /// The external DRAT checker (`--checker`), default
    /// `tools/drat-trim/drat-trim` under `--root`.
    checker: PathBuf,
    /// Hard deadline for one checker run (`--checker-timeout`). Wall-clock, and
    /// an instrument knob only: a row that outlives it is a non-answer, never a
    /// refused proof.
    checker_timeout: Duration,
    /// Where per-row `.cnf`/`.drat`/`.check.txt` artifacts land
    /// (`--work-dir`), default a process-unique directory under the system temp
    /// dir.
    work_dir: PathBuf,
    /// `--keep-artifacts`: never delete a row's files. Off by default because a
    /// 264-row audit at a 1M-conflict budget writes proofs by the gigabyte;
    /// artifacts of a row that did **not** certify are kept either way.
    keep_artifacts: bool,
    /// Primary-variable ceiling (`--primary-var-cap`), mirroring the solve
    /// gauge's own so a certify run skips exactly the rows the sweep skipped.
    primary_var_cap: usize,
    conflicts: u64,
    encode: u64,
    wall_secs: Option<f32>,
    /// Symmetry-breaking predicate cap. `None` = the jar default (20, forced
    /// to 0 by `expect 1`); an explicit value overrides both — the knob that
    /// separates "the SBP is unsound here" from "the core encoding is wrong"
    /// when a verdict disagreement shows up.
    symmetry: Option<u32>,
    /// LEDGER-001 overflow regime: `false` (default, and the jar's
    /// `noOverflow=true`) excludes overflowing instances, `true` wraps. A knob
    /// because an int-encoding over-constraint shows up as exactly this
    /// difference.
    allow_overflow: bool,
    jobs: usize,
    root: PathBuf,
    baselines: PathBuf,
    out: Option<PathBuf>,
}

/// One measured row, as it lands in the JSON artifact.
struct Row {
    key: String,
    bucket: String,
    verdict: Option<InstrumentVerdict>,
    jar: Option<JarVerdict>,
    agreement: &'static str,
    outcome: Option<InstrumentOutcome>,
    secs: f64,
    /// `--certify` only: what became of this row's certificate.
    certify: Option<CertifyArm>,
}

/// The certification arm of a `--certify` row. The row's `bucket` carries the
/// status ([`CheckerStatus::name`] and its siblings); this carries what a reader
/// needs to act on it.
struct CertifyArm {
    /// Bytes of DRAT CaDiCaL logged — `0` when no proof was produced.
    proof_bytes: u64,
    /// Wall milliseconds the external checker ran — `0` when it did not run.
    checker_ms: u128,
    /// The checker's own last word, or the failure that stopped the row.
    detail: String,
    /// Whether this row must fail the run.
    fatal: bool,
}

impl CertifyArm {
    /// The arm of a row that produced no certificate and nothing to say about
    /// one.
    fn none() -> Self {
        CertifyArm {
            proof_bytes: 0,
            checker_ms: 0,
            detail: String::new(),
            fatal: false,
        }
    }
}

fn main() {
    let cfg = match parse_args() {
        Ok(cfg) => cfg,
        Err(msg) => {
            eprintln!("backend-instrument: {msg}");
            std::process::exit(2);
        }
    };
    // A missing or unrunnable checker is a setup problem, not a finding, and it
    // is worth exactly zero solves: fail before the first row rather than after
    // the first proof, the same posture the gauge takes toward a missing jar.
    if cfg.certify {
        if let Err(msg) = drat_check::ensure_usable(&cfg.checker) {
            eprintln!("backend-instrument: {msg}");
            std::process::exit(2);
        }
        if let Err(e) = std::fs::create_dir_all(&cfg.work_dir) {
            eprintln!(
                "backend-instrument: cannot create work dir {}: {e}",
                cfg.work_dir.display()
            );
            std::process::exit(2);
        }
    }
    let baseline = load_baselines(&cfg.baselines);
    let rows = run(&cfg, &baseline);
    print_table(&cfg, &rows);
    if let Some(path) = &cfg.out {
        if let Err(e) = write_json(path, &cfg, &rows) {
            eprintln!("backend-instrument: writing {}: {e}", path.display());
            std::process::exit(1);
        }
    }
    if cfg.certify && !cfg.keep_artifacts {
        // Non-recursive on purpose: it succeeds exactly when every row cleaned
        // up after itself, and leaves the directory (with its evidence) alone
        // when a row did not.
        let _ = std::fs::remove_dir(&cfg.work_dir);
    }
    // Two findings are bugs rather than measurements, and the exit code says so
    // (a CI job or a shell `&&` must be able to tell): a SAT answer that fails
    // its own self-check, and a DRAT proof the checker would not verify.
    // Everything else — defers, over-budget rows, jar disagreements, checker
    // deadlines — is data this tool exists to collect, so it exits 0.
    let self_check = rows.iter().filter(|r| row_self_check_failed(r)).count();
    let uncertified = rows
        .iter()
        .filter(|r| r.certify.as_ref().is_some_and(|c| c.fatal))
        .count();
    if self_check + uncertified > 0 {
        eprintln!(
            "backend-instrument: FAILED — {self_check} self-check failure(s), \
             {uncertified} uncertified proof(s)"
        );
        if uncertified > 0 && !cfg.keep_artifacts {
            eprintln!(
                "backend-instrument: artifacts of the failing row(s) kept in {}",
                cfg.work_dir.display()
            );
        }
        std::process::exit(1);
    }
}

/// Whether a row's SAT answer failed to re-evaluate against its own goal — a
/// mettle bug, always.
fn row_self_check_failed(row: &Row) -> bool {
    row.outcome
        .as_ref()
        .is_some_and(|o| o.self_check_fail.is_some())
}

/// Parses `argv`; every flag is required to be well-formed (a typo in a budget
/// would silently change what the run measures).
#[allow(clippy::too_many_lines, reason = "flat flag parsing, one arm per flag")]
fn parse_args() -> Result<Config, String> {
    let mut rows_path: Option<PathBuf> = None;
    let mut certify = false;
    // `None` until a flag says otherwise: the budget defaults differ per arm
    // (the certify arm reproduces the *gauge's* run, not this bin's older
    // calibration defaults), and that can only be resolved once the arm is
    // known — which is after the whole of `argv` has been read.
    let mut conflicts: Option<u64> = None;
    let mut encode: Option<u64> = None;
    let mut wall_secs: Option<f32> = Some(600.0);
    let mut wall_given = false;
    let mut symmetry: Option<u32> = None;
    let mut allow_overflow = false;
    let mut jobs: usize = 1;
    let mut root = PathBuf::from(".");
    let mut baselines: Option<PathBuf> = None;
    let mut out: Option<PathBuf> = None;
    let mut checker: Option<PathBuf> = None;
    let mut checker_timeout: u64 = 600;
    let mut work_dir: Option<PathBuf> = None;
    let mut keep_artifacts = false;
    let mut primary_var_cap: usize = 20_000;

    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        let mut value = || args.next().ok_or_else(|| format!("{arg} needs a value"));
        match arg.as_str() {
            "--rows" => rows_path = Some(PathBuf::from(value()?)),
            "--conflicts" => {
                conflicts = Some(value()?.parse().map_err(|_| "--conflicts: not a number")?);
            }
            "--encode" => encode = Some(value()?.parse().map_err(|_| "--encode: not a number")?),
            "--wall" => {
                let secs: f32 = value()?.parse().map_err(|_| "--wall: not a number")?;
                wall_secs = if secs > 0.0 { Some(secs) } else { None };
                wall_given = true;
            }
            "--symmetry" => {
                symmetry = Some(value()?.parse().map_err(|_| "--symmetry: not a number")?);
            }
            "--certify" => certify = true,
            "--checker" => checker = Some(PathBuf::from(value()?)),
            "--checker-timeout" => {
                checker_timeout = value()?
                    .parse()
                    .map_err(|_| "--checker-timeout: not a number of seconds")?;
            }
            "--work-dir" => work_dir = Some(PathBuf::from(value()?)),
            "--keep-artifacts" => keep_artifacts = true,
            "--primary-var-cap" => {
                primary_var_cap = value()?
                    .parse()
                    .map_err(|_| "--primary-var-cap: not a number")?;
            }
            "--allow-overflow" => allow_overflow = true,
            "--jobs" => jobs = value()?.parse().map_err(|_| "--jobs: not a number")?,
            "--root" => root = PathBuf::from(value()?),
            "--baselines" => baselines = Some(PathBuf::from(value()?)),
            "--out" => out = Some(PathBuf::from(value()?)),
            other => return Err(format!("unknown flag {other:?}")),
        }
    }
    // The two arms answer different questions: refusing a flag that belongs to
    // the other one beats silently ignoring it, which is how a report ends up
    // labelled as something it did not measure.
    if certify && wall_given {
        return Err(
            "--certify has no solver wall limit — the conflict budget bounds the solve and \
             --checker-timeout bounds the check"
                .to_owned(),
        );
    }
    let rows_path = rows_path.ok_or("--rows is required")?;
    // `--rows -` reads stdin, so a worklist can be piped straight from whatever
    // produced it (a jq/python filter over a sweep artifact, a `grep` over a
    // report) without a temp file in between. That is the difference between the
    // cross-backend arm being reused and being re-derived every session.
    let text = if rows_path == Path::new("-") {
        let mut buf = String::new();
        std::io::Read::read_to_string(&mut std::io::stdin(), &mut buf)
            .map_err(|e| format!("reading rows from stdin: {e}"))?;
        buf
    } else {
        std::fs::read_to_string(&rows_path)
            .map_err(|e| format!("reading {}: {e}", rows_path.display()))?
    };
    let mut rows = Vec::new();
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        rows.push(parse_key(line)?);
    }
    let baselines = baselines.unwrap_or_else(|| root.join("baselines"));
    let checker = checker.unwrap_or_else(|| root.join("tools/drat-trim/drat-trim"));
    // Process-unique so two concurrent audits cannot overwrite each other's
    // proofs; the directory is removed at the end unless something was left in
    // it for a reader to look at.
    let work_dir = work_dir.unwrap_or_else(|| {
        std::env::temp_dir().join(format!("mettle-certify-{}", std::process::id()))
    });
    Ok(Config {
        rows,
        certify,
        checker,
        checker_timeout: Duration::from_secs(checker_timeout),
        work_dir,
        keep_artifacts,
        primary_var_cap,
        // The certify arm reproduces the solve gauge's own run so its verdicts
        // are the sweep's verdicts, not a differently-budgeted rerun of them.
        conflicts: conflicts.unwrap_or(if certify { 1_000_000 } else { 100_000 }),
        encode: encode.unwrap_or(if certify { 256_000_000 } else { 64_000_000 }),
        // Nothing in the certify arm honors a solver wall limit (`certify_goal`
        // is bounded by conflicts alone), so the header must not claim one.
        wall_secs: if certify { None } else { wall_secs },
        symmetry,
        allow_overflow,
        jobs: jobs.max(1),
        root,
        baselines,
        out,
    })
}

/// Splits a gauge key `path/to/model.als[7]` into its parts.
fn parse_key(key: &str) -> Result<(String, usize), String> {
    let open = key
        .rfind('[')
        .ok_or_else(|| format!("row {key:?} is not `path[idx]`"))?;
    let close = key
        .strip_suffix(']')
        .ok_or_else(|| format!("row {key:?} is not `path[idx]`"))?;
    let idx: usize = close[open + 1..]
        .parse()
        .map_err(|_| format!("row {key:?} has a non-numeric index"))?;
    Ok((key[..open].to_owned(), idx))
}

/// Runs every row, `jobs` at a time, and returns them in worklist order.
fn run(cfg: &Config, baseline: &Baseline) -> Vec<Row> {
    let slots: Vec<Mutex<Option<Row>>> = cfg.rows.iter().map(|_| Mutex::new(None)).collect();
    let next = AtomicUsize::new(0);
    let done = AtomicUsize::new(0);
    let total = cfg.rows.len();
    std::thread::scope(|scope| {
        for _ in 0..cfg.jobs.min(total.max(1)) {
            scope.spawn(|| loop {
                let i = next.fetch_add(1, Ordering::SeqCst);
                if i >= total {
                    return;
                }
                let (path, idx) = &cfg.rows[i];
                eprintln!("  start {path}[{idx}]");
                let _ = std::io::stderr().flush();
                let started = std::time::Instant::now();
                let row = measure_row(cfg, baseline, path, *idx, i, started);
                let finished = done.fetch_add(1, Ordering::SeqCst) + 1;
                eprintln!(
                    "  [{finished}/{total}] {} → {} ({:.1}s)",
                    row.key, row.bucket, row.secs
                );
                let _ = std::io::stderr().flush();
                if let Ok(mut slot) = slots[i].lock() {
                    *slot = Some(row);
                }
            });
        }
    });
    slots
        .into_iter()
        .filter_map(|s| s.into_inner().ok().flatten())
        .collect()
}

/// Resolves, lowers and solves one row.
///
/// `ordinal` is the row's position in the worklist, used only to name its
/// certify artifacts: sanitizing a gauge key into a filename is lossy (two keys
/// can sanitize to the same string), and one row silently overwriting another's
/// proof would make the checker verify the wrong pair.
fn measure_row(
    cfg: &Config,
    baseline: &Baseline,
    relpath: &str,
    idx: usize,
    ordinal: usize,
    started: std::time::Instant,
) -> Row {
    let key = format!("{relpath}[{idx}]");
    let jar = baseline.lookup(relpath, idx);
    let finish = |bucket: &str,
                  verdict: Option<InstrumentVerdict>,
                  outcome: Option<InstrumentOutcome>| Row {
        key: key.clone(),
        bucket: bucket.to_owned(),
        verdict,
        jar,
        agreement: agreement(verdict, jar),
        outcome,
        secs: started.elapsed().as_secs_f64(),
        certify: None,
    };

    let Some((graph, world)) = resolve(&cfg.root.join(relpath)) else {
        return finish("resolve_failed", None, None);
    };
    let Some(command) = world.commands.get(idx) else {
        return finish("no_such_command", None, None);
    };
    if is_temporal_model(&world, &graph, command) {
        // The temporal pipeline is a per-length sweep, not a single translate;
        // out of scope for a stage-1 verdict instrument, and typed rather than
        // silently mismeasured.
        return finish("temporal_out_of_scope", None, None);
    }
    let Ok(scoped) = compute_universe(&world, &graph, command) else {
        return finish("mettle_defer:scope", None, None);
    };
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &scoped, &mut ir);
    let expect_one = matches!(command.expect, Some(als_syntax::ast::Expect::Sat));
    let opts = SolveOptions {
        allow_overflow: cfg.allow_overflow,
        conflict_budget: Some(cfg.conflicts),
        encode_budget: Some(cfg.encode),
        symmetry: cfg.symmetry.unwrap_or(if expect_one { 0 } else { 20 }),
        ..SolveOptions::default()
    };
    let goal = match lower_command(&world, &graph, &scoped, &bounds, &mut ir, idx) {
        Ok(g) => g,
        Err(e) => return finish(&format!("mettle_defer:lower:{e}"), None, None),
    };
    let bucket_of = |verdict: InstrumentVerdict| match verdict {
        InstrumentVerdict::Unknown => "mettle_defer:over_budget".to_owned(),
        v => format!("answered_{}", v.name()),
    };
    if cfg.certify {
        let lowered = Lowered {
            ir: &ir,
            scoped: &scoped,
            goal: &goal,
            bounds: &bounds,
            opts: &opts,
        };
        let certified = certify_row(cfg, &lowered, &key, ordinal);
        let mut row = finish(&certified.bucket, certified.verdict, certified.outcome);
        row.certify = Some(certified.arm);
        return row;
    }
    match solve_goal_instrumented(&ir, &scoped, &goal, &bounds, &opts, cfg.wall_secs) {
        Ok(outcome) => finish(
            &bucket_of(outcome.verdict),
            Some(outcome.verdict),
            Some(outcome),
        ),
        Err(TranslateError::CapacityExceeded { .. }) => finish("mettle_defer:capacity", None, None),
        Err(_) => finish("mettle_defer:encode", None, None),
    }
}

/// One lowered command, ready to certify — the five pieces `certify_goal` needs,
/// bundled so the call site stays a call site.
struct Lowered<'a> {
    ir: &'a Ir,
    scoped: &'a als_core::ScopedUniverse,
    goal: &'a als_core::LoweredGoal,
    bounds: &'a als_core::BoundsResult,
    opts: &'a SolveOptions,
}

/// What certifying one row produced: the row fields it fills in, plus its
/// certify arm.
struct Certified {
    bucket: String,
    verdict: Option<InstrumentVerdict>,
    outcome: Option<InstrumentOutcome>,
    arm: CertifyArm,
}

impl Certified {
    /// A row that reached no verdict: a defer, or a certificate that could not
    /// be produced.
    fn skipped(bucket: &str, detail: String, fatal: bool) -> Self {
        Certified {
            bucket: bucket.to_owned(),
            verdict: None,
            outcome: None,
            arm: CertifyArm {
                proof_bytes: 0,
                checker_ms: 0,
                detail,
                fatal,
            },
        }
    }
}

/// The three files one certified row writes, named from its worklist position
/// and its gauge key.
///
/// The ordinal is what makes the names unique — sanitizing a key into a filename
/// is lossy, and two rows writing the same `.drat` would have the checker verify
/// one row's proof against another row's CNF, which is the one way this
/// instrument could report a false `NOT_CERTIFIED`.
struct Artifacts {
    cnf: PathBuf,
    proof: PathBuf,
    log: PathBuf,
}

impl Artifacts {
    fn new(work_dir: &Path, ordinal: usize, key: &str) -> Self {
        let mut stem = format!("{ordinal:04}-");
        for ch in key.chars() {
            stem.push(match ch {
                'a'..='z' | 'A'..='Z' | '0'..='9' | '.' | '-' => ch,
                _ => '_',
            });
        }
        Artifacts {
            cnf: work_dir.join(format!("{stem}.cnf")),
            proof: work_dir.join(format!("{stem}.drat")),
            log: work_dir.join(format!("{stem}.check.txt")),
        }
    }

    /// Deletes whatever of the three exists. Called as soon as a row's files
    /// have done their job: a 264-row audit at the gauge's 1M-conflict budget
    /// writes proofs by the gigabyte, and keeping all of them to the end of the
    /// run is how an audit fills a disk.
    fn discard(&self) {
        let _ = std::fs::remove_file(&self.cnf);
        let _ = std::fs::remove_file(&self.proof);
        let _ = std::fs::remove_file(&self.log);
    }
}

/// Encodes and proves one row, then hands its certificate to the checker.
fn certify_row(cfg: &Config, lowered: &Lowered<'_>, key: &str, ordinal: usize) -> Certified {
    // The gauge skips a command whose primary-variable count is over the cap
    // before it ever encodes; a certify run that did not would be auditing rows
    // the sweep never produced a verdict for.
    let primaries: usize = lowered
        .bounds
        .bounds
        .iter()
        .map(|(_, b)| b.upper().len() - b.lower().len())
        .sum();
    if primaries > cfg.primary_var_cap {
        return Certified::skipped("mettle_defer:primary_var_cap", String::new(), false);
    }

    let files = Artifacts::new(&cfg.work_dir, ordinal, key);
    let measured = match certify_goal(
        lowered.ir,
        lowered.scoped,
        lowered.goal,
        lowered.bounds,
        lowered.opts,
        &files.cnf,
        &files.proof,
    ) {
        Err(CertifyError::Translate(TranslateError::CapacityExceeded { .. })) => {
            return Certified::skipped("mettle_defer:capacity", String::new(), false)
        }
        Err(CertifyError::Translate(_)) => {
            return Certified::skipped("mettle_defer:encode", String::new(), false)
        }
        // A certificate that could not even be started is a broken instrument,
        // not a finding about the row — but an audit that cannot produce
        // certificates is not an audit, so it still stops the line.
        Err(e @ (CertifyError::ProofTrace(_) | CertifyError::CnfWrite { .. })) => {
            return Certified::skipped("CERTIFY_FAILED", e.to_string(), true)
        }
        Ok(CertifyOutcome::TriviallyUnsat) => {
            let detail = "unsatisfiable at encode time; no CNF, no proof".to_owned();
            let mut trivial = Certified::skipped("certified_trivial", detail, false);
            trivial.verdict = Some(InstrumentVerdict::Unsat);
            return trivial;
        }
        Ok(measured) => measured,
    };
    check_certificate(cfg, &files, measured)
}

/// Turns one solved row into its report entry, running the external checker
/// when — and only when — there is a proof of unsatisfiability to check.
fn check_certificate(cfg: &Config, files: &Artifacts, measured: CertifyOutcome) -> Certified {
    let verdict = match measured {
        CertifyOutcome::Unsat(_) => InstrumentVerdict::Unsat,
        CertifyOutcome::Sat(_) => InstrumentVerdict::Sat,
        CertifyOutcome::Unknown(_) => InstrumentVerdict::Unknown,
        CertifyOutcome::TriviallyUnsat => {
            unreachable!("a trivially-unsat row writes no files and never reaches the checker")
        }
    };
    let outcome = measured.measurements().map(|m| InstrumentOutcome {
        verdict,
        num_vars: m.num_vars,
        num_clauses: m.num_clauses,
        conflicts_used: Some(m.conflicts_used),
        encode_ms: m.encode_ms,
        solve_ms: m.solve_ms,
        // Certification never decodes a model: the answer it is about is UNSAT,
        // and a SAT row here is reported rather than examined.
        self_check_fail: None,
    });
    let finish = |bucket: &str, arm: CertifyArm| Certified {
        bucket: bucket.to_owned(),
        verdict: Some(verdict),
        outcome,
        arm,
    };

    let CertifyOutcome::Unsat(_) = measured else {
        // SAT and budget-exhausted rows leave nothing worth keeping: DRAT
        // expresses unsatisfiability, so a partial proof of neither refutes
        // anything.
        if !cfg.keep_artifacts {
            files.discard();
        }
        let bucket = if verdict == InstrumentVerdict::Sat {
            "sat"
        } else {
            "unknown"
        };
        return finish(bucket, CertifyArm::none());
    };

    // Read before the checker runs and before anything is deleted — the size of
    // the certificate is a measurement the report keeps even when the file is
    // not.
    let proof_bytes = std::fs::metadata(&files.proof).map_or(0, |m| m.len());
    let report = drat_check::verify(
        &cfg.checker,
        &files.cnf,
        &files.proof,
        &files.log,
        cfg.checker_timeout,
    );
    // A row that did **not** certify keeps its files regardless of
    // `--keep-artifacts` — that is precisely the row someone will want to look
    // at, and a deadline is a reason to re-run it with a longer one.
    if report.status == CheckerStatus::Verified && !cfg.keep_artifacts {
        files.discard();
    }
    finish(
        report.status.name(),
        CertifyArm {
            proof_bytes,
            checker_ms: report.elapsed_ms,
            detail: report.detail,
            fatal: report.status.is_fatal(),
        },
    )
}

/// The stop-the-line comparison: a backend answer against the banked jar
/// verdict.
fn agreement(verdict: Option<InstrumentVerdict>, jar: Option<JarVerdict>) -> &'static str {
    match (verdict, jar) {
        (Some(InstrumentVerdict::Sat), Some(JarVerdict::Sat))
        | (Some(InstrumentVerdict::Unsat), Some(JarVerdict::Unsat)) => "agree",
        (Some(InstrumentVerdict::Sat), Some(JarVerdict::Unsat))
        | (Some(InstrumentVerdict::Unsat), Some(JarVerdict::Sat)) => "DISAGREE",
        (Some(InstrumentVerdict::Sat | InstrumentVerdict::Unsat), Some(JarVerdict::Nonverdict)) => {
            "jar_nonverdict"
        }
        (Some(InstrumentVerdict::Sat | InstrumentVerdict::Unsat), None) => "no_baseline",
        _ => "no_answer",
    }
}

/// Loads and resolves one `.als` file.
fn resolve(path: &Path) -> Option<(ModuleGraph, als_types::ResolvedWorld)> {
    let loader = FilesystemLoader::new();
    let canon = std::fs::canonicalize(path).ok()?;
    let root = canon.to_string_lossy().replace('\\', "/");
    let graph = ModuleGraph::load(&root, &loader).ok()?;
    let world = als_types::resolve(&graph).ok()?.world;
    Some((graph, world))
}

/// The human-readable table (stdout).
fn print_table(cfg: &Config, rows: &[Row]) {
    if cfg.certify {
        println!(
            "certify conflicts={} encode={} primary_var_cap={} checker={} timeout={}s rows={}",
            cfg.conflicts,
            cfg.encode,
            cfg.primary_var_cap,
            cfg.checker.display(),
            cfg.checker_timeout.as_secs(),
            rows.len()
        );
    } else {
        println!(
            "backend={} conflicts={} encode={} wall={:?} rows={}",
            als_core::Backend::default().name(),
            cfg.conflicts,
            cfg.encode,
            cfg.wall_secs,
            rows.len()
        );
    }
    // The certify arm adds the two columns that are the point of running it: the
    // size of the certificate and the time the checker took over it.
    println!(
        "{:<72} {:<26} {:<10} {:>9} {:>12} {:>12} {:>10}{}",
        "row",
        "bucket",
        "jar",
        "secs",
        "vars",
        "clauses",
        "conflicts",
        if cfg.certify {
            format!(" {:>10} {:>9}", "proof_kb", "check_ms")
        } else {
            String::new()
        }
    );
    for row in rows {
        let outcome = row.outcome.as_ref();
        println!(
            "{:<72} {:<26} {:<10} {:>9.1} {:>12} {:>12} {:>10}{}",
            row.key,
            row.bucket,
            match row.jar {
                Some(JarVerdict::Sat) => "sat",
                Some(JarVerdict::Unsat) => "unsat",
                Some(JarVerdict::Nonverdict) => "nonverdict",
                None => "-",
            },
            row.secs,
            outcome.map_or(0, |o| o.num_vars as usize),
            outcome.map_or(0, |o| o.num_clauses),
            outcome
                .and_then(|o| o.conflicts_used)
                .map_or_else(|| "-".to_owned(), |c| c.to_string()),
            row.certify.as_ref().map_or_else(String::new, |c| format!(
                " {:>10} {:>9}",
                c.proof_bytes / 1024,
                c.checker_ms
            )),
        );
    }
    print_summary(cfg, rows);
}

/// The run's bottom line: what got answered, and the findings that are bugs
/// rather than data (jar disagreement, self-check failure, and — in the certify
/// arm — a proof that would not check).
fn print_summary(cfg: &Config, rows: &[Row]) {
    let answered = rows.iter().filter(|r| r.verdict.is_some()).count();
    let stuck = rows
        .iter()
        .filter(|r| r.verdict == Some(InstrumentVerdict::Unknown))
        .count();
    let disagree: Vec<&str> = rows
        .iter()
        .filter(|r| r.agreement == "DISAGREE")
        .map(|r| r.key.as_str())
        .collect();
    let self_check: Vec<&str> = rows
        .iter()
        .filter(|r| row_self_check_failed(r))
        .map(|r| r.key.as_str())
        .collect();
    println!(
        "\nanswered {} / {} (still stuck {stuck}) · DISAGREE {} · self-check failures {}",
        answered - stuck,
        rows.len(),
        disagree.len(),
        self_check.len()
    );
    for key in disagree {
        println!("  DISAGREE: {key}");
    }
    for key in self_check {
        println!("  SELF-CHECK FAIL: {key}");
    }
    if cfg.certify {
        print_certify_summary(rows);
    }
}

/// The certify arm's bottom line: how many rows are now machine-certified, and
/// every row that is not, with what the checker said about it.
fn print_certify_summary(rows: &[Row]) {
    // Counted per bucket in a fixed order rather than by iterating a map, so the
    // summary is byte-identical run to run (STYLE D2/D5).
    let buckets = [
        "certified",
        "certified_trivial",
        "sat",
        "unknown",
        "checker_timeout",
        "NOT_CERTIFIED",
        "CHECKER_FAILED",
        "CERTIFY_FAILED",
        "temporal_out_of_scope",
    ];
    let count = |bucket: &str| rows.iter().filter(|r| r.bucket == bucket).count();
    let tally: Vec<String> = buckets
        .iter()
        .filter(|b| count(b) > 0)
        .map(|b| format!("{b} {}", count(b)))
        .collect();
    // Whatever the fixed list does not name — the defer buckets, resolve
    // failures — is still accounted for, so the numbers always add up to the
    // worklist.
    let named: usize = buckets.iter().map(|b| count(b)).sum();
    let other = rows.len() - named;
    println!(
        "certify: {} · other {other} · total {}",
        tally.join(" · "),
        rows.len()
    );
    let proved = count("certified") + count("certified_trivial");
    println!(
        "certify: {proved} of {} rows are machine-certified UNSAT",
        rows.len()
    );
    for row in rows {
        if let Some(arm) = &row.certify {
            if arm.fatal {
                println!("  {}: {} — {}", row.bucket, row.key, arm.detail);
            }
        }
    }
}

/// Writes the JSON artifact by hand — this bin has no serde dependency and the
/// shape is four scalar fields per row.
fn write_json(path: &Path, cfg: &Config, rows: &[Row]) -> std::io::Result<()> {
    use std::fmt::Write as _;

    let mut s = String::new();
    s.push_str("{\n");
    let _ = writeln!(
        s,
        "  \"backend\": \"{}\",",
        if cfg.certify {
            "certify"
        } else {
            als_core::Backend::default().name()
        }
    );
    let _ = writeln!(s, "  \"conflicts\": {},", cfg.conflicts);
    let _ = writeln!(s, "  \"encode_budget\": {},", cfg.encode);
    let _ = writeln!(
        s,
        "  \"wall_secs\": {},",
        cfg.wall_secs
            .map_or_else(|| "null".to_owned(), |w| format!("{w}"))
    );
    if cfg.certify {
        let _ = writeln!(
            s,
            "  \"primary_var_cap\": {}, \"checker\": \"{}\", \"checker_timeout_secs\": {},",
            cfg.primary_var_cap,
            cfg.checker.display().to_string().escape_debug(),
            cfg.checker_timeout.as_secs()
        );
    }
    s.push_str("  \"rows\": [\n");
    for (i, row) in rows.iter().enumerate() {
        let outcome = row.outcome.as_ref();
        let _ = write!(
            s,
            concat!(
                "    {{\"key\": \"{}\", \"bucket\": \"{}\", \"verdict\": \"{}\", ",
                "\"jar\": \"{}\", \"agreement\": \"{}\", \"secs\": {:.2}, ",
                "\"vars\": {}, \"clauses\": {}, \"encode_ms\": {}, \"solve_ms\": {}, ",
                "\"conflicts_used\": {}, \"self_check_fail\": {}{}}}{}\n"
            ),
            row.key,
            row.bucket,
            row.verdict.map_or("-", InstrumentVerdict::name),
            match row.jar {
                Some(JarVerdict::Sat) => "sat",
                Some(JarVerdict::Unsat) => "unsat",
                Some(JarVerdict::Nonverdict) => "nonverdict",
                None => "-",
            },
            row.agreement,
            row.secs,
            outcome.map_or(0, |o| o.num_vars as usize),
            outcome.map_or(0, |o| o.num_clauses),
            outcome.map_or(0, |o| o.encode_ms),
            outcome.map_or(0, |o| o.solve_ms),
            outcome
                .and_then(|o| o.conflicts_used)
                .map_or_else(|| "null".to_owned(), |c| c.to_string()),
            outcome
                .and_then(|o| o.self_check_fail.as_deref())
                .map_or_else(
                    || "null".to_owned(),
                    |f| format!("\"{}\"", f.escape_debug())
                ),
            row.certify.as_ref().map_or_else(String::new, |c| format!(
                ", \"proof_bytes\": {}, \"checker_ms\": {}, \"checker_said\": \"{}\"",
                c.proof_bytes,
                c.checker_ms,
                c.detail.escape_debug()
            )),
            if i + 1 == rows.len() { "" } else { "," },
        );
    }
    s.push_str("  ]\n}\n");
    std::fs::write(path, s)
}
