//! Drives `OracleShim` as a subprocess: compiles it on demand, spawns one
//! JVM per `.als` file, enforces a per-file timeout, and hands the
//! captured stdout to [`crate::parse::parse_shim_output`].
//!
//! Runs the JVM with a fresh temp working directory per invocation
//! (`current_dir`), because the jar litters output directories named
//! after the model into its CWD (docs/reference/alloy6-reference.md).

use std::ffi::OsString;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Child, Command as ProcessCommand, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;
use std::time::{Duration, Instant};

use crate::config::{EnumerationCap, OracleConfig};
use crate::error::ConformError;
use crate::model::{FileOutcome, FileResult, ShimErrorKind};
use crate::parse::parse_shim_output;

/// Compiles `OracleShim.java` against the reference jar if the cached
/// `.class` is missing or older than the source, and returns the class
/// directory to run it from. Idempotent and cheap to call once per batch.
///
/// # Errors
/// Returns [`ConformError::JarNotFound`]/[`ConformError::ShimSourceNotFound`]
/// if the configured paths don't exist, [`ConformError::Spawn`] if `javac`
/// can't be launched at all, or [`ConformError::ShimCompile`] if `javac`
/// runs but reports a failure.
pub fn ensure_shim_compiled(cfg: &OracleConfig) -> Result<PathBuf, ConformError> {
    if !cfg.jar_path.is_file() {
        return Err(ConformError::JarNotFound(cfg.jar_path.clone()));
    }
    if !cfg.shim_source.is_file() {
        return Err(ConformError::ShimSourceNotFound(cfg.shim_source.clone()));
    }

    let class_file = cfg.shim_classes_dir.join("OracleShim.class");
    let up_to_date = matches!(
        (mtime(&class_file), mtime(&cfg.shim_source)),
        (Some(class_time), Some(src_time)) if class_time >= src_time
    );

    if !up_to_date {
        std::fs::create_dir_all(&cfg.shim_classes_dir)?;
        let output = ProcessCommand::new("javac")
            .arg("-cp")
            .arg(&cfg.jar_path)
            .arg("-d")
            .arg(&cfg.shim_classes_dir)
            .arg(&cfg.shim_source)
            .output()
            .map_err(|source| ConformError::Spawn {
                program: "javac",
                file: cfg.shim_source.clone(),
                source,
            })?;
        if !output.status.success() {
            return Err(ConformError::ShimCompile(
                String::from_utf8_lossy(&output.stderr).into_owned(),
            ));
        }
    }
    Ok(cfg.shim_classes_dir.clone())
}

fn mtime(path: &Path) -> Option<std::time::SystemTime> {
    std::fs::metadata(path).ok()?.modified().ok()
}

/// Makes `path` absolute against the current process's cwd, without
/// requiring the path to exist (unlike `fs::canonicalize`) -- the model
/// file argument may legitimately not exist (a caller passing a bad path
/// should see the shim's own "file not found" error, not a Rust-side
/// substitution).
fn absolutize(path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir().map_or_else(|_| path.to_path_buf(), |cwd| cwd.join(path))
    }
}

/// Runs the oracle over one `.als` file and returns a structured result.
/// This function always returns a value -- I/O failures, timeouts, and
/// malformed shim output are all folded into `FileOutcome` rather than
/// propagated as `Err` (STYLE E2/E3: this is the "never panics, never
/// returns a wrong answer" boundary; only genuinely un-recoverable setup
/// problems, handled by [`ensure_shim_compiled`] before this is called,
/// are `Err`).
///
/// `shim_classes` must already be populated by [`ensure_shim_compiled`].
#[must_use]
pub fn run_oracle_on_file(
    cfg: &OracleConfig,
    shim_classes: &Path,
    file: &Path,
    cap: EnumerationCap,
) -> FileResult {
    let outcome = run_and_parse(cfg, shim_classes, file, cap);
    FileResult {
        file: file.to_path_buf(),
        outcome,
    }
}

/// Runs the oracle over a set of files and aggregates a [`crate::scorecard::Scorecard`].
///
/// Files are de-duplicated and sorted by path before running (`PathBuf`'s
/// `Ord` is lexicographic component-by-component -- STYLE C2/C3's
/// required ordering guarantee), so the resulting scorecard's file order
/// is deterministic regardless of input order.
///
/// # Errors
/// Propagates [`ensure_shim_compiled`]'s errors: if the shim can't be
/// compiled at all, no individual file run can proceed either.
pub fn run_oracle_on_files(
    cfg: &OracleConfig,
    files: &[PathBuf],
    cap: EnumerationCap,
) -> Result<crate::scorecard::Scorecard, ConformError> {
    let shim_classes = ensure_shim_compiled(cfg)?;

    let mut sorted_files: Vec<PathBuf> = files.to_vec();
    sorted_files.sort();
    sorted_files.dedup();

    let results = sorted_files
        .iter()
        .map(|file| run_oracle_on_file(cfg, &shim_classes, file, cap))
        .collect();

    Ok(crate::scorecard::Scorecard::new(results))
}

fn run_and_parse(
    cfg: &OracleConfig,
    shim_classes: &Path,
    file: &Path,
    cap: EnumerationCap,
) -> FileOutcome {
    // The JVM runs with `current_dir` set to a scratch dir (see module
    // doc), so any relative path handed to it -- classpath entries or the
    // model file itself -- must be absolutized against *our* cwd first,
    // or `java` resolves them against the scratch dir instead and fails
    // to find its own classes.
    let classpath =
        match std::env::join_paths([absolutize(shim_classes), absolutize(&cfg.jar_path)]) {
            Ok(cp) => cp,
            Err(e) => {
                return FileOutcome::Error {
                    kind: ShimErrorKind::Protocol,
                    message: format!("could not build classpath: {e}"),
                }
            }
        };
    let file = absolutize(file);

    match spawn_and_capture(cfg, &classpath, &file, cap) {
        SpawnOutcome::Timeout => FileOutcome::Timeout,
        SpawnOutcome::Error(message) => FileOutcome::Error {
            kind: ShimErrorKind::Protocol,
            message,
        },
        SpawnOutcome::Completed { stdout, stderr } => {
            let outcome = parse_shim_output(&stdout);
            // A protocol failure (no parseable output at all) is far more
            // diagnosable with the JVM's stderr attached -- stdout alone
            // just says "empty".
            if let FileOutcome::Error {
                kind: ShimErrorKind::Protocol,
                message,
            } = outcome
            {
                if !stderr.trim().is_empty() {
                    return FileOutcome::Error {
                        kind: ShimErrorKind::Protocol,
                        message: format!("{message}\nstderr:\n{stderr}"),
                    };
                }
                return FileOutcome::Error {
                    kind: ShimErrorKind::Protocol,
                    message,
                };
            }
            outcome
        }
    }
}

enum SpawnOutcome {
    Completed { stdout: String, stderr: String },
    Timeout,
    Error(String),
}

static RUN_COUNTER: AtomicU64 = AtomicU64::new(0);

/// A scratch working directory unique to this process and this run,
/// derived from the PID and a monotonic counter rather than wall-clock
/// time (STYLE D4: no wall-clock in the pipeline) -- it never influences
/// any recorded result, only where the jar is allowed to litter.
fn fresh_scratch_dir() -> PathBuf {
    let n = RUN_COUNTER.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!("als-conform-run-{}-{n}", std::process::id()))
}

fn spawn_and_capture(
    cfg: &OracleConfig,
    classpath: &OsString,
    file: &Path,
    cap: EnumerationCap,
) -> SpawnOutcome {
    let scratch_dir = fresh_scratch_dir();
    if let Err(e) = std::fs::create_dir_all(&scratch_dir) {
        return SpawnOutcome::Error(format!("could not create scratch working directory: {e}"));
    }

    let mut command = ProcessCommand::new("java");
    command
        .current_dir(&scratch_dir)
        .arg("-cp")
        .arg(classpath)
        .arg("OracleShim")
        .arg(file)
        .arg(cfg.symmetry.to_string())
        .arg(cfg.no_overflow.to_string())
        .arg(&cfg.solver)
        .arg(cap.shim_arg())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());

    let mut child = match command.spawn() {
        Ok(c) => c,
        Err(e) => {
            let _ = std::fs::remove_dir_all(&scratch_dir);
            return SpawnOutcome::Error(format!("failed to spawn java: {e}"));
        }
    };

    let Some(stdout) = child.stdout.take() else {
        let _ = child.kill();
        let _ = std::fs::remove_dir_all(&scratch_dir);
        return SpawnOutcome::Error("child java process had no stdout pipe".to_string());
    };
    let Some(stderr) = child.stderr.take() else {
        let _ = child.kill();
        let _ = std::fs::remove_dir_all(&scratch_dir);
        return SpawnOutcome::Error("child java process had no stderr pipe".to_string());
    };

    // Drain both pipes on background threads while the main thread polls
    // for exit/timeout below -- otherwise a full pipe buffer could
    // deadlock the child against a timeout we're trying to enforce.
    let stdout_reader = thread::spawn(move || read_all(stdout));
    let stderr_reader = thread::spawn(move || read_all(stderr));

    let wait_result = wait_with_timeout(&mut child, cfg.timeout);

    let stdout_text = stdout_reader.join().unwrap_or_default();
    let stderr_text = stderr_reader.join().unwrap_or_default();
    let _ = std::fs::remove_dir_all(&scratch_dir);

    match wait_result {
        WaitResult::Exited => SpawnOutcome::Completed {
            stdout: stdout_text,
            stderr: stderr_text,
        },
        WaitResult::TimedOut => SpawnOutcome::Timeout,
        WaitResult::WaitError(message) => SpawnOutcome::Error(message),
    }
}

fn read_all(mut pipe: impl Read) -> String {
    let mut buf = String::new();
    let _ = pipe.read_to_string(&mut buf);
    buf
}

enum WaitResult {
    Exited,
    TimedOut,
    WaitError(String),
}

/// Polls `child` until it exits or `timeout` elapses; on timeout, kills
/// and reaps the child.
fn wait_with_timeout(child: &mut Child, timeout: Duration) -> WaitResult {
    const POLL_INTERVAL: Duration = Duration::from_millis(20);
    let start = Instant::now();
    loop {
        match child.try_wait() {
            Ok(Some(_status)) => return WaitResult::Exited,
            Ok(None) => {
                if start.elapsed() >= timeout {
                    let _ = child.kill();
                    let _ = child.wait();
                    return WaitResult::TimedOut;
                }
                thread::sleep(POLL_INTERVAL);
            }
            Err(e) => {
                // Can't determine child status; give up rather than spin
                // forever, but keep this distinct from a real timeout.
                let _ = child.kill();
                return WaitResult::WaitError(format!("failed to poll child status: {e}"));
            }
        }
    }
}
