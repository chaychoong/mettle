//! mt-024 `bench`: the jar-side runner.
//!
//! Drives `ResolveGaugeShim` directly (batch pass: one JVM over the whole
//! file list; cold pass: one fresh JVM per sampled file) rather than
//! through [`crate::shim`]'s `OracleShim` protocol -- that's a different
//! program with a different wire format and a deliberate one-file-per-JVM
//! design (see `shim.rs`'s module doc), unsuited to batch timing. This
//! module reuses `shim.rs`'s compile step
//! ([`crate::shim::compile_java_shim`]) and its pipe-drain/timeout helpers
//! ([`crate::shim::read_all`]/[`crate::shim::wait_with_timeout`]) rather
//! than duplicating them.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::{Command as ProcessCommand, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;
use std::time::{Duration, Instant};

use crate::error::ConformError;
use crate::shim::{compile_java_shim, read_all, wait_with_timeout, WaitResult};

const CLASS_NAME: &str = "ResolveGaugeShim";

/// One file's parsed verdict line from the shim's JSON-Lines output: the
/// mt-020 fields it already emitted (`file`, `ok`) plus mt-024's two
/// additive fields (`phase`, `nanos`).
pub(crate) struct JarLine {
    pub file: String,
    pub ok: bool,
    /// `"parse"` | `"resolve"`, present only when `ok` is false.
    pub phase: Option<String>,
    /// This file's own `parseEverything_fromFile` wall time inside the
    /// JVM, excluding JVM startup (which happens once, before the first
    /// line).
    pub nanos: u64,
}

/// Compiles `ResolveGaugeShim.java` (idempotent, cached by
/// [`compile_java_shim`]) and returns the `classes:jar` classpath to run
/// it with.
///
/// # Errors
/// [`ConformError::JarNotFound`]/[`ConformError::ShimSourceNotFound`]/
/// [`ConformError::ShimCompile`] as [`compile_java_shim`], or
/// [`ConformError::JvmFailed`] if the classpath can't be assembled.
pub(crate) fn ensure_compiled(
    jar_path: &Path,
    shim_source: &Path,
    classes_dir: &Path,
) -> Result<OsString, ConformError> {
    let classes = compile_java_shim(jar_path, shim_source, classes_dir, CLASS_NAME)?;
    std::env::join_paths([absolutize(&classes), absolutize(jar_path)]).map_err(|e| {
        ConformError::JvmFailed {
            class_name: CLASS_NAME.to_string(),
            message: format!("could not build classpath: {e}"),
        }
    })
}

fn absolutize(path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir().map_or_else(|_| path.to_path_buf(), |cwd| cwd.join(path))
    }
}

/// Runs the batch pass: one JVM, `ResolveGaugeShim <filelist>`, over every
/// file in `files` (already-absolutized paths, in the order the caller
/// wants the output in -- the shim preserves input order exactly). Returns
/// the parsed per-file lines plus the whole-process wall-clock (Rust-side
/// `Instant`, includes the one JVM startup -- this is the "amortized
/// startup" batch total).
///
/// # Errors
/// [`ConformError::JvmTimeout`]/[`ConformError::JvmFailed`] on process
/// failure, or [`ConformError::Io`] writing the scratch file list.
pub(crate) fn run_batch(
    classpath: &OsString,
    files: &[PathBuf],
    timeout: Duration,
) -> Result<(Vec<JarLine>, Duration), ConformError> {
    let scratch = fresh_scratch_dir("batch");
    std::fs::create_dir_all(&scratch)?;
    let filelist = scratch.join("filelist.txt");
    let contents = files
        .iter()
        .map(|p| p.to_string_lossy().into_owned())
        .collect::<Vec<_>>()
        .join("\n");
    std::fs::write(&filelist, contents)?;

    let run_result = run_java(
        classpath,
        &[filelist.as_os_str().to_os_string()],
        &scratch,
        timeout,
    );
    let _ = std::fs::remove_dir_all(&scratch);
    let (stdout, elapsed) = run_result?;

    Ok((parse_jsonl(&stdout)?, elapsed))
}

/// Runs the cold pass: one fresh JVM per file in `sample` (already
/// absolutized), each given its own one-line file list. Returns
/// `(file, whole_process_wall_clock)` pairs in `sample` order -- this
/// wall-clock includes that invocation's own JVM startup, by design (the
/// point of the cold pass is to make startup visible).
///
/// # Errors
/// As [`run_batch`].
pub(crate) fn run_cold(
    classpath: &OsString,
    sample: &[PathBuf],
    timeout: Duration,
) -> Result<Vec<(PathBuf, Duration)>, ConformError> {
    let mut out = Vec::with_capacity(sample.len());
    for (i, file) in sample.iter().enumerate() {
        let scratch = fresh_scratch_dir(&format!("cold-{i}"));
        std::fs::create_dir_all(&scratch)?;
        let filelist = scratch.join("filelist.txt");
        std::fs::write(&filelist, file.to_string_lossy().as_ref())?;

        let run_result = run_java(
            classpath,
            &[filelist.as_os_str().to_os_string()],
            &scratch,
            timeout,
        );
        let _ = std::fs::remove_dir_all(&scratch);
        let (_stdout, elapsed) = run_result?;
        out.push((file.clone(), elapsed));
    }
    Ok(out)
}

static RUN_COUNTER: AtomicU64 = AtomicU64::new(0);

/// A scratch working directory unique to this process, this run, and this
/// tag, derived from the PID and a monotonic counter rather than
/// wall-clock time (STYLE D4) -- mirrors `shim.rs`'s `fresh_scratch_dir`,
/// duplicated because that one is private to the `OracleShim` protocol
/// path and hard-codes no tag.
fn fresh_scratch_dir(tag: &str) -> PathBuf {
    let n = RUN_COUNTER.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!(
        "als-conform-bench-{}-{tag}-{n}",
        std::process::id()
    ))
}

/// Spawns `java -cp <classpath> ResolveGaugeShim <args...>` in `cwd`,
/// drains stdout/stderr on background threads (avoids a full-pipe
/// deadlock against the timeout poll -- same reasoning as `shim.rs`'s
/// `spawn_and_capture`), and returns stdout plus the whole-process
/// wall-clock.
fn run_java(
    classpath: &OsString,
    args: &[OsString],
    cwd: &Path,
    timeout: Duration,
) -> Result<(String, Duration), ConformError> {
    let start = Instant::now();
    let mut command = ProcessCommand::new("java");
    command
        .current_dir(cwd)
        .arg("-cp")
        .arg(classpath)
        .arg(CLASS_NAME)
        .args(args)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());

    let mut child = command.spawn().map_err(|source| ConformError::Spawn {
        program: "java",
        file: PathBuf::from(CLASS_NAME),
        source,
    })?;

    let Some(stdout) = child.stdout.take() else {
        let _ = child.kill();
        return Err(ConformError::JvmFailed {
            class_name: CLASS_NAME.to_string(),
            message: "child java process had no stdout pipe".to_string(),
        });
    };
    let Some(stderr) = child.stderr.take() else {
        let _ = child.kill();
        return Err(ConformError::JvmFailed {
            class_name: CLASS_NAME.to_string(),
            message: "child java process had no stderr pipe".to_string(),
        });
    };

    let stdout_reader = thread::spawn(move || read_all(stdout));
    let stderr_reader = thread::spawn(move || read_all(stderr));

    let wait_result = wait_with_timeout(&mut child, timeout);
    let stdout_text = stdout_reader.join().unwrap_or_default();
    let stderr_text = stderr_reader.join().unwrap_or_default();
    let elapsed = start.elapsed();

    match wait_result {
        WaitResult::Exited => {
            if stdout_text.trim().is_empty() {
                return Err(ConformError::JvmFailed {
                    class_name: CLASS_NAME.to_string(),
                    message: format!("no output on stdout; stderr:\n{stderr_text}"),
                });
            }
            Ok((stdout_text, elapsed))
        }
        WaitResult::TimedOut => Err(ConformError::JvmTimeout {
            class_name: CLASS_NAME.to_string(),
            timeout,
        }),
        WaitResult::WaitError(message) => Err(ConformError::JvmFailed {
            class_name: CLASS_NAME.to_string(),
            message,
        }),
    }
}

fn parse_jsonl(text: &str) -> Result<Vec<JarLine>, ConformError> {
    let mut out = Vec::new();
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let v: serde_json::Value =
            serde_json::from_str(line).map_err(|e| ConformError::JvmFailed {
                class_name: CLASS_NAME.to_string(),
                message: format!("malformed shim output line: {e}\nline: {line}"),
            })?;
        let file = v
            .get("file")
            .and_then(|f| f.as_str())
            .ok_or_else(|| ConformError::JvmFailed {
                class_name: CLASS_NAME.to_string(),
                message: format!("shim output line missing `file`: {line}"),
            })?
            .to_owned();
        let ok = v
            .get("ok")
            .and_then(serde_json::Value::as_bool)
            .unwrap_or(false);
        let phase = v.get("phase").and_then(|p| p.as_str()).map(str::to_owned);
        let nanos = v
            .get("nanos")
            .and_then(serde_json::Value::as_u64)
            .unwrap_or(0);
        out.push(JarLine {
            file,
            ok,
            phase,
            nanos,
        });
    }
    Ok(out)
}
