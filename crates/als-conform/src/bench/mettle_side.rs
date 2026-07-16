//! mt-024 `bench`: the mettle-side stage runner.
//!
//! Two stages, matching the CLAUDE-spec vocabulary exactly:
//! - **parse** — `als_syntax::parse` alone (lex + cook + parse; the front
//!   end).
//! - **resolve** — `als_types::ModuleGraph::load_with_source` +
//!   `als_types::resolve` (module-graph loading, which itself parses every
//!   transitively-`open`ed file, plus name resolution/type checking). This
//!   is mettle's full-pipeline verdict up to Rung 2, and the one directly
//!   comparable to the jar's fused `parseEverything_fromFile` verdict.
//!
//! Both stages reuse the verdict bucketing `resolve_gauge.rs`'s
//! `mettle_verdict` established (accept/parse/load/resolve/panic) --
//! duplicated rather than imported, because `resolve_gauge` is a binary
//! (`src/bin/`), not library surface this crate can depend on.

use std::panic::{self, AssertUnwindSafe};
use std::path::{Path, PathBuf};
use std::thread;
use std::time::{Duration, Instant};

use als_syntax::ArenaId as _;
use als_types::{FilesystemLoader, ModuleGraph, ResolveError};

/// One file's verdict from a single mettle pipeline stage.
#[derive(Debug, Clone, Copy)]
pub(crate) struct StageVerdict {
    pub ok: bool,
    /// `"accept"` | `"parse"` | `"load"` | `"resolve"` | `"panic"`.
    pub phase: &'static str,
}

impl StageVerdict {
    fn accept() -> Self {
        Self {
            ok: true,
            phase: "accept",
        }
    }

    fn panicked() -> Self {
        Self {
            ok: false,
            phase: "panic",
        }
    }
}

/// One file's timed result for one stage (in the caller's file-list
/// order, not carried here -- callers zip against their own file list).
/// `elapsed` is wall-clock (`Instant`), so under `--threads > 1` it
/// reflects real scheduling contention, not isolated single-core cost --
/// `bench`'s text output documents this rather than hiding it.
pub(crate) struct FileStageResult {
    pub verdict: StageVerdict,
    pub elapsed: Duration,
}

/// The result of one full (warm-up + timed) stage pass: the timed
/// per-file results, in the input file order, plus the timed pass's own
/// wall-clock total (the number directly comparable to the jar's
/// one-JVM batch total -- summing per-file `elapsed` would overcount
/// under parallelism, since files run concurrently).
pub(crate) struct StageRun {
    pub results: Vec<FileStageResult>,
    pub wall_total: Duration,
}

/// Runs mettle's front end (lex + cook + parse, `als_syntax::parse`) on
/// one file's source, catching panics so one adversarial input can't
/// abort the batch (mirrors `resolve_gauge.rs`'s `catch_unwind` use).
fn parse_stage(source: &str) -> StageVerdict {
    let result = panic::catch_unwind(AssertUnwindSafe(|| {
        als_syntax::parse(source, als_syntax::FileId::from_index(0))
    }));
    match result {
        Ok(Ok(_)) => StageVerdict::accept(),
        Ok(Err(_)) => StageVerdict {
            ok: false,
            phase: "parse",
        },
        Err(_) => StageVerdict::panicked(),
    }
}

/// Runs mettle's module-load + resolve/typecheck stage on one file, given
/// its root `path` (used for `open` resolution; must already be the
/// on-disk path `FilesystemLoader` reads sibling opens from) and owned
/// `source`.
fn resolve_stage(path: &str, source: String, loader: &FilesystemLoader) -> StageVerdict {
    let result = panic::catch_unwind(AssertUnwindSafe(|| {
        match ModuleGraph::load_with_source(path, source, loader) {
            Ok(graph) => match als_types::resolve(&graph) {
                Ok(_) => StageVerdict::accept(),
                Err(_) => StageVerdict {
                    ok: false,
                    phase: "resolve",
                },
            },
            Err(ResolveError::OpenedFileParse { .. }) => StageVerdict {
                ok: false,
                phase: "parse",
            },
            Err(_) => StageVerdict {
                ok: false,
                phase: "load",
            },
        }
    }));
    result.unwrap_or_else(|_| StageVerdict::panicked())
}

/// Runs one stage over `files` twice -- once discarded (warms the page
/// cache and allocator; per the bead spec, "run the set once untimed
/// first") and once timed -- split across `threads` worker threads
/// (static chunking: the ~167-file corpus is far too small for
/// work-stealing to matter). `run_one` receives each file's path and an
/// **owned** clone of its source, cloned by the caller just before
/// starting that file's timer, so the source-clone itself never pollutes
/// the measured stage cost.
///
/// Per-file results come back in `files` order regardless of how work was
/// chunked (STYLE D5: parallelism must not affect results).
fn run_stage_twice<F>(files: &[(PathBuf, String)], threads: usize, run_one: F) -> StageRun
where
    F: Fn(&Path, String) -> StageVerdict + Sync,
{
    let _ = run_stage_once(files, threads, &run_one); // warm-up, discarded
    run_stage_once(files, threads, &run_one)
}

fn run_stage_once<F>(files: &[(PathBuf, String)], threads: usize, run_one: &F) -> StageRun
where
    F: Fn(&Path, String) -> StageVerdict + Sync,
{
    let n = files.len();
    let n_threads = threads.max(1).min(n.max(1));
    let chunk = n.div_ceil(n_threads.max(1));

    let wall_start = Instant::now();
    let mut indexed: Vec<(usize, FileStageResult)> = thread::scope(|scope| {
        let mut handles = Vec::new();
        for t in 0..n_threads {
            let lo = t * chunk;
            let hi = ((t + 1) * chunk).min(n);
            if lo >= hi {
                continue;
            }
            let slice = &files[lo..hi];
            let run_one = &run_one;
            handles.push(scope.spawn(move || {
                let mut out = Vec::with_capacity(hi - lo);
                for (offset, (path, source)) in slice.iter().enumerate() {
                    let owned_source = source.clone();
                    let start = Instant::now();
                    let verdict = run_one(path, owned_source);
                    let elapsed = start.elapsed();
                    out.push((lo + offset, FileStageResult { verdict, elapsed }));
                }
                out
            }));
        }
        let mut all = Vec::new();
        for h in handles {
            all.extend(h.join().unwrap_or_default());
        }
        all
    });
    let wall_total = wall_start.elapsed();

    indexed.sort_by_key(|(idx, _)| *idx);
    StageRun {
        results: indexed.into_iter().map(|(_, r)| r).collect(),
        wall_total,
    }
}

/// Runs the `parse` stage (warm-up + timed) over `files` (path, source).
pub(crate) fn run_parse_stage(files: &[(PathBuf, String)], threads: usize) -> StageRun {
    run_stage_twice(files, threads, |_path, source| parse_stage(&source))
}

/// Runs the `resolve` stage (warm-up + timed) over `files` (path, source).
/// `path` must be the real on-disk path (canonicalized) so sibling `open`s
/// in the 167-file corpus resolve correctly, matching
/// `resolve_gauge paths`'s use of `FilesystemLoader`.
pub(crate) fn run_resolve_stage(files: &[(PathBuf, String)], threads: usize) -> StageRun {
    let loader = FilesystemLoader::new();
    run_stage_twice(files, threads, move |path, source| {
        resolve_stage(&path.to_string_lossy(), source, &loader)
    })
}
