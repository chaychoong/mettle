//! Per-row JSONL progress telemetry for `solve-gauge --progress-jsonl` (mt-094).
//!
//! An **observability side channel**, the same carve-out `status.rs` (this
//! crate's owner-facing status monitor) documents: wall-clock (`ts_ms`) is
//! fine here because nothing here reaches [`super::report`]. `run_gauge`
//! calls [`TelemetrySink::emit`] only from spots that already exist for
//! other reasons — the phase-B completion hook, `compute_command`'s start
//! heartbeat — so a sink threads through without moving a byte of the
//! deterministic report (STYLE D1/D4; the report-parity gate lives in
//! `als-conform/tests/solve_gauge_integration.rs`).
//!
//! One JSON object per line, flushed after every write, so a mid-run
//! `SIGKILL` leaves a file whose last line is either whole or missing —
//! never half-written-and-trusted. `crate::solve_gauge::watch` is the
//! reader: it re-parses the whole file on every `/data` poll and drops any
//! line that fails to deserialize, which in practice is at most the torn
//! last one.
//!
//! Four event kinds, one per run phase:
//! - [`RunStartEvent`] — once, before dispatch: the run's config and the
//!   full ordered row list (`{i, key}`), so a dashboard's grid is read from
//!   the run rather than hardcoded to a corpus size.
//! - [`RowStartEvent`] — when a row's compute actually begins on a worker
//!   (mirrors the existing start heartbeat in
//!   [`super::execute::compute_command`]).
//! - [`RowDoneEvent`] — when a row finishes; may arrive in **completion**
//!   order (it rides `parallel_fold_ordered`'s `on_result` hook, which the
//!   module doc of `parallel.rs` states fires in completion order), so a
//!   reader keys on `i`, never on arrival order.
//! - [`RunDoneEvent`] — once, after the fold.

use std::collections::BTreeMap;
use std::fs::File;
use std::io::{BufWriter, Write as _};
use std::path::Path;
use std::sync::Mutex;
use std::time::{SystemTime, UNIX_EPOCH};

use serde::{Deserialize, Serialize};

/// One row's identity in the sweep's grid order (file-sorted,
/// index-ascending — the same order [`super::execute::command_items`]
/// builds and [`super::fold_command`] folds in).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RowId {
    /// Position in the run's ordered row list — the grid index.
    pub i: usize,
    /// `relpath[idx]` (see [`super::sweep_baseline::command_key`]).
    pub key: String,
}

/// Emitted once, before phase-B dispatch: the config fields that decide what
/// a bucket means, plus the whole grid a dashboard renders.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RunStartEvent {
    pub ts_ms: u64,
    /// The scheduling mode this run measures (see
    /// [`super::sweep_baseline::mode_key`]) — what `watch` joins historical
    /// wall times on, so a stage-1 row is never compared against a
    /// counting-net baseline time.
    pub mode: String,
    pub solver: String,
    pub jobs: usize,
    pub conflict_budget: u64,
    pub encode_budget: u64,
    pub primary_var_cap: usize,
    pub symmetry: u32,
    pub count: bool,
    pub count_symmetry: u32,
    /// The whole grid, in order — a dashboard reads its shape from here,
    /// never from a hardcoded corpus size.
    pub rows: Vec<RowId>,
}

/// Emitted when a row's compute actually begins on a worker.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RowStartEvent {
    pub ts_ms: u64,
    pub i: usize,
    pub key: String,
}

/// Emitted when a row finishes (completion order — see the module doc).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RowDoneEvent {
    pub ts_ms: u64,
    pub i: usize,
    pub key: String,
    /// The verdict-stage bucket (`CmdRecord::verdict_bucket`).
    pub bucket: String,
    pub secs: f64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub disagreement: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub self_check_fail: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub panic_line: Option<String>,
}

/// Emitted once, after the fold.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RunDoneEvent {
    pub ts_ms: u64,
    pub total_secs: f64,
    pub verdict_buckets: BTreeMap<String, usize>,
}

/// One telemetry line. Internally tagged (`"event"`) so a JSONL line is
/// self-describing without a reader needing to know the field set of every
/// kind up front.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "event", rename_all = "snake_case")]
pub enum TelemetryEvent {
    RunStart(RunStartEvent),
    RowStart(RowStartEvent),
    RowDone(RowDoneEvent),
    RunDone(RunDoneEvent),
}

/// Wall-clock milliseconds since the Unix epoch. Telemetry-only (see the
/// module doc) — never reaches the deterministic report.
#[must_use]
pub fn now_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| u64::try_from(d.as_millis()).unwrap_or(u64::MAX))
}

/// A line-atomic JSONL sink. `row_start` fires from worker threads and the
/// others from the coordinator, so writes are serialized behind a `Mutex`
/// and each is flushed immediately: the failure mode this buys is a torn
/// *last* line on a hard kill, never a torn line mid-file.
#[derive(Debug)]
pub struct TelemetrySink {
    writer: Mutex<BufWriter<File>>,
}

impl TelemetrySink {
    /// Creates (truncating) the JSONL file at `path`.
    ///
    /// # Errors
    /// I/O failure opening the file.
    pub fn create(path: &Path) -> std::io::Result<Self> {
        let file = File::create(path)?;
        Ok(Self {
            writer: Mutex::new(BufWriter::new(file)),
        })
    }

    /// Writes one event as a line and flushes.
    ///
    /// Best-effort: a write failure (disk full, or a poisoned lock from a
    /// panic elsewhere while holding it) is swallowed rather than
    /// propagated — telemetry is an observability side channel and must
    /// never be able to fail the sweep it is watching (the same discipline
    /// `status.rs`'s `StatusFile` follows).
    pub fn emit(&self, event: &TelemetryEvent) {
        let Ok(mut w) = self.writer.lock() else {
            return;
        };
        let Ok(line) = serde_json::to_string(event) else {
            return;
        };
        let _ = writeln!(w, "{line}");
        let _ = w.flush();
    }
}

#[cfg(test)]
#[allow(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "test fixtures assert on known-good values"
)]
mod tests {
    use super::*;

    fn tmp_path(tag: &str) -> std::path::PathBuf {
        std::env::temp_dir().join(format!("als-telemetry-{tag}-{}.jsonl", std::process::id()))
    }

    fn row_done(i: usize, key: &str) -> TelemetryEvent {
        TelemetryEvent::RowDone(RowDoneEvent {
            ts_ms: 0,
            i,
            key: key.to_owned(),
            bucket: "agree_sat".to_owned(),
            secs: 0.1,
            disagreement: None,
            self_check_fail: None,
            panic_line: None,
        })
    }

    #[test]
    fn events_round_trip_through_json() {
        let ev = row_done(3, "a.als[0]");
        let json = serde_json::to_string(&ev).unwrap();
        assert!(json.contains("\"event\":\"row_done\""));
        assert!(!json.contains("disagreement"), "None fields are omitted");
        let back: TelemetryEvent = serde_json::from_str(&json).unwrap();
        match back {
            TelemetryEvent::RowDone(d) => {
                assert_eq!(d.i, 3);
                assert_eq!(d.key, "a.als[0]");
            }
            other => panic!("expected RowDone, got {other:?}"),
        }
    }

    #[test]
    fn a_run_start_round_trips_its_row_list() {
        let ev = TelemetryEvent::RunStart(RunStartEvent {
            ts_ms: 1,
            mode: "stage1".to_owned(),
            solver: "sat4j".to_owned(),
            jobs: 4,
            conflict_budget: 250_000,
            encode_budget: 64_000_000,
            primary_var_cap: 20_000,
            symmetry: 20,
            count: false,
            count_symmetry: 0,
            rows: vec![
                RowId {
                    i: 0,
                    key: "a.als[0]".to_owned(),
                },
                RowId {
                    i: 1,
                    key: "a.als[1]".to_owned(),
                },
            ],
        });
        let json = serde_json::to_string(&ev).unwrap();
        let back: TelemetryEvent = serde_json::from_str(&json).unwrap();
        match back {
            TelemetryEvent::RunStart(r) => assert_eq!(r.rows.len(), 2),
            other => panic!("expected RunStart, got {other:?}"),
        }
    }

    #[test]
    fn sink_writes_one_json_object_per_line() {
        let path = tmp_path("basic");
        std::fs::remove_file(&path).ok();
        let sink = TelemetrySink::create(&path).unwrap();
        sink.emit(&TelemetryEvent::RowStart(RowStartEvent {
            ts_ms: 1,
            i: 0,
            key: "a.als[0]".to_owned(),
        }));
        sink.emit(&row_done(0, "a.als[0]"));
        drop(sink);
        let text = std::fs::read_to_string(&path).unwrap();
        let lines: Vec<&str> = text.lines().collect();
        assert_eq!(lines.len(), 2);
        for line in &lines {
            let parsed: TelemetryEvent = serde_json::from_str(line).unwrap();
            assert!(matches!(
                parsed,
                TelemetryEvent::RowStart(_) | TelemetryEvent::RowDone(_)
            ));
        }
        std::fs::remove_file(&path).ok();
    }

    /// A sink written by multiple threads (mirroring `row_start` firing from
    /// worker threads while `row_done` fires on the coordinator) never
    /// interleaves two lines into one malformed one.
    #[test]
    fn concurrent_writers_produce_valid_one_object_per_line_jsonl() {
        let path = tmp_path("concurrent");
        std::fs::remove_file(&path).ok();
        let sink = TelemetrySink::create(&path).unwrap();
        std::thread::scope(|scope| {
            for t in 0..8usize {
                let sink = &sink;
                scope.spawn(move || {
                    for i in 0..50usize {
                        sink.emit(&row_done(t * 50 + i, &format!("m{t}.als[{i}]")));
                    }
                });
            }
        });
        let text = std::fs::read_to_string(&path).unwrap();
        let lines: Vec<&str> = text.lines().collect();
        assert_eq!(lines.len(), 400);
        for line in &lines {
            // Every line parses whole -- a torn/interleaved write would fail here.
            serde_json::from_str::<TelemetryEvent>(line).unwrap();
        }
        std::fs::remove_file(&path).ok();
    }

    /// The reader-side contract: a torn final line (a kill mid-write) must
    /// not stop the rest of the file from being read. The reader itself
    /// lives in `watch::data`; this pins the primitive it relies on.
    #[test]
    fn a_torn_final_line_is_droppable_without_losing_earlier_lines() {
        let path = tmp_path("torn");
        std::fs::write(
            &path,
            "{\"event\":\"row_start\",\"ts_ms\":1,\"i\":0,\"key\":\"a.als[0]\"}\n\
             {\"event\":\"row_done\",\"ts_ms\":2,\"i\":0,\"key\":\"a.als[0]\",\"bucket\":\"agree_sat\",\"secs\":0.1}\n\
             {\"event\":\"row_start\",\"ts_ms\":3,\"i\":1,\"key\":\"b.als[0",
        )
        .unwrap();
        let text = std::fs::read_to_string(&path).unwrap();
        let parsed: Vec<TelemetryEvent> = text
            .lines()
            .filter_map(|l| serde_json::from_str(l).ok())
            .collect();
        assert_eq!(parsed.len(), 2, "the torn tail must be dropped, not panic");
        std::fs::remove_file(&path).ok();
    }
}
