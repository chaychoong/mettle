//! Assembles `GET /data`: joins the live JSONL telemetry with the run's row
//! list and (optionally) historical baseline wall times.
//!
//! Re-reads the JSONL file in full on every call rather than keeping
//! server-side state incrementally updated. A sweep tops out in the low
//! thousands of rows (the corpus's whole command count), so re-parsing the
//! file every ~1s poll is cheap, and it sidesteps ever having to reconcile
//! this process's view with a file a completely different process (the
//! `solve-gauge` run) is concurrently appending to — the file is simply the
//! only state that matters, read fresh each time.

use std::collections::BTreeMap;
use std::path::Path;

use serde::Serialize;

use crate::solve_gauge::sweep_baseline::{mode_key, read_prior, SweepBaselineFile};
use crate::solve_gauge::telemetry::{
    self, RowDoneEvent, RowId, RunDoneEvent, RunStartEvent, TelemetryEvent,
};

/// One row as the dashboard renders it: the telemetry facts folded down to
/// "where is this command right now".
#[derive(Debug, Clone, Serialize)]
struct RowView {
    i: usize,
    key: String,
    /// `"pending"` | `"running"` | `"done"`.
    state: &'static str,
    #[serde(skip_serializing_if = "Option::is_none")]
    bucket: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    secs: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    started_ts_ms: Option<u64>,
    /// The same command's recorded wall time in the committed sweep
    /// baseline, joined on the run's own `mode` — never a different mode's
    /// time (mt-059's lesson: a stage-1 time is not a hint for a counting
    /// run, and it is not a fair comparison for one either).
    #[serde(skip_serializing_if = "Option::is_none")]
    hist_ms: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    disagreement: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    self_check_fail: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    panic_line: Option<String>,
}

/// The whole `/data` response body.
#[derive(Debug, Clone, Serialize)]
struct DataResponse {
    /// True until the JSONL file has a `run_start` event — lets `conform
    /// watch` be started before the sweep it is watching.
    waiting: bool,
    run: Option<RunStartEvent>,
    rows: Vec<RowView>,
    done: Option<RunDoneEvent>,
    /// So the page computes a running row's live elapsed from
    /// `server_ts_ms - started_ts_ms` rather than trusting its own clock.
    server_ts_ms: u64,
}

/// Builds the `/data` JSON body. Never fails outright: a missing/unreadable
/// JSONL file, or a torn/garbled tail line, degrades to a "waiting" payload
/// or fewer rows rather than an HTTP error — a dashboard watching a live
/// sweep must stay answering through all of that.
pub(super) fn assemble(jsonl_path: &Path, baseline_path: &Path) -> String {
    let server_ts_ms = telemetry::now_ms();
    let Ok(text) = std::fs::read_to_string(jsonl_path) else {
        let resp = DataResponse {
            waiting: true,
            run: None,
            rows: Vec::new(),
            done: None,
            server_ts_ms,
        };
        return render(&resp);
    };
    let events = parse_events(&text);
    let resp = fold_events(&events, baseline_path, server_ts_ms);
    render(&resp)
}

fn render(resp: &DataResponse) -> String {
    serde_json::to_string(resp).unwrap_or_else(|_| "{\"waiting\":true}".to_owned())
}

/// Parses every line that deserializes as a whole [`TelemetryEvent`]; a line
/// that does not (in practice, at most the final one, torn by a write this
/// read raced) is dropped rather than failing the whole read.
fn parse_events(text: &str) -> Vec<TelemetryEvent> {
    text.lines()
        .filter(|l| !l.trim().is_empty())
        .filter_map(|l| serde_json::from_str(l).ok())
        .collect()
}

/// Folds the event stream into the current row states, keyed by grid
/// position so `row_done`'s completion-order arrival (see `telemetry`'s
/// module doc) never scrambles the grid.
fn fold_events(events: &[TelemetryEvent], baseline_path: &Path, server_ts_ms: u64) -> DataResponse {
    let mut run = None;
    let mut done = None;
    let mut rows: BTreeMap<usize, RowView> = BTreeMap::new();

    for event in events {
        match event {
            TelemetryEvent::RunStart(r) => {
                for RowId { i, key } in &r.rows {
                    rows.insert(
                        *i,
                        RowView {
                            i: *i,
                            key: key.clone(),
                            state: "pending",
                            bucket: None,
                            secs: None,
                            started_ts_ms: None,
                            hist_ms: None,
                            disagreement: None,
                            self_check_fail: None,
                            panic_line: None,
                        },
                    );
                }
                run = Some(r.clone());
            }
            TelemetryEvent::RowStart(s) => {
                if let Some(row) = rows.get_mut(&s.i) {
                    row.state = "running";
                    row.started_ts_ms = Some(s.ts_ms);
                }
            }
            TelemetryEvent::RowDone(d) => apply_row_done(&mut rows, d),
            TelemetryEvent::RunDone(r) => done = Some(r.clone()),
        }
    }

    if let Some(r) = &run {
        if let Some(baseline) = read_prior(baseline_path) {
            join_hist_ms(&mut rows, &baseline, &r.mode);
        }
    }

    DataResponse {
        waiting: run.is_none(),
        run,
        rows: rows.into_values().collect(),
        done,
        server_ts_ms,
    }
}

fn apply_row_done(rows: &mut BTreeMap<usize, RowView>, d: &RowDoneEvent) {
    let row = rows.entry(d.i).or_insert_with(|| RowView {
        i: d.i,
        key: d.key.clone(),
        state: "pending",
        bucket: None,
        secs: None,
        started_ts_ms: None,
        hist_ms: None,
        disagreement: None,
        self_check_fail: None,
        panic_line: None,
    });
    row.state = "done";
    row.bucket = Some(d.bucket.clone());
    row.secs = Some(d.secs);
    row.disagreement.clone_from(&d.disagreement);
    row.self_check_fail.clone_from(&d.self_check_fail);
    row.panic_line.clone_from(&d.panic_line);
}

/// Joins each row's historical wall time from the committed sweep baseline,
/// on the run's own `mode` — falling back to the baseline's bare legacy `ms`
/// only when the baseline's own header was captured in that same mode
/// (mirroring the migration `sweep_baseline::SweepEntry::timings` does for
/// the gauge itself).
fn join_hist_ms(rows: &mut BTreeMap<usize, RowView>, baseline: &SweepBaselineFile, mode: &str) {
    let header_mode = mode_key(&baseline.config);
    for row in rows.values_mut() {
        let Some(entry) = baseline.entries.get(&row.key) else {
            continue;
        };
        row.hist_ms = entry
            .ms_by_mode
            .get(mode)
            .copied()
            .or_else(|| (header_mode == mode).then_some(entry.ms));
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
    use crate::solve_gauge::sweep_baseline::{SweepConfig, SweepEntry};

    fn tmp_dir(tag: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir().join(format!("als-watch-data-{tag}-{}", std::process::id()));
        std::fs::remove_dir_all(&dir).ok();
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }

    fn jsonl(dir: &Path, lines: &[&str]) -> std::path::PathBuf {
        let path = dir.join("progress.jsonl");
        std::fs::write(&path, lines.join("\n") + "\n").unwrap();
        path
    }

    #[test]
    fn a_missing_jsonl_file_answers_a_waiting_payload() {
        let dir = tmp_dir("missing");
        let body = assemble(&dir.join("nope.jsonl"), &dir.join("nope-baseline.json"));
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        assert_eq!(v["waiting"], serde_json::json!(true));
        assert!(v["run"].is_null());
        assert_eq!(v["rows"].as_array().unwrap().len(), 0);
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn rows_join_state_and_historical_wall_time_from_a_fixture() {
        let dir = tmp_dir("join");
        let path = jsonl(
            &dir,
            &[
                r#"{"event":"run_start","ts_ms":100,"mode":"stage1","solver":"sat4j","jobs":2,"conflict_budget":1,"encode_budget":2,"primary_var_cap":3,"symmetry":20,"count":false,"count_symmetry":0,"rows":[{"i":0,"key":"a.als[0]"},{"i":1,"key":"a.als[1]"},{"i":2,"key":"b.als[0]"}]}"#,
                r#"{"event":"row_start","ts_ms":110,"i":0,"key":"a.als[0]"}"#,
                r#"{"event":"row_done","ts_ms":120,"i":0,"key":"a.als[0]","bucket":"agree_sat","secs":0.5}"#,
                r#"{"event":"row_start","ts_ms":130,"i":1,"key":"a.als[1]"}"#,
                // row 2 (b.als[0]) never starts -- stays pending.
                // A torn tail line: dropped, not fatal.
                r#"{"event":"row_start","ts_ms":140,"i":2,"key":"b.als["#,
            ],
        );

        let mut entries = BTreeMap::new();
        let mut ms_by_mode = BTreeMap::new();
        ms_by_mode.insert("stage1".to_owned(), 738u64);
        entries.insert(
            "a.als[0]".to_owned(),
            SweepEntry {
                verdict_bucket: "agree_sat".to_owned(),
                count_bucket: None,
                ms: 738,
                ms_by_mode,
            },
        );
        let baseline_file = SweepBaselineFile {
            config: SweepConfig {
                symmetry: 20,
                conflict_budget: 1,
                encode_budget: 2,
                primary_var_cap: 3,
                no_overflow: true,
                solver: "sat4j".to_owned(),
                count_enabled: false,
                count_symmetry: 0,
                count_cap: 0,
                enum_budget: 0,
                enumerate_all: false,
                capture_commit: None,
            },
            entries,
        };
        let baseline_path = dir.join("baseline.json");
        baseline_file.write_atomic(&baseline_path).unwrap();

        let body = assemble(&path, &baseline_path);
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        assert_eq!(v["waiting"], serde_json::json!(false));
        assert_eq!(v["run"]["mode"], serde_json::json!("stage1"));

        let rows = v["rows"].as_array().unwrap();
        assert_eq!(rows.len(), 3);
        let by_i = |i: i64| rows.iter().find(|r| r["i"] == i).unwrap();

        assert_eq!(by_i(0)["state"], serde_json::json!("done"));
        assert_eq!(by_i(0)["bucket"], serde_json::json!("agree_sat"));
        assert_eq!(by_i(0)["hist_ms"], serde_json::json!(738));

        assert_eq!(by_i(1)["state"], serde_json::json!("running"));
        assert_eq!(by_i(1)["started_ts_ms"], serde_json::json!(130));
        // a.als[1] has no baseline entry of its own.
        assert!(by_i(1)["hist_ms"].is_null());

        assert_eq!(by_i(2)["state"], serde_json::json!("pending"));

        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn a_missing_baseline_leaves_hist_ms_absent_without_failing() {
        let dir = tmp_dir("nobaseline");
        let path = jsonl(
            &dir,
            &[
                r#"{"event":"run_start","ts_ms":1,"mode":"stage1","solver":"sat4j","jobs":1,"conflict_budget":1,"encode_budget":1,"primary_var_cap":1,"symmetry":0,"count":false,"count_symmetry":0,"rows":[{"i":0,"key":"a.als[0]"}]}"#,
                r#"{"event":"row_done","ts_ms":2,"i":0,"key":"a.als[0]","bucket":"agree_sat","secs":0.1}"#,
            ],
        );
        let body = assemble(&path, &dir.join("does-not-exist.json"));
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        assert_eq!(v["rows"][0]["state"], serde_json::json!("done"));
        assert!(v["rows"][0]["hist_ms"].is_null());
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn a_disagreement_and_a_run_done_summary_pass_through() {
        let dir = tmp_dir("disagree");
        let path = jsonl(
            &dir,
            &[
                r#"{"event":"run_start","ts_ms":1,"mode":"stage1","solver":"sat4j","jobs":1,"conflict_budget":1,"encode_budget":1,"primary_var_cap":1,"symmetry":0,"count":false,"count_symmetry":0,"rows":[{"i":0,"key":"a.als[0]"}]}"#,
                r#"{"event":"row_done","ts_ms":2,"i":0,"key":"a.als[0]","bucket":"DISAGREE","secs":0.1,"disagreement":"a.als[0]: mettle=SAT jar=UNSAT"}"#,
                r#"{"event":"run_done","ts_ms":3,"total_secs":9.5,"verdict_buckets":{"DISAGREE":1}}"#,
            ],
        );
        let body = assemble(&path, &dir.join("no-baseline.json"));
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        assert_eq!(
            v["rows"][0]["disagreement"],
            serde_json::json!("a.als[0]: mettle=SAT jar=UNSAT")
        );
        assert_eq!(v["done"]["total_secs"], serde_json::json!(9.5));
        std::fs::remove_dir_all(&dir).ok();
    }
}
