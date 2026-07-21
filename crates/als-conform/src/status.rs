//! Owner-facing status monitor (mt-054 (d)).
//!
//! A [`StatusFile`] atomically rewrites a single well-known plain-text file so
//! the product owner can `watch`/`tail` a long run and see it is alive, where it
//! is, and its last few heartbeats. Rewrites are rate-limited to ~once per 2s
//! plus phase transitions and completion.
//!
//! This is an **observability channel**, so wall-clock is fine here (STYLE D4
//! governs the deterministic *pipeline*, never a monitor). It is fed from the
//! same progress stream the stderr heartbeat uses: the bin composes stderr +
//! status by teeing each progress line, so the library's `run_gauge` still takes
//! only a `&mut dyn FnMut(&str)` and never touches this file (STYLE E3). A
//! disabled [`StatusFile`] is a no-op sink (`--no-status`).
//!
//! Field extraction (`phase`, `k/N`, current item) is best-effort parsing of the
//! progress lines the driver already emits; a parse miss only degrades the
//! monitor, never a result.

use std::collections::VecDeque;
use std::fmt::Write as _;
use std::path::PathBuf;
use std::time::{Instant, SystemTime, UNIX_EPOCH};

/// How many recent heartbeat lines to keep and show.
const RECENT_CAP: usize = 10;
/// Minimum wall-time between throttled rewrites.
const MIN_REWRITE_INTERVAL: std::time::Duration = std::time::Duration::from_secs(2);

/// A rate-limited, atomically-rewritten status file.
#[derive(Debug)]
pub struct StatusFile {
    path: PathBuf,
    tool: String,
    args: String,
    start: Instant,
    start_wall_secs: u64,
    phase: String,
    progress: Option<(usize, usize)>,
    current: Option<String>,
    recent: VecDeque<String>,
    last_write: Option<Instant>,
    enabled: bool,
}

impl StatusFile {
    /// Creates a status file at `path` (creating its parent directory), tagged
    /// with the `tool` name and an `args` summary. On any I/O failure the
    /// monitor is disabled rather than propagated — it must never break a run.
    #[must_use]
    pub fn new(path: PathBuf, tool: &str, args: &str) -> Self {
        let enabled = match path.parent() {
            Some(dir) => std::fs::create_dir_all(dir).is_ok(),
            None => true,
        };
        let mut sf = Self {
            path,
            tool: tool.to_owned(),
            args: args.to_owned(),
            start: Instant::now(),
            start_wall_secs: unix_secs(),
            phase: "starting".to_owned(),
            progress: None,
            current: None,
            recent: VecDeque::with_capacity(RECENT_CAP),
            last_write: None,
            enabled,
        };
        sf.write(true);
        sf
    }

    /// A disabled no-op sink (`--no-status`).
    #[must_use]
    pub fn disabled() -> Self {
        Self {
            path: PathBuf::new(),
            tool: String::new(),
            args: String::new(),
            start: Instant::now(),
            start_wall_secs: unix_secs(),
            phase: String::new(),
            progress: None,
            current: None,
            recent: VecDeque::new(),
            last_write: None,
            enabled: false,
        }
    }

    /// Records one progress line: updates the derived fields, appends to the
    /// recent-lines ring, and rewrites the file (forced on a phase change,
    /// otherwise throttled).
    pub fn heartbeat(&mut self, line: &str) {
        if !self.enabled {
            return;
        }
        let prev_phase = self.phase.clone();
        self.absorb(line);
        if self.recent.len() == RECENT_CAP {
            self.recent.pop_front();
        }
        self.recent.push_back(line.to_owned());
        self.write(self.phase != prev_phase);
    }

    /// Writes the final state with a one-line `DONE:` summary and end time
    /// (always written, bypassing the rate limit).
    #[allow(
        clippy::assigning_clones,
        reason = "one-shot final state write, not a hot path"
    )]
    pub fn done(&mut self, summary: &str) {
        if !self.enabled {
            return;
        }
        self.phase = "done".to_owned();
        self.current = Some(format!("DONE: {summary}"));
        self.write(true);
    }

    /// Updates derived fields from a progress line (best-effort).
    fn absorb(&mut self, line: &str) {
        let trimmed = line.trim_start();
        if let Some((k, n, rest)) = parse_k_of_n(trimmed) {
            self.progress = Some((k, n));
            if !rest.is_empty() {
                self.current = Some(rest.to_owned());
            }
        } else if let Some(phase) = detect_phase(trimmed) {
            self.phase = phase;
            self.current = Some(trimmed.to_owned());
        } else if !trimmed.is_empty() {
            self.current = Some(trimmed.to_owned());
        }
    }

    /// Atomically rewrites the file (temp + rename), honoring the rate limit
    /// unless `force`.
    fn write(&mut self, force: bool) {
        if !self.enabled {
            return;
        }
        let now = Instant::now();
        if !force {
            if let Some(last) = self.last_write {
                if now.duration_since(last) < MIN_REWRITE_INTERVAL {
                    return;
                }
            }
        }
        self.last_write = Some(now);
        let body = self.render();
        // Best-effort: a monitor write failure must never abort the run.
        let tmp = self.path.with_extension("txt.tmp");
        if std::fs::write(&tmp, &body).is_ok() {
            let _ = std::fs::rename(&tmp, &self.path);
        }
    }

    fn render(&self) -> String {
        let mut out = String::new();
        let _ = writeln!(out, "{}  {}", self.tool, self.args);
        let _ = writeln!(out, "started : {}", fmt_unix_utc(self.start_wall_secs));
        let _ = writeln!(out, "phase   : {}", self.phase);
        if let Some((k, n)) = self.progress {
            let _ = writeln!(out, "progress: {k}/{n}");
        }
        if let Some(cur) = &self.current {
            let _ = writeln!(out, "current : {cur}");
        }
        let _ = writeln!(out, "elapsed : {:.1}s", self.start.elapsed().as_secs_f64());
        if self.phase == "done" {
            let _ = writeln!(out, "ended   : {}", fmt_unix_utc(unix_secs()));
        }
        let _ = writeln!(out, "\nrecent:");
        for line in &self.recent {
            let _ = writeln!(out, "  {line}");
        }
        out
    }
}

/// Parses a leading `[k/N]` token, returning `(k, N, rest-of-line)`.
fn parse_k_of_n(line: &str) -> Option<(usize, usize, &str)> {
    let rest = line.strip_prefix('[')?;
    let (inside, after) = rest.split_once(']')?;
    let (k, n) = inside.split_once('/')?;
    Some((k.trim().parse().ok()?, n.trim().parse().ok()?, after.trim()))
}

/// Recognizes a phase-announcing progress line.
fn detect_phase(line: &str) -> Option<String> {
    let l = line.to_ascii_lowercase();
    if l.starts_with("stage 1") {
        Some("stage 1 (verdict)".to_owned())
    } else if l.starts_with("stage 2") {
        Some("stage 2 (count)".to_owned())
    } else if l.starts_with("refresh") {
        Some("refresh counts".to_owned())
    } else {
        None
    }
}

fn unix_secs() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| d.as_secs())
}

/// Formats Unix seconds as `YYYY-MM-DD HH:MM:SS UTC` (Hinnant's civil-from-days;
/// dependency-free, monitor-only so exactness beyond seconds is irrelevant).
#[allow(
    clippy::cast_possible_wrap,
    clippy::many_single_char_names,
    reason = "the civil-from-days reference algorithm names its intermediates y/m/d/z/era/doe"
)]
fn fmt_unix_utc(secs: u64) -> String {
    let days = (secs / 86_400) as i64;
    let rem = secs % 86_400;
    let (h, m, s) = (rem / 3600, (rem % 3600) / 60, rem % 60);
    let z = days + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let month = if mp < 10 { mp + 3 } else { mp - 9 };
    let year = if month <= 2 { y + 1 } else { y };
    format!("{year:04}-{month:02}-{d:02} {h:02}:{m:02}:{s:02} UTC")
}

#[cfg(test)]
#[allow(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "test fixtures assert on known-good values"
)]
mod tests {
    use super::*;

    #[test]
    fn parses_k_of_n() {
        assert_eq!(
            parse_k_of_n("[3/50] path/x.als"),
            Some((3, 50, "path/x.als"))
        );
        assert_eq!(parse_k_of_n("no brackets"), None);
    }

    #[test]
    fn detects_phase() {
        assert_eq!(
            detect_phase("stage 1: mettle sweep over 10 files").as_deref(),
            Some("stage 1 (verdict)")
        );
        assert!(detect_phase("  foo[0] …").is_none());
    }

    #[test]
    fn fmt_epoch() {
        // 2021-01-01 00:00:00 UTC = 1609459200.
        assert_eq!(fmt_unix_utc(1_609_459_200), "2021-01-01 00:00:00 UTC");
        assert_eq!(fmt_unix_utc(0), "1970-01-01 00:00:00 UTC");
    }

    #[test]
    fn writes_and_completes() {
        let dir = std::env::temp_dir().join(format!("als-status-{}", std::process::id()));
        let path = dir.join("s.txt");
        let mut sf = StatusFile::new(path.clone(), "solve-gauge", "--jobs 4");
        sf.heartbeat("stage 1: mettle sweep over 3 files");
        sf.heartbeat("[1/3] a.als");
        sf.done("3 files, 0 disagreements");
        let body = std::fs::read_to_string(&path).unwrap();
        assert!(body.contains("solve-gauge"));
        assert!(body.contains("DONE: 3 files"));
        assert!(body.contains("ended"));
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn disabled_is_noop() {
        let mut sf = StatusFile::disabled();
        sf.heartbeat("anything");
        sf.done("x"); // must not panic or write
    }
}
