//! The gauge's report types ([`SolveGaugeReport`], [`PerCommand`]) and their
//! deterministic text renderer.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use serde::Serialize;

use crate::error::ConformError;

use super::baseline;
use super::sweep_baseline::SweepDelta;
use super::GaugeConfig;

/// One command's entry in the deterministic per-command report array (mt-054 (c),
/// for delta mode). Filled in file-sorted, index-ascending order.
#[derive(Debug, Clone, Serialize)]
pub struct PerCommand {
    /// `relpath[idx]`.
    pub key: String,
    /// The verdict-stage bucket this command landed in.
    pub verdict_bucket: String,
    /// The counting-net bucket, when stage 2 ran and covered this command.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub count_bucket: Option<String>,
}

/// The gauge's deterministic report. `BTreeMap`s serialize/iterate in key order
/// and every `Vec` is filled in file-sorted, index-ascending order, so a full
/// (non-fail-fast) run is byte-identical run to run and at any job count (STYLE
/// D1). A fail-fast `partial` run is explicitly not byte-stable across job counts.
#[derive(Debug, Clone, Serialize)]
pub struct SolveGaugeReport {
    /// Total root-module commands processed.
    pub commands: usize,
    /// Names of the `*-verdict.json` baselines merged.
    pub baseline_files: Vec<String>,
    /// Names of the `*-count-sb<N>.json` count baselines merged (cache stage 2).
    pub count_baseline_files: Vec<String>,
    /// Per-command baseline entries loaded.
    pub baseline_entries: usize,
    /// Verdict-stage buckets; these sum to [`Self::commands`] (asserted).
    pub verdict_buckets: BTreeMap<String, usize>,
    /// Every verdict disagreement, `relpath[idx]: mettle=… jar=…`.
    pub disagreements: Vec<String>,
    /// Every SAT instance that failed its own self-check (a mettle bug).
    pub self_check_failures: Vec<String>,
    /// Every command whose mettle pipeline panicked (a mettle bug).
    pub panics: Vec<String>,
    /// Stage-1 symmetry-breaking cap the verdict net ran at.
    pub symmetry: u32,
    /// Stage-2 symmetry-breaking cap the counting net ran at on both sides.
    pub count_symmetry: u32,
    /// Whether stage 2 ran.
    pub count_enabled: bool,
    /// Counting-net buckets (`count_match` / `COUNT_MISMATCH` / `skip_*`).
    pub count_buckets: BTreeMap<String, usize>,
    /// Every count mismatch, `relpath[idx]: mettle=m jar=j`.
    pub count_mismatches: Vec<String>,
    /// mt-054 (c): per-command results, in file-sorted, index-ascending order.
    pub per_command: Vec<PerCommand>,
    /// mt-054 (c): a fail-fast run that stopped early is a partial report.
    pub partial: bool,
    /// mt-054 (c): what tripped fail-fast (for the `PARTIAL (...)` marker).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub fail_fast_trigger: Option<String>,
    /// mt-057 (3): what moved relative to the sweep baseline (`--delta`).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub delta: Option<SweepDelta>,
}

impl SolveGaugeReport {
    pub(super) fn new(
        cfg: &GaugeConfig,
        baseline: &baseline::Baseline,
        count_files: Vec<String>,
    ) -> Self {
        Self {
            commands: 0,
            baseline_files: baseline.loaded.clone(),
            count_baseline_files: count_files,
            baseline_entries: baseline.command_count(),
            verdict_buckets: BTreeMap::new(),
            disagreements: Vec::new(),
            self_check_failures: Vec::new(),
            panics: Vec::new(),
            symmetry: cfg.symmetry,
            count_symmetry: cfg.count_symmetry,
            count_enabled: cfg.count,
            count_buckets: BTreeMap::new(),
            count_mismatches: Vec::new(),
            per_command: Vec::new(),
            partial: false,
            fail_fast_trigger: None,
            delta: None,
        }
    }
}

impl SolveGaugeReport {
    /// The process exit code this report implies: `1` for a fail-fast partial
    /// run, else `0` (a gauge, not a test — disagreements alone do not fail).
    #[must_use]
    pub fn exit_status(&self) -> u8 {
        u8::from(self.partial)
    }

    /// Renders the deterministic human-readable report.
    #[must_use]
    pub fn render_text(&self) -> String {
        let mut out = String::new();
        let _ = writeln!(out, "=== mt-037 solve gauge ===");
        if self.partial {
            let _ = writeln!(
                out,
                "PARTIAL (fail-fast after {})",
                self.fail_fast_trigger.as_deref().unwrap_or("<trigger>")
            );
        }
        let _ = writeln!(out, "commands          : {}", self.commands);
        let _ = writeln!(out, "stage-1 symmetry  : {}", self.symmetry);
        let _ = writeln!(
            out,
            "baselines         : {} ({} command entries)",
            if self.baseline_files.is_empty() {
                "<none>".to_owned()
            } else {
                self.baseline_files.join(", ")
            },
            self.baseline_entries
        );

        let _ = writeln!(out, "\nverdict buckets (sum = {}):", self.commands);
        for (bucket, n) in &self.verdict_buckets {
            let _ = writeln!(out, "  {bucket:<32} {n}");
        }

        render_list(&mut out, "DISAGREE", &self.disagreements);
        render_list(&mut out, "self-check failures", &self.self_check_failures);
        render_list(&mut out, "panics", &self.panics);

        if self.count_enabled {
            let _ = writeln!(
                out,
                "\n=== counting net (--count, symmetry {}) ===",
                self.count_symmetry
            );
            let _ = writeln!(
                out,
                "count baselines   : {}",
                if self.count_baseline_files.is_empty() {
                    "<none / live jar>".to_owned()
                } else {
                    self.count_baseline_files.join(", ")
                }
            );
            if self.count_buckets.is_empty() {
                let _ = writeln!(out, "  (no SAT commands reached the counting net)");
            }
            for (bucket, n) in &self.count_buckets {
                let _ = writeln!(out, "  {bucket:<32} {n}");
            }
            render_list(&mut out, "COUNT_MISMATCH", &self.count_mismatches);
        }

        self.render_delta(&mut out);
        out
    }

    /// The `--delta` section: what moved relative to the sweep baseline.
    fn render_delta(&self, out: &mut String) {
        let Some(delta) = &self.delta else {
            return;
        };
        let _ = writeln!(
            out,
            "\n=== delta vs {} ===",
            if delta.baseline_files.is_empty() {
                "<none>".to_owned()
            } else {
                delta.baseline_files.join(", ")
            }
        );
        let _ = writeln!(out, "unchanged         : {}", delta.unchanged);
        if !delta.count_compared {
            let _ = writeln!(
                out,
                "count buckets     : not compared (one side ran without --count)"
            );
        }
        render_list(out, "changed", &delta.changed);
        render_list(out, "new commands", &delta.new_commands);
        render_list(out, "gone commands", &delta.gone_commands);
        if delta.is_clean() {
            let _ = writeln!(out, "\nNO CHANGE vs the recorded baseline.");
        }
    }

    /// Renders the report as stable pretty JSON.
    ///
    /// # Errors
    /// Only if serialization itself fails (does not happen short of allocation
    /// failure).
    pub fn to_json(&self) -> Result<String, ConformError> {
        Ok(serde_json::to_string_pretty(self)?)
    }
}

/// Prints a titled list with its count (the count line always appears, so a clean
/// run shows an explicit `0` rather than silence).
fn render_list(out: &mut String, title: &str, items: &[String]) {
    let _ = writeln!(out, "\n{title}: {}", items.len());
    for item in items {
        let _ = writeln!(out, "  {item}");
    }
}
