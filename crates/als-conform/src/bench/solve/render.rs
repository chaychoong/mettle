//! Text rendering for [`super::SolveBenchReport`]. Pure formatting, no I/O --
//! mirrors [`super::super::render`]'s split from its own orchestration.

use std::fmt::Write as _;

use super::SolveBenchReport;

pub(super) fn render_text(report: &SolveBenchReport) -> String {
    let mut out = String::new();
    render_corpus(&mut out, report);
    render_summary(&mut out, report);
    render_top20(&mut out, report);
    render_disagreements(&mut out, report);
    render_caveats(&mut out);
    out
}

fn render_corpus(out: &mut String, report: &SolveBenchReport) {
    let _ = writeln!(
        out,
        "=== mt-138 solve head-to-head: mettle (CaDiCaL) vs. jar (sat4j) ==="
    );
    let _ = writeln!(out);
    let _ = writeln!(out, "corpus:");
    for root in &report.corpus.roots {
        let _ = writeln!(out, "  {}", root.display());
    }
    let _ = writeln!(out, "  {} files", report.corpus.file_count);
    let _ = writeln!(out);
}

fn render_summary(out: &mut String, report: &SolveBenchReport) {
    let s = &report.summary;
    let _ = writeln!(out, "--- summary ---");
    let _ = writeln!(
        out,
        "note: timings vary run to run; row counts and ordering are byte-stable."
    );
    let _ = writeln!(out);
    let _ = writeln!(out, "both-answered commands: {}", s.both_answered);
    let _ = writeln!(
        out,
        "  jar    total_ms={:.2}  median_ms={:.3}",
        s.jar_total_ms, s.jar_median_ms
    );
    let _ = writeln!(
        out,
        "  mettle total_ms={:.2}  median_ms={:.3}",
        s.mettle_total_ms, s.mettle_median_ms
    );
    let _ = writeln!(out);

    if s.excluded.is_empty() {
        let _ = writeln!(out, "excluded: (none)");
    } else {
        let _ = writeln!(out, "excluded by reason:");
        for e in &s.excluded {
            let _ = writeln!(out, "  {:<40} {:>6}", e.reason, e.count);
        }
    }
    let _ = writeln!(out);
}

fn render_top20(out: &mut String, report: &SolveBenchReport) {
    let _ = writeln!(out, "--- top 20 by jar time ---");
    let _ = writeln!(
        out,
        "{:<50} {:>5} {:<6} {:>12} {:>12}",
        "FILE[IDX]", "", "VERDICT", "JAR_MS", "METTLE_MS"
    );
    for row in &report.top20 {
        let _ = writeln!(
            out,
            "{:<50} [{:>3}] {:<6} {:>12.2} {:>12.2}",
            row.file.display(),
            row.index,
            row.verdict,
            row.jar_ms,
            row.mettle_ms
        );
    }
    let _ = writeln!(out);
}

fn render_disagreements(out: &mut String, report: &SolveBenchReport) {
    if report.disagreements.is_empty() {
        let _ = writeln!(out, "verdict disagreements: (none)");
        let _ = writeln!(out);
    } else {
        let _ = writeln!(
            out,
            "verdict disagreements: {} -- THIS IS A REGRESSION, not a wiring bug",
            report.disagreements.len()
        );
        for d in &report.disagreements {
            let _ = writeln!(
                out,
                "  {}[{}]  mettle={}  jar={}",
                d.file.display(),
                d.index,
                d.mettle_verdict,
                d.jar_verdict
            );
        }
        let _ = writeln!(out);
    }

    if !report.anomalies.is_empty() {
        let _ = writeln!(
            out,
            "anomalies (self-check failures / panics, mettle-side):"
        );
        for line in &report.anomalies {
            let _ = writeln!(out, "  {line}");
        }
        let _ = writeln!(out);
    }
}

fn render_caveats(out: &mut String) {
    let _ = writeln!(out, "--- caveats ---");
    let _ = writeln!(
        out,
        "- one command at a time on both sides: the jar runs one JVM per file (its commands\n\
         \x20\x20run in sequence inside it), and mettle runs single-threaded -- no parallelism\n\
         \x20\x20anywhere near a recorded time."
    );
    let _ = writeln!(
        out,
        "- the jar's timer is in-JVM (OracleShim's own System.nanoTime() around\n\
         \x20\x20translation+solve); JVM startup and the file's one parse are excluded on\n\
         \x20\x20both sides."
    );
    let _ = writeln!(
        out,
        "- the solvers differ by design (mettle: CaDiCaL, the jar: sat4j) -- that difference is\n\
         \x20\x20part of what this report measures, not noise to average away."
    );
    let _ = writeln!(
        out,
        "- verdict agreement is asserted here (see disagreements above), not merely reported --\n\
         \x20\x20this tool does not consult solve-gauge's cached baseline; it is a live,\n\
         \x20\x20independent cross-check against the jar this run just made."
    );
}
