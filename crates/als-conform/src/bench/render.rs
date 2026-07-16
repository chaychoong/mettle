//! Text rendering for [`super::BenchReport`]. Pure formatting -- no I/O, no
//! process spawning -- kept separate from `mod.rs`'s orchestration so it's
//! trivially unit-testable against synthetic reports (see `tests.rs`).

use std::fmt::Write as _;

use super::BenchReport;

pub(super) fn render_text(report: &BenchReport) -> String {
    let mut out = String::new();
    render_corpus(&mut out, report);
    render_conformance(&mut out, report);
    render_speed(&mut out, report);
    out
}

fn render_corpus(out: &mut String, report: &BenchReport) {
    let _ = writeln!(out, "=== mt-024 conformance + speed bench ===");
    let _ = writeln!(out);
    let _ = writeln!(out, "corpus:");
    for root in &report.corpus.roots {
        let _ = writeln!(out, "  {}", root.display());
    }
    let _ = writeln!(out, "  {} files", report.corpus.file_count);
    let _ = writeln!(out);
}

fn render_conformance(out: &mut String, report: &BenchReport) {
    let c = &report.conformance;
    let _ = writeln!(out, "--- conformance ---");
    let _ = writeln!(
        out,
        "{:<10} {:>7} {:>7} {:>7} {:>7}",
        "STAGE", "TOTAL", "ACCEPT", "REJECT", "PANICS"
    );
    for s in &c.mettle_summary {
        let _ = writeln!(
            out,
            "{:<10} {:>7} {:>7} {:>7} {:>7}",
            s.stage, s.total, s.accept, s.reject, s.panics
        );
    }
    let _ = writeln!(out);

    if !c.jar_available {
        let _ = writeln!(
            out,
            "jar skipped (--skip-jar): mettle-vs-jar agreement not computed."
        );
        let _ = writeln!(out);
        return;
    }

    let _ = writeln!(
        out,
        "{:<10} {:>9} {:>7} {:>9} {:>9}",
        "STAGE", "COMPARED", "AGREE", "DISAGREE", "AGREE %"
    );
    for stage in &c.stages {
        let _ = writeln!(
            out,
            "{:<10} {:>9} {:>7} {:>9} {:>8.2}%",
            stage.stage, stage.compared, stage.agree, stage.disagree, stage.agreement_pct
        );
    }
    let _ = writeln!(out);

    for stage in &c.stages {
        if stage.disagreements.is_empty() {
            let _ = writeln!(out, "{} disagreements: (none)", stage.stage);
            continue;
        }
        let _ = writeln!(out, "{} disagreements:", stage.stage);
        for d in &stage.disagreements {
            let _ = writeln!(
                out,
                "  {:<50} mettle={:<16} jar={}",
                d.file.display(),
                d.mettle_verdict,
                d.jar_verdict
            );
        }
    }
    let _ = writeln!(out);
}

fn render_speed(out: &mut String, report: &BenchReport) {
    let s = &report.speed;
    let _ = writeln!(out, "--- speed ---");
    let _ = writeln!(
        out,
        "note: timings vary run to run; every other number above is byte-stable."
    );
    let _ = writeln!(out);

    let _ = writeln!(out, "mettle (warm, --threads-parallel):");
    let _ = writeln!(
        out,
        "  {:<10} {:>7} {:>12} {:>12}",
        "STAGE", "FILES", "TOTAL_MS", "MEDIAN_US"
    );
    for st in &s.mettle.stages {
        let _ = writeln!(
            out,
            "  {:<10} {:>7} {:>12.2} {:>12.3}",
            st.stage, st.files, st.total_ms, st.median_us
        );
    }
    let _ = writeln!(out);

    let Some(jar) = &s.jar else {
        let _ = writeln!(out, "jar skipped (--skip-jar): no jar timing.");
        return;
    };

    let _ = writeln!(
        out,
        "jar batch (one JVM, {} files, amortized startup):",
        jar.batch.files
    );
    let _ = writeln!(
        out,
        "  total_ms={:.2}  in_jvm_total_ms={:.2}  median_us={:.3}",
        jar.batch.total_ms, jar.batch.in_jvm_total_ms, jar.batch.median_us
    );
    let _ = writeln!(
        out,
        "  (total_ms includes the one JVM startup; in_jvm_total_ms/median_us do not)"
    );
    let _ = writeln!(out);

    let _ = writeln!(
        out,
        "jar cold (fresh JVM per file, {} files, size-spread sample, startup included):",
        jar.cold.sample_files.len()
    );
    for (file, ms) in jar
        .cold
        .sample_files
        .iter()
        .zip(jar.cold.per_file_ms.iter())
    {
        let _ = writeln!(out, "  {:<50} {ms:>10.2} ms", file.display());
    }
    let _ = writeln!(
        out,
        "  median_ms={:.2}  mean_ms={:.2}",
        jar.cold.median_ms, jar.cold.mean_ms
    );
    let _ = writeln!(out);

    if !s.ratios.is_empty() {
        let _ = writeln!(
            out,
            "caveat: only mettle-total-vs-jar-batch-total is like-for-like (both are \"whole \
             corpus, fused parse+resolve, one process\" numbers) -- the jar has no separate \
             parse-only timing (parseEverything_fromFile is one fused call), and mettle's total \
             reflects --threads parallelism while the jar batch runs single-threaded inside one \
             JVM, so a ratio near 1 does not mean equal single-core speed."
        );
        for r in &s.ratios {
            let _ = writeln!(
                out,
                "  {:<10} mettle_total_ms={:.2}  jar_batch_total_ms={:.2}  jar/mettle={:.2}x",
                r.stage, r.mettle_total_ms, r.jar_batch_total_ms, r.jar_over_mettle
            );
        }
        let _ = writeln!(out);
    }
}
