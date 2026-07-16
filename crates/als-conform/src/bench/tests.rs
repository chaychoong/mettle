//! Report-assembly unit tests: synthetic verdict/timing records in, assert
//! the text + JSON shape out. No jar, no corpus files, no process spawning
//! -- exactly the "pure aggregation" boundary `scorecard.rs`'s own tests
//! exercise for the mt-006 scorecard.

use std::path::PathBuf;

use super::*;

fn sample_report(jar_available: bool) -> BenchReport {
    let mettle_summary = vec![
        StageSummary {
            stage: "parse".to_string(),
            total: 3,
            accept: 3,
            reject: 0,
            panics: 0,
        },
        StageSummary {
            stage: "resolve".to_string(),
            total: 3,
            accept: 2,
            reject: 1,
            panics: 0,
        },
    ];

    let stages = if jar_available {
        vec![
            StageConformance {
                stage: "parse".to_string(),
                compared: 3,
                agree: 3,
                disagree: 0,
                agreement_pct: 100.0,
                disagreements: Vec::new(),
            },
            StageConformance {
                stage: "resolve".to_string(),
                compared: 3,
                agree: 2,
                disagree: 1,
                agreement_pct: 200.0 / 3.0,
                disagreements: vec![Disagreement {
                    file: PathBuf::from("bad.als"),
                    mettle_verdict: "reject:resolve".to_string(),
                    jar_verdict: "accept".to_string(),
                }],
            },
        ]
    } else {
        Vec::new()
    };

    let mettle_speed = MettleSpeed {
        stages: vec![
            StageTiming {
                stage: "parse".to_string(),
                files: 3,
                total_ms: 1.5,
                median_us: 200.0,
            },
            StageTiming {
                stage: "resolve".to_string(),
                files: 3,
                total_ms: 4.0,
                median_us: 900.0,
            },
        ],
    };

    let (jar, ratios) = if jar_available {
        let jar = JarSpeed {
            batch: JarBatchTiming {
                files: 3,
                total_ms: 300.0,
                in_jvm_total_ms: 6.0,
                median_us: 1800.0,
            },
            cold: JarColdTiming {
                sample_files: vec![PathBuf::from("a.als"), PathBuf::from("z.als")],
                per_file_ms: vec![250.0, 260.0],
                median_ms: 255.0,
                mean_ms: 255.0,
            },
        };
        let ratios = vec![RatioEntry {
            stage: "resolve".to_string(),
            mettle_total_ms: 4.0,
            jar_batch_total_ms: 300.0,
            jar_over_mettle: 75.0,
        }];
        (Some(jar), ratios)
    } else {
        (None, Vec::new())
    };

    BenchReport {
        corpus: CorpusInfo {
            roots: vec![PathBuf::from("corpus/x"), PathBuf::from("corpus/y")],
            file_count: 3,
        },
        conformance: ConformanceSection {
            jar_available,
            mettle_summary,
            stages,
        },
        speed: SpeedSection {
            mettle: mettle_speed,
            jar,
            ratios,
        },
    }
}

#[test]
fn render_text_includes_corpus_and_stage_summary() {
    let text = sample_report(true).render_text();
    assert!(text.contains("mt-024 conformance + speed bench"));
    assert!(text.contains("corpus/x"));
    assert!(text.contains("corpus/y"));
    assert!(text.contains("3 files"));
    assert!(text.contains("parse"));
    assert!(text.contains("resolve"));
}

#[test]
fn render_text_shows_disagreements_when_present() {
    let text = sample_report(true).render_text();
    assert!(text.contains("bad.als"));
    assert!(text.contains("reject:resolve"));
    assert!(text.contains("parse disagreements: (none)"));
}

#[test]
fn render_text_notes_skip_jar() {
    let text = sample_report(false).render_text();
    assert!(text.contains("jar skipped (--skip-jar): mettle-vs-jar agreement not computed."));
    assert!(text.contains("jar skipped (--skip-jar): no jar timing."));
    // No jar-only content should appear.
    assert!(!text.contains("jar batch"));
    assert!(!text.contains("jar cold"));
}

#[test]
fn render_text_shows_batch_and_cold_and_ratio_caveat() {
    let text = sample_report(true).render_text();
    assert!(text.contains("jar batch (one JVM, 3 files"));
    assert!(text.contains("jar cold (fresh JVM per file, 2 files"));
    assert!(text.contains("caveat: only mettle-total-vs-jar-batch-total is like-for-like"));
    assert!(text.contains("jar/mettle=75.00x"));
}

#[test]
fn json_roundtrip_is_deterministic_and_parses() {
    let report = sample_report(true);
    let json1 = report
        .to_json()
        .unwrap_or_else(|e| panic!("serialize failed: {e}"));
    let json2 = report
        .to_json()
        .unwrap_or_else(|e| panic!("serialize failed: {e}"));
    assert_eq!(json1, json2);

    let value: serde_json::Value =
        serde_json::from_str(&json1).unwrap_or_else(|e| panic!("json did not parse: {e}"));
    assert_eq!(value["corpus"]["file_count"], 3);
    assert_eq!(value["conformance"]["jar_available"], true);
    assert_eq!(value["conformance"]["stages"][1]["stage"], "resolve");
    assert_eq!(
        value["conformance"]["stages"][1]["disagreements"][0]["file"],
        "bad.als"
    );
    assert_eq!(value["speed"]["jar"]["batch"]["files"], 3);
    assert_eq!(value["speed"]["ratios"][0]["jar_over_mettle"], 75.0);

    // Key order in the serialized text should match struct declaration
    // order (D2/D3: no HashMap anywhere in this schema).
    let corpus_idx = json1.find("\"corpus\"").unwrap_or(usize::MAX);
    let conformance_idx = json1.find("\"conformance\"").unwrap_or(usize::MAX);
    let speed_idx = json1.find("\"speed\"").unwrap_or(usize::MAX);
    assert!(corpus_idx < conformance_idx);
    assert!(conformance_idx < speed_idx);
}

#[test]
fn json_omits_jar_speed_when_skipped() {
    let report = sample_report(false);
    let json = report
        .to_json()
        .unwrap_or_else(|e| panic!("serialize failed: {e}"));
    let value: serde_json::Value =
        serde_json::from_str(&json).unwrap_or_else(|e| panic!("json did not parse: {e}"));
    assert!(value["speed"]["jar"].is_null());
    assert_eq!(value["conformance"]["jar_available"], false);
    assert!(value["conformance"]["stages"]
        .as_array()
        .is_some_and(std::vec::Vec::is_empty));
}

#[test]
fn discover_corpus_is_sorted_and_deduplicated() {
    let dir = std::env::temp_dir().join(format!(
        "als-conform-bench-test-discover-{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("sub")).unwrap_or_else(|e| panic!("mkdir failed: {e}"));
    std::fs::write(dir.join("b.als"), "sig A {}").unwrap_or_else(|e| panic!("write failed: {e}"));
    std::fs::write(dir.join("a.als"), "sig B {}").unwrap_or_else(|e| panic!("write failed: {e}"));
    std::fs::write(dir.join("ignore.txt"), "not als")
        .unwrap_or_else(|e| panic!("write failed: {e}"));
    std::fs::write(dir.join("sub/c.als"), "sig C {}")
        .unwrap_or_else(|e| panic!("write failed: {e}"));

    let found = discover_corpus(&[dir.clone(), dir.clone()]);
    let _ = std::fs::remove_dir_all(&dir);

    assert_eq!(
        found.len(),
        3,
        "expected 3 unique .als files, got {found:?}"
    );
    let mut sorted = found.clone();
    sorted.sort();
    assert_eq!(found, sorted, "discover_corpus must return sorted output");
}

#[test]
fn pick_cold_sample_includes_smallest_and_largest_and_is_deterministic() {
    let files: Vec<(PathBuf, String)> = vec![
        (PathBuf::from("a"), "x".repeat(10)),
        (PathBuf::from("b"), "x".repeat(50)),
        (PathBuf::from("c"), "x".repeat(30)),
        (PathBuf::from("d"), "x".repeat(5)),
        (PathBuf::from("e"), "x".repeat(90)),
    ];
    let sample1 = pick_cold_sample(&files, 3);
    let sample2 = pick_cold_sample(&files, 3);
    assert_eq!(sample1, sample2, "selection must be deterministic");
    assert_eq!(sample1.len(), 3);
    assert_eq!(sample1[0], PathBuf::from("d")); // smallest (5 bytes)
    assert_eq!(sample1[2], PathBuf::from("e")); // largest (90 bytes)
}

#[test]
fn pick_cold_sample_caps_at_file_count() {
    let files: Vec<(PathBuf, String)> = vec![
        (PathBuf::from("a"), "x".to_string()),
        (PathBuf::from("b"), "xx".to_string()),
    ];
    let sample = pick_cold_sample(&files, 10);
    assert_eq!(sample.len(), 2);
}

#[test]
fn median_and_mean_basic() {
    assert!((median(vec![1.0, 2.0, 3.0]) - 2.0).abs() < f64::EPSILON);
    assert!((median(vec![1.0, 2.0, 3.0, 4.0]) - 2.5).abs() < f64::EPSILON);
    assert!((median(vec![]) - 0.0).abs() < f64::EPSILON);
    assert!((mean(&[2.0, 4.0]) - 3.0).abs() < f64::EPSILON);
    assert!((mean(&[]) - 0.0).abs() < f64::EPSILON);
}
