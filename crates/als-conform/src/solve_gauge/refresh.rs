//! `--refresh-counts` mode (mt-054 (b)): produce a cached jar count baseline.
//!
//! Walks the roots, runs the reference jar (`EnumerationCap::UpTo(count_cap + 1)`)
//! on **every** `.als` file at the pinned config, and records each command's
//! outcome into a [`CountBaselineFile`]. Per-file JVMs run in parallel under
//! `--jobs`. **Interruption-safe:** the output is rewritten atomically after each
//! file completes, and `--resume` skips relpaths already present.
//!
//! Stage 1 does not run here — this mode only materializes jar facts.

use std::collections::BTreeMap;
use std::path::Path;

use crate::config::{EnumerationCap, OracleConfig};
use crate::error::ConformError;
use crate::shim::{ensure_shim_compiled, run_oracle_on_file};

use super::count_baseline::{
    file_counts_from_outcome, read_count_baseline, CountBaselineFile, CountConfig, FileCounts,
};
use super::parallel::parallel_fold;
use super::{collect_sorted_als, workspace_relpath, GaugeConfig, JAR_SOLVER};

/// Runs the count-baseline refresh, writing (and incrementally rewriting)
/// `out_path`.
///
/// # Errors
/// Propagates shim-compilation failure, a `--resume` header that disagrees with
/// the run's pinned config, and a final-write I/O failure.
pub fn refresh_counts(
    cfg: &GaugeConfig,
    out_path: &Path,
    resume: bool,
    progress: &mut dyn FnMut(&str),
) -> Result<(), ConformError> {
    let header = CountConfig {
        count_symmetry: cfg.count_symmetry,
        count_cap: cfg.count_cap,
        jar_timeout_secs: cfg.jar_timeout.as_secs(),
        no_overflow: !cfg.allow_overflow,
        solver: JAR_SOLVER.to_owned(),
    };

    let oracle_cfg = OracleConfig::new(&cfg.jar_path, &cfg.shim_source)
        .with_symmetry(i32::try_from(cfg.count_symmetry).unwrap_or(i32::MAX))
        .with_no_overflow(!cfg.allow_overflow)
        .with_solver(JAR_SOLVER)
        .with_timeout(cfg.jar_timeout);
    let shim_classes = ensure_shim_compiled(&oracle_cfg)?;

    // Seed the accumulator from an existing output when resuming (its config must
    // match — mixing configs into one baseline would produce fabricated counts).
    let mut acc = CountBaselineFile {
        config: header.clone(),
        entries: BTreeMap::new(),
    };
    if resume {
        if let Ok(text) = std::fs::read_to_string(out_path) {
            if let Some((existing_config, existing_entries)) = read_count_baseline(&text) {
                resume_config_guard(&existing_config, &header, out_path)?;
                acc.entries = existing_entries;
            }
        }
    }

    let mut files = collect_sorted_als(&cfg.roots);
    let already = acc.entries.len();
    files.retain(|p| {
        !acc.entries
            .contains_key(&workspace_relpath(p, &cfg.workspace_root))
    });
    progress(&format!(
        "refresh-counts: {} files to run ({already} already present) → {}",
        files.len(),
        out_path.display()
    ));

    let cap = u32::try_from(cfg.count_cap + 1).unwrap_or(u32::MAX);
    let work = |path: &std::path::PathBuf, send: &mut dyn FnMut(&str)| {
        let rel = workspace_relpath(path, &cfg.workspace_root);
        send(&format!("refresh {rel}"));
        let result =
            run_oracle_on_file(&oracle_cfg, &shim_classes, path, EnumerationCap::UpTo(cap));
        (rel, file_counts_from_outcome(&result.outcome))
    };

    // Fold on the coordinator thread: insert and atomically rewrite after each
    // file, so a kill at any point leaves a valid, resumable baseline.
    let mut on_result = |_i: usize, r: &(String, FileCounts)| {
        acc.entries.insert(r.0.clone(), r.1.clone());
        let _ = write_atomic(out_path, &acc);
    };

    parallel_fold(
        &files,
        cfg.jobs,
        false,
        progress,
        |p| workspace_relpath(p, &cfg.workspace_root),
        &mut on_result,
        work,
        |_| None,
    );

    // Final authoritative write (also covers the empty / all-resumed case).
    write_atomic(out_path, &acc)?;
    progress(&format!(
        "refresh-counts: done, {} files recorded",
        acc.entries.len()
    ));
    Ok(())
}

/// A `--resume` header disagreeing with the run's config is a hard error: the
/// existing entries were produced at a different config and cannot be extended.
fn resume_config_guard(
    existing: &CountConfig,
    run: &CountConfig,
    out_path: &Path,
) -> Result<(), ConformError> {
    let name = out_path.display().to_string();
    let field = if existing.count_symmetry != run.count_symmetry {
        Some((
            "count_symmetry",
            run.count_symmetry.to_string(),
            existing.count_symmetry.to_string(),
        ))
    } else if existing.count_cap != run.count_cap {
        Some((
            "count_cap",
            run.count_cap.to_string(),
            existing.count_cap.to_string(),
        ))
    } else if existing.no_overflow != run.no_overflow {
        Some((
            "no_overflow",
            run.no_overflow.to_string(),
            existing.no_overflow.to_string(),
        ))
    } else if existing.solver != run.solver {
        Some(("solver", run.solver.clone(), existing.solver.clone()))
    } else {
        None
    };
    if let Some((field, expected, found)) = field {
        return Err(ConformError::CountBaselineConfigMismatch {
            file: name,
            field,
            expected,
            found,
        });
    }
    Ok(())
}

/// Serializes `baseline` to deterministic pretty JSON and writes it to `out_path`
/// atomically (temp file in the same directory + rename).
fn write_atomic(out_path: &Path, baseline: &CountBaselineFile) -> Result<(), ConformError> {
    let json = baseline.to_json()?;
    let tmp = out_path.with_extension("json.tmp");
    std::fs::write(&tmp, json)?;
    std::fs::rename(&tmp, out_path)?;
    Ok(())
}
