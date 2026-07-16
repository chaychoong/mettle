//! mt-020 — the differential resolve/typecheck gauge (Rung 2's exit).
//!
//! Drives **mettle's own** load+resolve pipeline
//! ([`ModuleGraph::load_with_source`] + [`als_types::resolve`]) over a large
//! body of real Alloy source and emits a deterministic ACCEPT/REJECT verdict
//! per input, so it can be diffed against the reference jar's post-`resolveAll`
//! verdict (the jar side is [`ParseOnlyShim`], whose
//! `parseEverything_fromString` already runs the full `resolveAll` — the same
//! entry point mt-013 used for the parse pass).
//!
//! This bin is the mettle side + the differential; the jar side is one JVM
//! invocation of `ParseOnlyShim` over the `filelist.txt` this bin writes.
//!
//! Subcommands (all deterministic; see `docs/reference/alloy4fun-resolve-pass.md`):
//!
//! - `alloy4fun --corpus <dir> --out <dir> [--threads N] [--limit N]`
//!   Reads every `*.json` under `<dir>` (JSON-Lines alloy4fun records),
//!   extracts and **byte-deduplicates** the `code` field, sorts the unique
//!   codes lexicographically by bytes (fully reproducible, no hashing), writes
//!   each to `<out>/codes/NNNNNN.als`, computes mettle's verdict per code, and
//!   writes `<out>/mettle.jsonl` + `<out>/filelist.txt` (abs paths, index
//!   order). `--limit N` takes the first N by that sort order (an honest,
//!   documented subset).
//!
//! - `paths <list-file> --out <dir>`
//!   For the 167-file corpus: `<list-file>` holds one real `.als` path per
//!   line; each is loaded from disk ([`FilesystemLoader`], multi-file opens
//!   honored) and its mettle verdict written to `<out>/mettle.jsonl` +
//!   `<out>/filelist.txt` (the same paths, for the jar side).
//!
//! - `diff --mettle <mettle.jsonl> --jar <jar.jsonl>`
//!   Joins the two verdict streams by `file` and prints the differential
//!   scorecard (agree-accept / agree-reject / jar-accepts+mettle-rejects /
//!   jar-rejects+mettle-accepts), then lists every disagreement with mettle's
//!   error phase+variant, sorted by file. Exit code 1 if any
//!   jar-accepts+mettle-rejects (drop-in violations) remain.
//!
//! This bin prints and exits (STYLE E3), like `conform.rs`; the library never
//! does.

#![allow(clippy::unwrap_used, clippy::expect_used)]
// A gauge/reporting bin: precision loss in a percentage print is immaterial,
// and JSON line/col fields fit `usize` on any real target.
#![allow(clippy::cast_precision_loss, clippy::cast_possible_truncation)]

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::fs;
use std::io::{BufWriter, Write};
use std::panic::{self, AssertUnwindSafe};
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::thread;

use als_types::{FilesystemLoader, MapLoader, ModuleGraph, ResolveError};

/// One resolve warning as the parity gauge sees it: its class and 1-based
/// (line, col). mt-023.
struct Warn {
    class: &'static str,
    line: usize,
    col: usize,
}

/// mettle's verdict for one input, plus enough detail to bucket a
/// disagreement without re-running.
struct Verdict {
    ok: bool,
    /// `"accept"`, `"parse"`, `"load"`, `"resolve"`, or `"panic"`.
    phase: &'static str,
    /// The `ResolveError` variant name (or `""` on accept, `"<panic>"` on panic).
    variant: &'static str,
    /// Warnings emitted on ACCEPT (mt-023), span-ordered, `(class, line, col)`.
    warnings: Vec<Warn>,
}

impl Verdict {
    fn accept(warnings: Vec<Warn>) -> Self {
        Self {
            ok: true,
            phase: "accept",
            variant: "",
            warnings,
        }
    }
    fn reject(phase: &'static str, variant: &'static str) -> Self {
        Self {
            ok: false,
            phase,
            variant,
            warnings: Vec::new(),
        }
    }
    fn panicked() -> Self {
        Self {
            ok: false,
            phase: "panic",
            variant: "<panic>",
            warnings: Vec::new(),
        }
    }
}

/// 1-based `(line, col)` of byte `offset` in `source`, counting columns in
/// Unicode scalar values (matching mettle's CLI diagnostics and the jar's
/// line/col reporting closely enough for line-granular parity).
fn line_col(source: &str, offset: u32) -> (usize, usize) {
    let off = (offset as usize).min(source.len());
    let mut line = 1usize;
    let mut line_start = 0usize;
    for (i, b) in source.as_bytes().iter().enumerate().take(off) {
        if *b == b'\n' {
            line += 1;
            line_start = i + 1;
        }
    }
    let col = source[line_start..off].chars().count() + 1;
    (line, col)
}

/// The stable short name of a `ResolveError` variant, for bucketing.
fn variant_name(e: &ResolveError) -> &'static str {
    match e {
        ResolveError::OpenedFileParse { .. } => "OpenedFileParse",
        ResolveError::ModuleFileNotFound { .. } => "ModuleFileNotFound",
        ResolveError::CircularImport { .. } => "CircularImport",
        ResolveError::DuplicateAlias { .. } => "DuplicateAlias",
        ResolveError::OpenArgCount { .. } => "OpenArgCount",
        ResolveError::NoneAsOpenArg { .. } => "NoneAsOpenArg",
        ResolveError::OpenParamNotFound { .. } => "OpenParamNotFound",
        ResolveError::DuplicateSig { .. } => "DuplicateSig",
        ResolveError::DuplicateParam { .. } => "DuplicateParam",
        ResolveError::CyclicInheritance { .. } => "CyclicInheritance",
        ResolveError::ParentSigNotFound { .. } => "ParentSigNotFound",
        ResolveError::ExtendsSubsetSig { .. } => "ExtendsSubsetSig",
        ResolveError::DuplicateField { .. } => "DuplicateField",
        ResolveError::FieldBoundHasCall { .. } => "FieldBoundHasCall",
        ResolveError::FieldBoundEmpty { .. } => "FieldBoundEmpty",
        ResolveError::FieldNameClash { .. } => "FieldNameClash",
        ResolveError::UnknownName { .. } => "UnknownName",
        ResolveError::ArityMismatch { .. } => "ArityMismatch",
        ResolveError::AmbiguousName { .. } => "AmbiguousName",
        ResolveError::NotFormula { .. } => "NotFormula",
        ResolveError::NotSet { .. } => "NotSet",
        ResolveError::NotInt { .. } => "NotInt",
        ResolveError::UnaryNotBinary { .. } => "UnaryNotBinary",
        ResolveError::NotUnarySet { .. } => "NotUnarySet",
        ResolveError::IllegalJoin { .. } => "IllegalJoin",
        ResolveError::BadCall { .. } => "BadCall",
        ResolveError::FuncBodyArity { .. } => "FuncBodyArity",
        ResolveError::DuplicateAssert { .. } => "DuplicateAssert",
        ResolveError::DuplicateMacro { .. } => "DuplicateMacro",
        ResolveError::MultipleMacros { .. } => "MultipleMacros",
        ResolveError::MacroTooDeep { .. } => "MacroTooDeep",
        ResolveError::CommandTargetNotFound { .. } => "CommandTargetNotFound",
        ResolveError::CommandTargetAmbiguous { .. } => "CommandTargetAmbiguous",
        ResolveError::ScopeSigNotFound { .. } => "ScopeSigNotFound",
        ResolveError::MutableSigScoped { .. } => "MutableSigScoped",
        ResolveError::ExactScopeOnVar { .. } => "ExactScopeOnVar",
        ResolveError::ExactParamVarSig { .. } => "ExactParamVarSig",
    }
}

/// Runs mettle's full pipeline (load graph → resolve/typecheck) on one root
/// `source` at `path`, using `loader` for transitively-opened files. Wrapped in
/// `catch_unwind` so a single adversarial input cannot abort a batch — a panic
/// is recorded as its own bucket to surface (expectation: zero).
fn mettle_verdict<L: als_types::ModuleLoader>(path: &str, source: String, loader: &L) -> Verdict {
    let result = panic::catch_unwind(AssertUnwindSafe(|| {
        match ModuleGraph::load_with_source(path, source, loader) {
            Ok(graph) => match als_types::resolve(&graph) {
                Ok(resolved) => {
                    // Convert each warning's span → (class, line, col) using the
                    // source of the file it points into (mt-023).
                    let warnings = resolved
                        .warnings
                        .iter()
                        .map(|w| {
                            let span = w.span();
                            let src = &graph.files.file(span.file).source;
                            let (line, col) = line_col(src, span.start);
                            Warn {
                                class: w.class(),
                                line,
                                col,
                            }
                        })
                        .collect();
                    Verdict::accept(warnings)
                }
                Err(e) => Verdict::reject("resolve", variant_name(&e)),
            },
            Err(e) => {
                let phase = if matches!(e, ResolveError::OpenedFileParse { .. }) {
                    "parse"
                } else {
                    "load"
                };
                Verdict::reject(phase, variant_name(&e))
            }
        }
    }));
    result.unwrap_or_else(|_| Verdict::panicked())
}

/// One JSON-Lines verdict record (hand-written JSON; escapes only what a file
/// path / verdict field can contain).
fn write_verdict_line(w: &mut impl Write, file: &str, v: &Verdict) -> std::io::Result<()> {
    let mut warns = String::from("[");
    for (i, wn) in v.warnings.iter().enumerate() {
        if i > 0 {
            warns.push(',');
        }
        let _ = write!(
            warns,
            "{{\"class\":\"{}\",\"line\":{},\"col\":{}}}",
            wn.class, wn.line, wn.col
        );
    }
    warns.push(']');
    writeln!(
        w,
        "{{\"file\":\"{}\",\"ok\":{},\"phase\":\"{}\",\"variant\":\"{}\",\"warnings\":{}}}",
        json_escape(file),
        v.ok,
        v.phase,
        v.variant,
        warns
    )
}

fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 4);
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out
}

// ---------------------------------------------------------------------------
// alloy4fun subcommand
// ---------------------------------------------------------------------------

fn collect_unique_codes(corpus_dir: &Path) -> Vec<String> {
    let mut entries: Vec<PathBuf> = fs::read_dir(corpus_dir)
        .unwrap_or_else(|e| panic!("cannot read corpus dir {}: {e}", corpus_dir.display()))
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "json"))
        .collect();
    entries.sort();

    // Byte-exact dedup: the code text itself is the key (no hashing → no
    // collision risk, exactly reproducible). BTreeSet keeps the unique set
    // sorted by Unicode scalar order == UTF-8 byte order.
    let mut unique: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for path in &entries {
        let text = fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
        for line in text.lines() {
            let line = line.trim();
            if line.is_empty() {
                continue;
            }
            let rec: serde_json::Value = match serde_json::from_str(line) {
                Ok(v) => v,
                Err(_) => continue,
            };
            if let Some(code) = rec.get("code").and_then(|c| c.as_str()) {
                unique.insert(code.to_owned());
            }
        }
    }
    unique.into_iter().collect()
}

fn run_alloy4fun(
    corpus_dir: &Path,
    out_dir: &Path,
    threads: usize,
    limit: Option<usize>,
) -> ExitCode {
    eprintln!("[alloy4fun] reading corpus from {}", corpus_dir.display());
    let mut codes = collect_unique_codes(corpus_dir);
    eprintln!("[alloy4fun] {} unique codes", codes.len());
    if let Some(n) = limit {
        codes.truncate(n);
        eprintln!(
            "[alloy4fun] limited to first {} (by sort order)",
            codes.len()
        );
    }
    let total = codes.len();

    let codes_dir = out_dir.join("codes");
    fs::create_dir_all(&codes_dir).expect("create codes dir");

    // Suppress per-panic backtraces during the batch (we bucket panics
    // ourselves via catch_unwind and report the count).
    panic::set_hook(Box::new(|_| {}));

    let n_threads = threads.max(1).min(total.max(1));
    let chunk = total.div_ceil(n_threads);
    let codes_ref = &codes;
    let codes_dir_ref = &codes_dir;

    let mut results: Vec<(usize, Verdict)> = thread::scope(|scope| {
        let mut handles = Vec::new();
        for t in 0..n_threads {
            let lo = t * chunk;
            let hi = ((t + 1) * chunk).min(total);
            if lo >= hi {
                continue;
            }
            handles.push(scope.spawn(move || {
                let loader = MapLoader::new();
                let mut out = Vec::with_capacity(hi - lo);
                for (offset, code) in codes_ref[lo..hi].iter().enumerate() {
                    let idx = lo + offset;
                    let file = codes_dir_ref.join(format!("{idx:06}.als"));
                    fs::write(&file, code).expect("write code file");
                    let path = file.to_string_lossy().into_owned();
                    let v = mettle_verdict(&path, code.clone(), &loader);
                    out.push((idx, v));
                }
                out
            }));
        }
        let mut all = Vec::new();
        for h in handles {
            all.extend(h.join().expect("thread join"));
        }
        all
    });

    let _ = panic::take_hook();
    results.sort_by_key(|(idx, _)| *idx);

    // Emit filelist.txt (abs paths, index order) and mettle.jsonl.
    let filelist = out_dir.join("filelist.txt");
    let mut fl = BufWriter::new(fs::File::create(&filelist).expect("create filelist"));
    let mettle_out = out_dir.join("mettle.jsonl");
    let mut mo = BufWriter::new(fs::File::create(&mettle_out).expect("create mettle.jsonl"));

    let mut n_accept = 0usize;
    let mut n_panic = 0usize;
    for (idx, v) in &results {
        let file = codes_dir.join(format!("{idx:06}.als"));
        let abs = fs::canonicalize(&file).unwrap_or(file);
        let abs = abs.to_string_lossy();
        writeln!(fl, "{abs}").expect("write filelist");
        write_verdict_line(&mut mo, &abs, v).expect("write verdict");
        if v.ok {
            n_accept += 1;
        }
        if v.phase == "panic" {
            n_panic += 1;
        }
    }
    fl.flush().ok();
    mo.flush().ok();

    eprintln!(
        "[alloy4fun] mettle: {} accept, {} reject, {} panic (of {})",
        n_accept,
        total - n_accept,
        n_panic,
        total
    );
    eprintln!("[alloy4fun] wrote {}", mettle_out.display());
    eprintln!("[alloy4fun] wrote {}", filelist.display());
    eprintln!(
        "[alloy4fun] next: java -cp <shim>:<jar> ParseOnlyShim {} > {}/jar.jsonl",
        filelist.display(),
        out_dir.display()
    );
    if n_panic > 0 {
        eprintln!("[alloy4fun] WARNING: {n_panic} panics — investigate");
        return ExitCode::from(1);
    }
    ExitCode::SUCCESS
}

// ---------------------------------------------------------------------------
// paths subcommand (corpus: real .als files, multi-file opens)
// ---------------------------------------------------------------------------

fn run_paths(list_file: &Path, out_dir: &Path) -> ExitCode {
    let text = fs::read_to_string(list_file)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", list_file.display()));
    let paths: Vec<String> = text
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .map(str::to_owned)
        .collect();

    fs::create_dir_all(out_dir).expect("create out dir");
    let mettle_out = out_dir.join("mettle.jsonl");
    let mut mo = BufWriter::new(fs::File::create(&mettle_out).expect("create mettle.jsonl"));
    let filelist = out_dir.join("filelist.txt");
    let mut fl = BufWriter::new(fs::File::create(&filelist).expect("create filelist"));

    let loader = FilesystemLoader::new();
    let mut n_accept = 0usize;
    for p in &paths {
        let abs =
            fs::canonicalize(p).map_or_else(|_| p.clone(), |a| a.to_string_lossy().into_owned());
        let source = match fs::read_to_string(&abs) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("[paths] cannot read {abs}: {e}");
                continue;
            }
        };
        let v = mettle_verdict(&abs, source, &loader);
        if v.ok {
            n_accept += 1;
        }
        writeln!(fl, "{abs}").expect("write filelist");
        write_verdict_line(&mut mo, &abs, &v).expect("write verdict");
    }
    fl.flush().ok();
    mo.flush().ok();
    eprintln!(
        "[paths] mettle: {} accept, {} reject (of {})",
        n_accept,
        paths.len() - n_accept,
        paths.len()
    );
    eprintln!("[paths] wrote {}", mettle_out.display());
    eprintln!("[paths] wrote {}", filelist.display());
    ExitCode::SUCCESS
}

// ---------------------------------------------------------------------------
// diff subcommand
// ---------------------------------------------------------------------------

/// A parsed verdict line from either side.
struct Row {
    ok: bool,
    phase: String,
    variant: String,
}

fn read_jsonl(path: &Path) -> BTreeMap<String, Row> {
    let text =
        fs::read_to_string(path).unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
    let mut map = BTreeMap::new();
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let v: serde_json::Value = serde_json::from_str(line)
            .unwrap_or_else(|e| panic!("bad json line in {}: {e}", path.display()));
        let file = v
            .get("file")
            .and_then(|f| f.as_str())
            .expect("verdict line missing `file`")
            .to_owned();
        let ok = v
            .get("ok")
            .and_then(serde_json::Value::as_bool)
            .unwrap_or(false);
        let phase = v
            .get("phase")
            .and_then(|p| p.as_str())
            .unwrap_or("")
            .to_owned();
        let variant = v
            .get("variant")
            .and_then(|p| p.as_str())
            .or_else(|| v.get("category").and_then(|p| p.as_str()))
            .unwrap_or("")
            .to_owned();
        map.insert(file, Row { ok, phase, variant });
    }
    map
}

fn run_diff(mettle_path: &Path, jar_path: &Path) -> ExitCode {
    let mettle = read_jsonl(mettle_path);
    let jar = read_jsonl(jar_path);

    let mut agree_accept = 0usize;
    let mut agree_reject = 0usize;
    // jar ACCEPT, mettle REJECT — drop-in violations.
    let mut jar_accept_mettle_reject: Vec<(&String, &Row)> = Vec::new();
    // jar REJECT, mettle ACCEPT — over-acceptance (ADR-0009 debt + new bugs).
    let mut jar_reject_mettle_accept: Vec<(&String, &Row)> = Vec::new();
    let mut missing = 0usize;

    for (file, m) in &mettle {
        let Some(j) = jar.get(file) else {
            missing += 1;
            continue;
        };
        match (j.ok, m.ok) {
            (true, true) => agree_accept += 1,
            (false, false) => agree_reject += 1,
            (true, false) => jar_accept_mettle_reject.push((file, m)),
            (false, true) => jar_reject_mettle_accept.push((file, j)),
        }
    }

    let total = agree_accept
        + agree_reject
        + jar_accept_mettle_reject.len()
        + jar_reject_mettle_accept.len();
    println!("=== mt-020 differential resolve/typecheck gauge ===");
    println!("compared           : {total}");
    println!("agree ACCEPT       : {agree_accept}");
    println!("agree REJECT       : {agree_reject}");
    println!(
        "jar ACCEPT / mettle REJECT (drop-in violations) : {}",
        jar_accept_mettle_reject.len()
    );
    println!(
        "jar REJECT / mettle ACCEPT (over-acceptance)    : {}",
        jar_reject_mettle_accept.len()
    );
    if missing > 0 {
        println!("(mettle rows with no jar row: {missing})");
    }
    let agree = agree_accept + agree_reject;
    if total > 0 {
        println!(
            "agreement          : {}/{} = {:.4}%",
            agree,
            total,
            100.0 * agree as f64 / total as f64
        );
    }

    // Bucket the over-acceptances by mettle's would-be phase is not available
    // (mettle accepted); bucket the drop-in violations by mettle's phase+variant.
    if !jar_accept_mettle_reject.is_empty() {
        println!("\n--- jar ACCEPT / mettle REJECT (fix all) ---");
        let mut by_variant: BTreeMap<(&str, &str), usize> = BTreeMap::new();
        for (_, m) in &jar_accept_mettle_reject {
            *by_variant
                .entry((m.phase.as_str(), m.variant.as_str()))
                .or_default() += 1;
        }
        for ((phase, variant), n) in &by_variant {
            println!("  {phase:8} {variant:24} {n}");
        }
        println!("  files:");
        for (file, m) in &jar_accept_mettle_reject {
            println!("    {} [{}/{}]", file, m.phase, m.variant);
        }
    }

    if !jar_reject_mettle_accept.is_empty() {
        println!("\n--- jar REJECT / mettle ACCEPT (measure) ---");
        let mut by_cat: BTreeMap<&str, usize> = BTreeMap::new();
        for (_, j) in &jar_reject_mettle_accept {
            *by_cat.entry(j.variant.as_str()).or_default() += 1;
        }
        for (cat, n) in &by_cat {
            println!("  jar-category {cat:24} {n}");
        }
    }

    if jar_accept_mettle_reject.is_empty() {
        ExitCode::SUCCESS
    } else {
        ExitCode::from(1)
    }
}

// ---------------------------------------------------------------------------
// warn-diff subcommand (mt-023 warning parity)
// ---------------------------------------------------------------------------

/// One side's warnings for a file, as `(class, line, col)` triples.
type WarnSet = Vec<(String, usize, usize)>;

/// Reads a verdict jsonl, returning per-file `(ok, warnings)`. mettle warnings
/// carry `class`; jar warnings carry `message` (mapped to a class via
/// [`als_types::jar_stem_class`]) — `jar` selects which. Unclassifiable jar
/// stems are collected into `unclassified`.
fn read_warn_jsonl(
    path: &Path,
    jar: bool,
    unclassified: &mut BTreeMap<String, usize>,
) -> BTreeMap<String, (bool, WarnSet)> {
    let text =
        fs::read_to_string(path).unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
    let mut map = BTreeMap::new();
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let v: serde_json::Value = serde_json::from_str(line)
            .unwrap_or_else(|e| panic!("bad json line in {}: {e}", path.display()));
        let file = v
            .get("file")
            .and_then(|f| f.as_str())
            .expect("verdict line missing `file`")
            .to_owned();
        let ok = v
            .get("ok")
            .and_then(serde_json::Value::as_bool)
            .unwrap_or(false);
        let mut ws: WarnSet = Vec::new();
        if let Some(arr) = v.get("warnings").and_then(|w| w.as_array()) {
            for w in arr {
                let line_no = w
                    .get("line")
                    .and_then(serde_json::Value::as_u64)
                    .unwrap_or(0) as usize;
                let col = w
                    .get("col")
                    .and_then(serde_json::Value::as_u64)
                    .unwrap_or(0) as usize;
                let class = if jar {
                    let msg = w.get("message").and_then(|m| m.as_str()).unwrap_or("");
                    if let Some(c) = als_types::jar_stem_class(msg) {
                        c.to_owned()
                    } else {
                        *unclassified
                            .entry(msg.lines().next().unwrap_or("").to_owned())
                            .or_default() += 1;
                        continue;
                    }
                } else {
                    w.get("class")
                        .and_then(|c| c.as_str())
                        .unwrap_or("")
                        .to_owned()
                };
                ws.push((class, line_no, col));
            }
        }
        map.insert(file, (ok, ws));
    }
    map
}

/// Deduplicated `(class, line)` set — the primary parity key (§8: positions may
/// differ in column between the reference's operator `Pos` and mettle's node
/// span, so parity is matched at line granularity; see warning-parity.md).
fn class_line_set(ws: &WarnSet) -> std::collections::BTreeSet<(String, usize)> {
    ws.iter().map(|(c, l, _)| (c.clone(), *l)).collect()
}

#[allow(clippy::too_many_lines)]
fn run_warn_diff(mettle_path: &Path, jar_path: &Path) -> ExitCode {
    let mut unclassified: BTreeMap<String, usize> = BTreeMap::new();
    let mettle = read_warn_jsonl(mettle_path, false, &mut unclassified);
    let jar = read_warn_jsonl(jar_path, true, &mut unclassified);

    let mut agree_accept = 0usize;
    let mut files_exact = 0usize;
    let mut files_with_missing = 0usize;
    let mut files_with_extra = 0usize;
    let mut col_matched = 0usize; // (class,line,col) exact among matched (class,line)
    let mut line_matched = 0usize; // matched (class,line) pairs
    let mut missing_by_class: BTreeMap<String, usize> = BTreeMap::new();
    let mut extra_by_class: BTreeMap<String, usize> = BTreeMap::new();
    let mut missing_examples: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut extra_examples: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut jar_total = 0usize;
    let mut mettle_total = 0usize;

    for (file, (m_ok, m_ws)) in &mettle {
        let Some((j_ok, j_ws)) = jar.get(file) else {
            continue;
        };
        if !(*m_ok && *j_ok) {
            continue; // parity only defined on agree-ACCEPT files.
        }
        agree_accept += 1;
        let m_set = class_line_set(m_ws);
        let j_set = class_line_set(j_ws);
        jar_total += j_set.len();
        mettle_total += m_set.len();

        let missing: Vec<_> = j_set.difference(&m_set).cloned().collect();
        let extra: Vec<_> = m_set.difference(&j_set).cloned().collect();
        if missing.is_empty() && extra.is_empty() {
            files_exact += 1;
        }
        if !missing.is_empty() {
            files_with_missing += 1;
        }
        if !extra.is_empty() {
            files_with_extra += 1;
        }
        for (class, line) in &missing {
            *missing_by_class.entry(class.clone()).or_default() += 1;
            let ex = missing_examples.entry(class.clone()).or_default();
            if ex.len() < 5 {
                ex.push(format!("{file}:{line}"));
            }
        }
        for (class, line) in &extra {
            *extra_by_class.entry(class.clone()).or_default() += 1;
            let ex = extra_examples.entry(class.clone()).or_default();
            if ex.len() < 5 {
                ex.push(format!("{file}:{line}"));
            }
        }
        // Column agreement among (class,line) pairs present on both sides.
        for (class, line) in m_set.intersection(&j_set) {
            line_matched += 1;
            let m_col = m_ws
                .iter()
                .find(|(c, l, _)| c == class && l == line)
                .map(|(_, _, col)| *col);
            let j_col = j_ws
                .iter()
                .find(|(c, l, _)| c == class && l == line)
                .map(|(_, _, col)| *col);
            if m_col == j_col {
                col_matched += 1;
            }
        }
    }

    println!("=== mt-023 warning-parity gauge (agree-ACCEPT files) ===");
    println!("agree-ACCEPT files           : {agree_accept}");
    println!("files with identical warn set: {files_exact}");
    println!(
        "files mettle-MISSING a warn  : {files_with_missing}  (LEDGER-002 direction — drive to 0)"
    );
    println!("files mettle-EXTRA a warn    : {files_with_extra}");
    println!("jar (class,line) warnings    : {jar_total}");
    println!("mettle (class,line) warnings : {mettle_total}");
    println!("matched (class,line) pairs   : {line_matched}  ({col_matched} also column-exact)");

    if !missing_by_class.is_empty() {
        println!("\n--- mettle-MISSING by class (fix all) ---");
        for (class, n) in &missing_by_class {
            println!("  {class:24} {n}");
            if let Some(ex) = missing_examples.get(class) {
                for e in ex {
                    println!("      e.g. {e}");
                }
            }
        }
    }
    if !extra_by_class.is_empty() {
        println!("\n--- mettle-EXTRA by class (triage) ---");
        for (class, n) in &extra_by_class {
            println!("  {class:24} {n}");
            if let Some(ex) = extra_examples.get(class) {
                for e in ex {
                    println!("      e.g. {e}");
                }
            }
        }
    }
    if !unclassified.is_empty() {
        println!("\n--- UNCLASSIFIED jar stems (extend the stem table!) ---");
        for (stem, n) in &unclassified {
            println!("  {n:6} {stem}");
        }
    }

    // Exit 1 if any mettle-missing remains (the LEDGER-002 conformance gate).
    if missing_by_class.is_empty() {
        ExitCode::SUCCESS
    } else {
        ExitCode::from(1)
    }
}

// ---------------------------------------------------------------------------
// main / arg parsing
// ---------------------------------------------------------------------------

fn opt(args: &[String], flag: &str) -> Option<String> {
    args.iter()
        .position(|a| a == flag)
        .and_then(|i| args.get(i + 1))
        .cloned()
}

fn usage() -> ExitCode {
    eprintln!(
        "usage:\n\
         \x20 resolve-gauge alloy4fun --corpus <dir> --out <dir> [--threads N] [--limit N]\n\
         \x20 resolve-gauge paths <list-file> --out <dir>\n\
         \x20 resolve-gauge diff --mettle <mettle.jsonl> --jar <jar.jsonl>\n\
         \x20 resolve-gauge warn-diff --mettle <mettle.jsonl> --jar <jar.jsonl>"
    );
    ExitCode::from(2)
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let Some(cmd) = args.first() else {
        return usage();
    };
    match cmd.as_str() {
        "alloy4fun" => {
            let (Some(corpus), Some(out)) = (opt(&args, "--corpus"), opt(&args, "--out")) else {
                return usage();
            };
            let threads = opt(&args, "--threads")
                .and_then(|s| s.parse().ok())
                .unwrap_or_else(|| {
                    thread::available_parallelism().map_or(4, std::num::NonZero::get)
                });
            let limit = opt(&args, "--limit").and_then(|s| s.parse().ok());
            run_alloy4fun(Path::new(&corpus), Path::new(&out), threads, limit)
        }
        "paths" => {
            let Some(list) = args.get(1).filter(|a| !a.starts_with("--")) else {
                return usage();
            };
            let Some(out) = opt(&args, "--out") else {
                return usage();
            };
            run_paths(Path::new(list), Path::new(&out))
        }
        "diff" => {
            let (Some(m), Some(j)) = (opt(&args, "--mettle"), opt(&args, "--jar")) else {
                return usage();
            };
            run_diff(Path::new(&m), Path::new(&j))
        }
        "warn-diff" => {
            let (Some(m), Some(j)) = (opt(&args, "--mettle"), opt(&args, "--jar")) else {
                return usage();
            };
            run_warn_diff(Path::new(&m), Path::new(&j))
        }
        _ => usage(),
    }
}
