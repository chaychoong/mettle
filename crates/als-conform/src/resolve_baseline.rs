//! Cached reference-jar **resolve-verdict** baseline (mt-110).
//!
//! The jar's ACCEPT/REJECT answer for a fixed body of source at a fixed jar is
//! an immutable fact, but every resolver gate re-derived it with a live ~4-minute
//! JVM pass over the 150,891 alloy4fun codes. This module defines the on-disk
//! format for banking that pass (`baselines/alloy4fun-resolve.txt`), so
//! `resolve-gauge diff --jar-baseline` answers in seconds — the mt-054 count
//! baseline's bargain (`solve_gauge::count_baseline`), applied to the resolve
//! gauge.
//!
//! **Format.** A `#`-comment header of `key: value` lines, then one line per
//! jar-**rejected** code, in index order:
//!
//! ```text
//! 000012 resolve 3:9 The name "add" cannot be found.
//! ```
//!
//! Accepts are implicit — they are two thirds of the corpus, and recording them
//! would treble the artifact for no information. Only the first line of a jar
//! message is kept (several span three), which is enough to bucket a family.
//!
//! **Config-mismatch is a hard error, never a silent skip** (the count
//! baseline's rule): the header pins the corpus by SHA-256 over the extracted
//! code bytes in index order plus the code count, and the jar by the SHA-256
//! `docs/reference/alloy6-reference.md` pins it by. A baseline loaded against a
//! corpus it was not produced from would silently compare row *i* of one corpus
//! against row *i* of another, which is worse than no baseline at all.
//!
//! Everything is `BTreeMap`-ordered and the digests are content-only, so the
//! rendered artifact is byte-identical run to run (STYLE D1). This module never
//! prints (STYLE E3).

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::fs;
use std::io::Read;
use std::path::Path;

use sha2::{Digest, Sha256};

use crate::error::ConformError;

/// The pinned identity a baseline was produced at. Every field is compared at
/// load; the two content digests are hard gates, the rest is provenance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolveBaselineHeader {
    /// SHA-256 of the oracle jar the verdicts came from.
    pub jar_sha256: String,
    /// Number of extracted codes the run covered.
    pub codes: usize,
    /// SHA-256 over the extracted code files' bytes, concatenated in index
    /// order (the `alloy4fun` subcommand's byte-sorted dedup order).
    pub corpus_sha256: String,
    /// `YYYY-MM-DD` the baseline was baked.
    pub generated: String,
    /// The command that produced it, for reproduction.
    pub command: String,
}

/// One jar reject: its phase (`parse`/`resolve`), 1-based position, and the
/// first line of the jar's message.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RejectRow {
    pub phase: String,
    pub line: usize,
    pub col: usize,
    pub message: String,
}

/// A whole baseline: header plus the jar's rejects keyed by code index.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolveBaseline {
    pub header: ResolveBaselineHeader,
    /// Jar-rejected code indices → the reject. Every index below
    /// `header.codes` that is absent was ACCEPTED by the jar.
    pub rejects: BTreeMap<usize, RejectRow>,
}

/// The hex SHA-256 of a file's bytes, read in 64 KiB chunks so a 40 MB jar
/// never lands in memory whole.
///
/// # Errors
/// If the file cannot be read.
pub fn sha256_file(path: &Path) -> Result<String, ConformError> {
    let mut file = fs::File::open(path)?;
    let mut hasher = Sha256::new();
    let mut buf = vec![0u8; 64 * 1024];
    loop {
        let n = file.read(&mut buf)?;
        if n == 0 {
            break;
        }
        hasher.update(&buf[..n]);
    }
    Ok(hex(&hasher.finalize()))
}

/// The hex SHA-256 over `paths`' bytes concatenated **in the given order** —
/// the corpus fingerprint. Order is part of the identity: the baseline keys
/// rows by index, so a corpus with the same bytes in a different order is a
/// different corpus.
///
/// # Errors
/// If any file cannot be read.
pub fn sha256_corpus(paths: &[String]) -> Result<String, ConformError> {
    let mut hasher = Sha256::new();
    for p in paths {
        hasher.update(fs::read(p)?);
    }
    Ok(hex(&hasher.finalize()))
}

fn hex(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        let _ = write!(out, "{b:02x}");
    }
    out
}

impl ResolveBaseline {
    /// Renders the artifact: header comments, then one line per reject in index
    /// order.
    #[must_use]
    pub fn render(&self) -> String {
        let h = &self.header;
        let mut out = String::with_capacity(self.rejects.len() * 80 + 1024);
        out.push_str("# mettle resolve-verdict baseline (reference-jar side, mt-110)\n");
        out.push_str("#\n");
        let _ = writeln!(out, "# jar-sha256: {}", h.jar_sha256);
        let _ = writeln!(out, "# codes: {}", h.codes);
        let _ = writeln!(out, "# corpus-sha256: {}", h.corpus_sha256);
        let _ = writeln!(out, "# generated: {}", h.generated);
        let _ = writeln!(out, "# command: {}", h.command);
        out.push_str("#\n");
        out.push_str("# One line per jar-REJECTED code: `<index> <phase> <line>:<col> <first line of jar message>`.\n");
        out.push_str("# Indices not listed were ACCEPTED by the jar.\n");
        for (idx, r) in &self.rejects {
            let _ = writeln!(
                out,
                "{idx:06} {} {}:{} {}",
                r.phase, r.line, r.col, r.message
            );
        }
        out
    }

    /// Parses a rendered baseline.
    ///
    /// # Errors
    /// [`ConformError::ResolveBaselineParse`] if a header field is missing or a
    /// row is malformed — a half-understood baseline is not usable.
    pub fn parse(text: &str) -> Result<Self, ConformError> {
        let mut fields: BTreeMap<&str, &str> = BTreeMap::new();
        let mut rejects = BTreeMap::new();
        for (n, raw) in text.lines().enumerate() {
            let line = raw.trim_end();
            if line.is_empty() {
                continue;
            }
            if let Some(comment) = line.strip_prefix('#') {
                if let Some((k, v)) = comment.split_once(':') {
                    fields.insert(k.trim(), v.trim());
                }
                continue;
            }
            let (idx, row) = parse_row(line, n + 1)?;
            rejects.insert(idx, row);
        }
        let header = ResolveBaselineHeader {
            jar_sha256: field(&fields, "jar-sha256")?.to_owned(),
            codes: field(&fields, "codes")?.parse().map_err(|_| {
                ConformError::ResolveBaselineParse {
                    detail: "header `codes` is not a number".to_owned(),
                }
            })?,
            corpus_sha256: field(&fields, "corpus-sha256")?.to_owned(),
            generated: field(&fields, "generated")?.to_owned(),
            command: field(&fields, "command")?.to_owned(),
        };
        Ok(Self { header, rejects })
    }

    /// Checks the baseline against the extraction it is about to answer for:
    /// same number of codes, same bytes in the same order.
    ///
    /// # Errors
    /// [`ConformError::ResolveBaselineMismatch`] on either — never a warning:
    /// row *i* of a different corpus is a different model.
    pub fn verify_corpus(&self, code_paths: &[String]) -> Result<(), ConformError> {
        if code_paths.len() != self.header.codes {
            return Err(ConformError::ResolveBaselineMismatch {
                field: "codes".to_owned(),
                expected: self.header.codes.to_string(),
                actual: code_paths.len().to_string(),
            });
        }
        let digest = sha256_corpus(code_paths)?;
        if digest != self.header.corpus_sha256 {
            return Err(ConformError::ResolveBaselineMismatch {
                field: "corpus-sha256".to_owned(),
                expected: self.header.corpus_sha256.clone(),
                actual: digest,
            });
        }
        Ok(())
    }

    /// Checks the baseline against the oracle jar at `jar_path`.
    ///
    /// # Errors
    /// [`ConformError::ResolveBaselineMismatch`] if the jar's digest differs —
    /// a different jar is a different oracle.
    pub fn verify_jar(&self, jar_path: &Path) -> Result<(), ConformError> {
        let digest = sha256_file(jar_path)?;
        if digest != self.header.jar_sha256 {
            return Err(ConformError::ResolveBaselineMismatch {
                field: "jar-sha256".to_owned(),
                expected: self.header.jar_sha256.clone(),
                actual: digest,
            });
        }
        Ok(())
    }
}

fn field<'a>(fields: &BTreeMap<&str, &'a str>, key: &str) -> Result<&'a str, ConformError> {
    fields
        .get(key)
        .copied()
        .ok_or_else(|| ConformError::ResolveBaselineParse {
            detail: format!("header is missing `{key}`"),
        })
}

/// `<index> <phase> <line>:<col> <message>` — the message may be empty and may
/// itself contain spaces and colons, so only the first three fields are split.
fn parse_row(line: &str, lineno: usize) -> Result<(usize, RejectRow), ConformError> {
    let bad = |what: &str| ConformError::ResolveBaselineParse {
        detail: format!("line {lineno}: {what}"),
    };
    let mut it = line.splitn(4, ' ');
    let idx: usize = it
        .next()
        .ok_or_else(|| bad("empty row"))?
        .parse()
        .map_err(|_| bad("index is not a number"))?;
    let phase = it.next().ok_or_else(|| bad("missing phase"))?;
    let pos = it.next().ok_or_else(|| bad("missing line:col"))?;
    let (l, c) = pos
        .split_once(':')
        .ok_or_else(|| bad("malformed line:col"))?;
    Ok((
        idx,
        RejectRow {
            phase: phase.to_owned(),
            line: l.parse().map_err(|_| bad("line is not a number"))?,
            col: c.parse().map_err(|_| bad("col is not a number"))?,
            message: it.next().unwrap_or("").to_owned(),
        },
    ))
}

/// Today's UTC date as `YYYY-MM-DD`, for the header's provenance stamp. Wall
/// clock never reaches a verdict here — the stamp is read by humans only, and
/// the two digests are what the loader actually enforces (STYLE D4).
#[must_use]
pub fn today_utc() -> String {
    crate::status::fmt_unix_utc(crate::status::unix_secs())
        .chars()
        .take(10)
        .collect()
}

/// The first line of a jar message, with control characters dropped — the
/// artifact is line-oriented, so an embedded newline would forge a row.
#[must_use]
pub fn first_line(message: &str) -> String {
    message
        .split(['\n', '\r'])
        .next()
        .unwrap_or("")
        .trim_end()
        .chars()
        .filter(|c| !c.is_control())
        .collect()
}

#[cfg(test)]
#[allow(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "test fixtures assert on known-good values"
)]
mod tests {
    use super::*;

    fn sample() -> ResolveBaseline {
        let mut rejects = BTreeMap::new();
        rejects.insert(
            7,
            RejectRow {
                phase: "resolve".to_owned(),
                line: 3,
                col: 9,
                message: "The name \"add\" cannot be found.".to_owned(),
            },
        );
        rejects.insert(
            1234,
            RejectRow {
                phase: "parse".to_owned(),
                line: 1,
                col: 1,
                message: String::new(),
            },
        );
        ResolveBaseline {
            header: ResolveBaselineHeader {
                jar_sha256: "aa".repeat(32),
                codes: 5000,
                corpus_sha256: "bb".repeat(32),
                generated: "2026-08-23".to_owned(),
                command: "resolve-gauge bake-baseline ...".to_owned(),
            },
            rejects,
        }
    }

    #[test]
    fn render_parse_round_trips() {
        let b = sample();
        let parsed = ResolveBaseline::parse(&b.render()).expect("parse");
        assert_eq!(parsed, b);
    }

    #[test]
    fn render_is_stable() {
        assert_eq!(sample().render(), sample().render());
        assert!(sample().render().contains("\n000007 resolve 3:9 The name"));
    }

    #[test]
    fn missing_header_field_is_an_error() {
        let text = sample()
            .render()
            .lines()
            .filter(|l| !l.starts_with("# corpus-sha256"))
            .collect::<Vec<_>>()
            .join("\n");
        let e = ResolveBaseline::parse(&text).expect_err("missing field must fail");
        assert!(
            matches!(&e, ConformError::ResolveBaselineParse { detail } if detail.contains("corpus-sha256")),
            "{e:?}"
        );
    }

    #[test]
    fn a_doctored_count_header_fails_the_corpus_check() {
        let b = sample();
        let e = b
            .verify_corpus(&["/nonexistent".to_owned()])
            .expect_err("count mismatch must fail");
        assert!(
            matches!(&e, ConformError::ResolveBaselineMismatch { field, .. } if field == "codes"),
            "{e:?}"
        );
    }

    #[test]
    fn corpus_digest_follows_content_and_order() {
        let dir = std::env::temp_dir().join("mt110-baseline-digest-test");
        let _ = fs::create_dir_all(&dir);
        let a = dir.join("a.als");
        let b = dir.join("b.als");
        fs::write(&a, "sig A {}\n").expect("write a");
        fs::write(&b, "sig B {}\n").expect("write b");
        let (pa, pb) = (
            a.to_string_lossy().into_owned(),
            b.to_string_lossy().into_owned(),
        );
        let ab = sha256_corpus(&[pa.clone(), pb.clone()]).expect("digest ab");
        let ba = sha256_corpus(&[pb, pa]).expect("digest ba");
        assert_ne!(ab, ba, "order is part of the corpus identity");
        assert_eq!(ab.len(), 64);
    }

    #[test]
    fn first_line_cannot_forge_a_row() {
        assert_eq!(
            first_line("This must be a set or relation.\n000001 resolve 1:1 forged"),
            "This must be a set or relation."
        );
        assert_eq!(first_line(""), "");
    }
}
