//! Cached reference-jar **warning-parity** baseline (mt-118).
//!
//! `resolve-gauge warn-diff` (mt-023) needs the jar's per-file warning arrays
//! on top of its ACCEPT/REJECT verdict, but a live jar pass over the 150,891
//! alloy4fun codes is a several-minute JVM run. The jar's warnings for a fixed
//! body of source at a fixed jar are an immutable fact, exactly like the
//! resolve-verdict baseline ([`crate::resolve_baseline`]) this format sits
//! beside — the same bargain, applied to warnings.
//!
//! **Format.** A `#`-comment header of `key: value` lines (plus informational
//! comment lines, ignored by [`WarningsBaseline::parse`]), then one line per
//! jar-**ACCEPTED** code that has at least one warning, sorted by code id:
//!
//! ```text
//! 000012 unused-var@3:9 eq-redundant@5:12
//! ```
//!
//! A code id is the corpus extraction's file stem (`codes/NNNNNN.als` →
//! `NNNNNN`, matching [`crate::resolve_baseline::ResolveBaseline`]'s index
//! scheme). Warnings on a row are `<class>@<line>:<col>` tokens, sorted by
//! `(class, line, col)`.
//!
//! Two things are implicit and never written down:
//! - A jar-ACCEPTED code id absent from this file was accepted with **zero**
//!   warnings — recording it would roughly double the artifact (most
//!   agree-ACCEPT files carry no warnings) for no information.
//! - jar-**REJECTED** code ids never appear here at all; jar verdicts live in
//!   `baselines/alloy4fun-resolve.txt`, and a REJECTED file has no warning
//!   array to speak of. Deriving "is this id jar-ACCEPT" is the resolve
//!   baseline's job, not this one's.
//!
//! Everything is `BTreeMap`-ordered, so the rendered artifact is
//! byte-identical run to run (STYLE D1). This module never prints (STYLE E3).

use std::collections::BTreeMap;
use std::fmt::Write as _;

use crate::error::ConformError;

/// The pinned identity a warnings baseline was produced at. Provenance only —
/// unlike [`crate::resolve_baseline::ResolveBaselineHeader`] this format keys
/// rows by code id rather than position, so there is no corpus-order hazard
/// to gate on.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WarningsBaselineHeader {
    /// SHA-256 of the oracle jar the warnings came from.
    pub jar_sha256: String,
    /// `YYYY-MM-DD` the baseline was baked.
    pub generated: String,
    /// The command that produced it, for reproduction.
    pub command: String,
}

/// One warning: its parity class ([`als_types::ResolveWarning::class`] /
/// [`als_types::jar_stem_class`]) and 1-based `(line, col)`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct WarningRow {
    pub class: String,
    pub line: usize,
    pub col: usize,
}

/// A whole baseline: header plus every jar-ACCEPTED code id that has at least
/// one warning, mapped to its (class, line, col)-sorted warning list.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WarningsBaseline {
    pub header: WarningsBaselineHeader,
    /// Code id → its warnings, sorted `(class, line, col)`. A jar-ACCEPTED
    /// code id absent here had zero warnings; a jar-REJECTED id never
    /// appears.
    pub warnings: BTreeMap<String, Vec<WarningRow>>,
}

impl WarningsBaseline {
    /// Renders the artifact: header comments, then one line per code id with
    /// warnings, in code-id order.
    #[must_use]
    pub fn render(&self) -> String {
        let h = &self.header;
        let total: usize = self.warnings.values().map(Vec::len).sum();
        let mut out = String::with_capacity(total * 24 + 1024);
        out.push_str("# mettle jar warning baseline (reference-jar side, mt-118)\n");
        out.push_str("#\n");
        let _ = writeln!(out, "# jar-sha256: {}", h.jar_sha256);
        let _ = writeln!(out, "# generated: {}", h.generated);
        let _ = writeln!(out, "# command: {}", h.command);
        out.push_str("#\n");
        let _ = writeln!(out, "# accepted-with-warnings: {}", self.warnings.len());
        let _ = writeln!(out, "# total-warnings: {total}");
        out.push_str("#\n");
        out.push_str("# One line per jar-ACCEPTED code with >=1 warning:\n");
        out.push_str("# `<code-id> <class>@<line>:<col> <class>@<line>:<col> ...`\n");
        out.push_str("# Warnings sorted (class, line, col); rows sorted by code id.\n");
        out.push_str("# A jar-ACCEPTED code id absent here has zero warnings. jar-REJECTED\n");
        out.push_str("# code ids never appear (see baselines/alloy4fun-resolve.txt for those).\n");
        for (id, ws) in &self.warnings {
            out.push_str(id);
            for w in ws {
                let _ = write!(out, " {}@{}:{}", w.class, w.line, w.col);
            }
            out.push('\n');
        }
        out
    }

    /// Parses a rendered baseline.
    ///
    /// # Errors
    /// [`ConformError::WarningsBaselineParse`] if a required header field is
    /// missing or a row is malformed — a half-understood baseline is not
    /// usable.
    pub fn parse(text: &str) -> Result<Self, ConformError> {
        let mut fields: BTreeMap<&str, &str> = BTreeMap::new();
        let mut warnings = BTreeMap::new();
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
            let (id, ws) = parse_row(line, n + 1)?;
            warnings.insert(id, ws);
        }
        let header = WarningsBaselineHeader {
            jar_sha256: field(&fields, "jar-sha256")?.to_owned(),
            generated: field(&fields, "generated")?.to_owned(),
            command: field(&fields, "command")?.to_owned(),
        };
        Ok(Self { header, warnings })
    }
}

fn field<'a>(fields: &BTreeMap<&str, &'a str>, key: &str) -> Result<&'a str, ConformError> {
    fields
        .get(key)
        .copied()
        .ok_or_else(|| ConformError::WarningsBaselineParse {
            detail: format!("header is missing `{key}`"),
        })
}

/// `<code-id> <class>@<line>:<col> ...` — the code id is the first
/// whitespace-delimited token, everything after it is a `class@line:col`
/// token.
fn parse_row(line: &str, lineno: usize) -> Result<(String, Vec<WarningRow>), ConformError> {
    let bad = |what: &str| ConformError::WarningsBaselineParse {
        detail: format!("line {lineno}: {what}"),
    };
    let mut it = line.split_whitespace();
    let id = it.next().ok_or_else(|| bad("empty row"))?.to_owned();
    let mut ws = Vec::new();
    for token in it {
        let (class, pos) = token
            .split_once('@')
            .ok_or_else(|| bad(&format!("malformed warning token `{token}`")))?;
        let (l, c) = pos
            .split_once(':')
            .ok_or_else(|| bad(&format!("malformed line:col in `{token}`")))?;
        ws.push(WarningRow {
            class: class.to_owned(),
            line: l
                .parse()
                .map_err(|_| bad(&format!("line is not a number in `{token}`")))?,
            col: c
                .parse()
                .map_err(|_| bad(&format!("col is not a number in `{token}`")))?,
        });
    }
    if ws.is_empty() {
        return Err(bad("row has a code id but no warnings"));
    }
    Ok((id, ws))
}

#[cfg(test)]
#[allow(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "test fixtures assert on known-good values"
)]
mod tests {
    use super::*;

    fn sample() -> WarningsBaseline {
        let mut warnings = BTreeMap::new();
        warnings.insert(
            "000012".to_owned(),
            vec![
                WarningRow {
                    class: "eq-redundant".to_owned(),
                    line: 5,
                    col: 12,
                },
                WarningRow {
                    class: "unused-var".to_owned(),
                    line: 3,
                    col: 9,
                },
            ],
        );
        warnings.insert(
            "150887".to_owned(),
            vec![WarningRow {
                class: "closure-redundant".to_owned(),
                line: 1,
                col: 1,
            }],
        );
        WarningsBaseline {
            header: WarningsBaselineHeader {
                jar_sha256: "aa".repeat(32),
                generated: "2026-08-23".to_owned(),
                command: "resolve-gauge bake-warnings ...".to_owned(),
            },
            warnings,
        }
    }

    #[test]
    fn render_parse_round_trips() {
        let b = sample();
        let parsed = WarningsBaseline::parse(&b.render()).expect("parse");
        assert_eq!(parsed, b);
    }

    #[test]
    fn render_is_stable() {
        assert_eq!(sample().render(), sample().render());
        assert!(sample()
            .render()
            .contains("\n000012 eq-redundant@5:12 unused-var@3:9\n"));
    }

    #[test]
    fn missing_header_field_is_an_error() {
        let text = sample()
            .render()
            .lines()
            .filter(|l| !l.starts_with("# command"))
            .collect::<Vec<_>>()
            .join("\n");
        let e = WarningsBaseline::parse(&text).expect_err("missing field must fail");
        assert!(
            matches!(&e, ConformError::WarningsBaselineParse { detail } if detail.contains("command")),
            "{e:?}"
        );
    }

    #[test]
    fn malformed_row_is_an_error() {
        let mut text = sample().render();
        text.push_str("000099 not-a-valid-token\n");
        let e = WarningsBaseline::parse(&text).expect_err("malformed row must fail");
        assert!(
            matches!(&e, ConformError::WarningsBaselineParse { detail } if detail.contains("malformed warning token")),
            "{e:?}"
        );
    }
}
