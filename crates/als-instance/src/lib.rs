//! Instance-surface machinery: the Alloy **instance-XML** writer (mt-071) — the
//! file format `mettle exec --xml` exports and `mettle serve` (mt-072) will
//! hand Sterling-protocol clients.
//!
//! The writer is a jar-shape-exact port of `A4Solution.writeXML`, specified by
//! `docs/reference/alloy6-instance-xml.md` — see [`xml`].

#![deny(clippy::unwrap_used, clippy::expect_used)]

pub mod xml;

pub use xml::{write_instance_xml, XmlRequest, XmlSolution};
