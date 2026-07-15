//! Front end for Alloy source: source spans, typed-index arena
//! infrastructure, and the arena-based AST. Lexer, parser, pretty-printer,
//! and diagnostics arrive with Rung 1 (beads mt-010..mt-014).
//!
//! This crate is also the shared dependency root (STYLE S3): [`Arena`],
//! [`ArenaId`], [`define_id!`], and [`Span`] defined here are reused by every
//! downstream IR.

#![deny(clippy::unwrap_used, clippy::expect_used)]

pub mod arena;
pub mod ast;
pub mod span;

pub use arena::{Arena, ArenaId};
pub use span::{FileId, Span};
