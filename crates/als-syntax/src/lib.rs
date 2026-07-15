//! Front end for Alloy source: source spans, typed-index arena
//! infrastructure, the arena-based AST, and the lexer. Parser,
//! pretty-printer, and diagnostics arrive next (beads mt-011..mt-014).
//!
//! This crate is also the shared dependency root (STYLE S3): [`Arena`],
//! [`ArenaId`], [`define_id!`], and [`Span`] defined here are reused by every
//! downstream IR.

#![deny(clippy::unwrap_used, clippy::expect_used)]

pub mod arena;
pub mod ast;
pub mod cook;
pub mod lexer;
pub mod parser;
pub mod span;
pub mod token;

pub use arena::{Arena, ArenaId};
pub use ast::Ast;
pub use cook::cook;
pub use lexer::{lex, LexError};
pub use parser::{parse, ParseError};
pub use span::{FileId, Span};
pub use token::{Token, TokenKind};
