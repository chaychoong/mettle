//! Front end for Alloy source: source spans, typed-index arena
//! infrastructure, the arena-based AST, the lexer, the parser (with its token
//! cooking pass), and the pretty-printer. Diagnostics arrive next (mt-013).
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
// The shared binding-power table is an internal contract between parser and
// printer, not API surface (STYLE S4).
pub(crate) mod prec;
pub mod print;
pub mod span;
pub mod token;

pub use arena::{Arena, ArenaId};
pub use ast::Ast;
pub use cook::cook;
pub use lexer::{lex, LexError};
pub use parser::{parse, ParseError};
pub use print::{dump, Pretty};
pub use span::{FileId, Span};
pub use token::{Token, TokenKind};
