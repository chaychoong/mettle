//! Name resolution, sig hierarchy, and the relevance/type checker (Rung 2).
//!
//! This crate turns the Rung-1 `Ast` (`als-syntax`) into a resolved,
//! type-checked world, reproducing the reference `CompModule.resolveAll`
//! accept/reject verdict (ADR-0008, pinned in
//! `docs/reference/alloy6-resolution.md`).
//!
//! **mt-017 — the module graph / `open` layer (this bead).** The foundation
//! the resolver sits on: a [`FileTable`] of parsed files, a [`ModuleGraph`] of
//! instantiated modules with the exact file-search order ([`ModuleLoader`] +
//! [`path::compute_module_path`]), cycle detection, parametric instantiation
//! with instance identity `(file, args)`, alias machinery, private-open
//! visibility, and the module-phase [`ResolveError`] variants. Name/type
//! resolution over this graph is mt-018.

#![deny(clippy::unwrap_used, clippy::expect_used)]

pub mod error;
pub mod file;
pub mod graph;
mod load;
pub mod loader;
pub mod path;
pub mod stdlib;

pub use error::ResolveError;
pub use file::{FileTable, LoadedFile};
pub use graph::{ArgRef, ModuleGraph, ModuleId, ModuleInstance, OpenEdge, ParamBinding};
pub use loader::{FilesystemLoader, MapLoader, ModuleLoader};
