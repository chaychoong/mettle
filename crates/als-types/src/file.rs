//! The file world: a `FileId`-keyed arena of loaded, parsed source files.
//!
//! `als-syntax::parse` takes a [`FileId`]; those ids are minted **here**, at
//! load time, so spans in every parsed `Ast` point back into the right source
//! (STYLE G1/G2). Each physical file is parsed **once** and cached by its
//! normalized path — parametric `open`s reuse the same parse (a distinct
//! *module instance* over the same [`FileId`], see [`crate::graph`]).

use std::collections::BTreeMap;

use als_syntax::ast::Ast;
use als_syntax::{parse, Arena, ArenaId, FileId, ParseError, Span};

use crate::path::normalize;

/// One loaded, parsed source file.
#[derive(Debug)]
pub struct LoadedFile {
    /// Normalized forward-slash path this file was loaded from.
    pub path: String,
    /// The raw source text (owned; caret rendering reads it later).
    pub source: String,
    /// The parsed AST for this file.
    pub ast: Ast,
}

impl LoadedFile {
    /// Borrows the parsed AST (an ergonomic alias for the `ast` field that
    /// keeps borrow sites in the loader terse).
    #[must_use]
    pub fn ast_ref(&self) -> &Ast {
        &self.ast
    }
}

/// A `FileId`-keyed arena of loaded files, with a path→id index for
/// parse-once caching. The index is membership/lookup only — its iteration
/// order never escapes — so a `BTreeMap` satisfies determinism (STYLE D3).
#[derive(Debug, Default)]
pub struct FileTable {
    files: Arena<FileId, LoadedFile>,
    by_path: BTreeMap<String, FileId>,
}

impl FileTable {
    /// Creates an empty file table.
    #[must_use]
    pub fn new() -> Self {
        Self {
            files: Arena::new(),
            by_path: BTreeMap::new(),
        }
    }

    /// The `FileId` already loaded for `path` (normalized), if any.
    #[must_use]
    pub fn get(&self, path: &str) -> Option<FileId> {
        self.by_path.get(&normalize(path)).copied()
    }

    /// Looks up a loaded file by id.
    #[must_use]
    pub fn file(&self, id: FileId) -> &LoadedFile {
        &self.files[id]
    }

    /// Number of distinct files loaded.
    #[must_use]
    pub fn len(&self) -> usize {
        self.files.len()
    }

    /// Whether nothing has been loaded.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.files.is_empty()
    }

    /// Iterates `(FileId, &LoadedFile)` in load order.
    pub fn iter(&self) -> impl Iterator<Item = (FileId, &LoadedFile)> {
        self.files.iter()
    }

    /// Interns and parses `source` at `path`, returning the (possibly cached)
    /// `FileId`. A file is parsed exactly once; a second call for the same
    /// normalized path returns the existing id and ignores `source`.
    ///
    /// `open_span` is the directive that pulled this file in, used to attribute
    /// a parse failure (the root passes its own header span or a synthetic one).
    ///
    /// # Errors
    /// Returns the underlying [`ParseError`] if the freshly-read source does
    /// not parse.
    pub fn intern(
        &mut self,
        path: &str,
        source: String,
        open_span: Span,
    ) -> Result<FileId, (ParseError, Span)> {
        let path = normalize(path);
        if let Some(existing) = self.by_path.get(&path) {
            return Ok(*existing);
        }
        // Mint the id first so parse spans carry the correct file (the id is
        // `len()` before allocation — allocation is deterministic, STYLE A2).
        let file_id = FileId::from_index(self.files.len());
        let ast = parse(&source, file_id).map_err(|err| (err, open_span))?;
        let id = self.files.alloc(LoadedFile {
            path: path.clone(),
            source,
            ast,
        });
        debug_assert_eq!(id, file_id, "file-id allocation drifted from prediction");
        self.by_path.insert(path, id);
        Ok(id)
    }
}
