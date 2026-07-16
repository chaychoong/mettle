//! The module graph: the owned DAG of loaded module instances that the
//! resolver (mt-018) resolves names against.
//!
//! This layer reproduces resolution-doc §0–§2:
//! - **Recursive load** (§0/§2.1): parse the root, walk `open`s transitively
//!   in the exact file-search order, parse each file once.
//! - **Cycle detection** (§2.2): a file appearing twice on the current
//!   open-chain is a load-time reject.
//! - **Parametric instantiation** (§2.3): positional argument binding with
//!   single-hop parameter substitution (the reference's `resolveParams`
//!   fixpoint, done in dependency order so one pass suffices — semantics
//!   faithful, structure idiomatic, STYLE M1), and **instance identity =
//!   (file, resolved args)** so `[A]`/`[A]` merge and `[A]`/`[B]` stay
//!   distinct (probes 24/25).
//! - **Aliasing** (§2.4): explicit `as`, the no-arg plain-filename auto-alias,
//!   the `open$N` placeholder + basename rewrite, and the duplicate-alias
//!   reject (probe 26).
//! - **Private-open visibility** (§2.5): edges carry the `private` flag and the
//!   qualified-lookup walk ([`ModuleGraph::walk_prefix`]) blocks a private hop
//!   across modules — the building block mt-018's name resolution calls.
//!
//! Sig *references* (open arguments, parameter targets) are carried as names
//! here; mt-018 turns them into `SigId`s. No expression resolution happens in
//! this bead.

use als_syntax::{define_id, Arena, FileId, Span};

use crate::error::ResolveError;
use crate::file::FileTable;
use crate::loader::ModuleLoader;
use crate::path::normalize;

define_id! {
    /// Index into [`ModuleGraph::modules`]: one *instance* of a file
    /// instantiated with one argument tuple.
    pub struct ModuleId;
}

/// A (possibly qualified) sig reference used as an `open` argument, after
/// parameter substitution. mt-018 resolves this to a `SigId`; here it is the
/// name segments plus the span it was written at.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ArgRef {
    /// Reference path segments (`["A"]`, `["m", "Elem"]`).
    pub segments: Vec<String>,
    /// Where the argument was written.
    pub span: Span,
}

impl ArgRef {
    /// The `/`-joined textual form, the key for instance identity.
    #[must_use]
    pub fn joined(&self) -> String {
        self.segments.join("/")
    }
}

/// One of a module's declared parameters bound to a resolved argument
/// (resolution-doc §2.3).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ParamBinding {
    /// Parameter name, from the opened module's `module` header.
    pub param: String,
    /// `exactly` marker on the parameter.
    pub is_exact: bool,
    /// The resolved argument bound to it.
    pub arg: ArgRef,
}

/// One `open` edge out of a module instance.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct OpenEdge {
    /// The alias this module reaches the target by (resolution-doc §2.4).
    pub alias: String,
    /// The instantiated target module.
    pub target: ModuleId,
    /// Resolved instantiation arguments, in order.
    pub args: Vec<ArgRef>,
    /// `private open` — hidden from qualified lookups by other modules.
    pub is_private: bool,
    /// Span of the `open` directive.
    pub span: Span,
}

/// One loaded module instance: a file plus the argument tuple it was
/// instantiated with. Distinct argument tuples over one file are distinct
/// instances (distinct [`ModuleId`]s) sharing one [`FileId`].
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ModuleInstance {
    /// The file this instance parses.
    pub file: FileId,
    /// Declared module-name segments: the `module` header's name if present,
    /// else the path this module was opened by (empty for a header-less root).
    /// This is what `computeModulePath` measures the namespace-root depth by.
    pub module_name: Vec<String>,
    /// Positional parameter bindings (empty for a non-parametric module).
    pub params: Vec<ParamBinding>,
    /// `open` edges in source order.
    pub opens: Vec<OpenEdge>,
}

/// The loaded module world: the file table, the instance arena, the root, and
/// the meta-phase `seenDollar` gate (resolution-doc §1 phase 8).
#[derive(Debug)]
pub struct ModuleGraph {
    /// Every parsed file, `FileId`-keyed.
    pub files: FileTable,
    /// Every module instance, `ModuleId`-keyed, in creation order.
    pub modules: Arena<ModuleId, ModuleInstance>,
    /// The root module (the file handed to [`ModuleGraph::load`]).
    pub root: ModuleId,
    /// Whether any name in **any loaded file** contained `$` — gates mt-018's
    /// meta-sig synthesis (the reference accumulates this across every parsed
    /// file). Declared `$` names are already a parse-time reject, so only
    /// `sig$`/`field$` uses remain.
    pub seen_dollar: bool,
}

impl ModuleGraph {
    /// Loads the module graph rooted at `root_path`, reading the root and every
    /// transitively-opened file through `loader`.
    ///
    /// # Errors
    /// Any [`ResolveError`] from the module phase (missing file, circular
    /// import, duplicate alias, bad instantiation) or a parse failure in an
    /// opened file.
    pub fn load<L: ModuleLoader>(root_path: &str, loader: &L) -> Result<Self, ResolveError> {
        let path = normalize(root_path);
        let source = loader
            .load(&path)
            .ok_or_else(|| ResolveError::ModuleFileNotFound {
                target: root_path.to_owned(),
                span: crate::load::synthetic_span(),
            })?;
        Self::load_with_source(&path, source, loader)
    }

    /// Loads the module graph from an already-read root `source`, using
    /// `loader` for transitively-opened files. Useful when the caller already
    /// holds the root text (the CLI reads it for parse diagnostics first).
    ///
    /// # Errors
    /// As [`ModuleGraph::load`], plus a root parse failure.
    pub fn load_with_source<L: ModuleLoader>(
        root_path: &str,
        source: String,
        loader: &L,
    ) -> Result<Self, ResolveError> {
        crate::load::run(root_path, source, loader)
    }

    /// Follows one `open` alias out of `module`, respecting private-open
    /// blocking: a `private` open is invisible to a *different* querying
    /// module (resolution-doc §2.5). Returns the target instance, or `None`
    /// when no such alias is reachable.
    #[must_use]
    pub fn follow_alias(
        &self,
        module: ModuleId,
        alias: &str,
        querying: ModuleId,
    ) -> Option<ModuleId> {
        for edge in &self.modules[module].opens {
            if edge.alias == alias {
                if edge.is_private && querying != module {
                    return None;
                }
                return Some(edge.target);
            }
        }
        None
    }

    /// Walks a qualified prefix `segments` from `start`, hopping module aliases
    /// as far as they match, and returns `(landing_module, consumed)` — the
    /// module the prefix bottoms out in and how many leading segments were
    /// consumed as aliases. mt-018 looks the remaining `segments[consumed..]`
    /// up (sig/func/assert) inside `landing_module`. Private hops are blocked
    /// for a foreign `querying` module (resolution-doc §2.4/§2.5).
    #[must_use]
    pub fn walk_prefix(
        &self,
        start: ModuleId,
        segments: &[&str],
        querying: ModuleId,
    ) -> (ModuleId, usize) {
        let mut current = start;
        let mut consumed = 0;
        while consumed < segments.len() {
            match self.follow_alias(current, segments[consumed], querying) {
                Some(next) => {
                    current = next;
                    consumed += 1;
                }
                None => break,
            }
        }
        (current, consumed)
    }
}
