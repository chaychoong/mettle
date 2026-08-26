//! The recursive load algorithm behind [`crate::graph::ModuleGraph`]: the file
//! search order, cycle detection, parametric instantiation, and alias
//! computation (resolution-doc §0–§2). The *shapes* it produces live in
//! [`crate::graph`]; this module is the machine that fills them.

use std::collections::{BTreeMap, BTreeSet};

use als_syntax::ast::{Ast, ExprKind, Open, QualName};
use als_syntax::{Arena, ArenaId, FileId, Span};

use crate::error::ResolveError;
use crate::file::FileTable;
use crate::graph::{ArgRef, ModuleGraph, ModuleId, ModuleInstance, OpenEdge, ParamBinding};
use crate::loader::ModuleLoader;
use crate::path::{compute_module_path, is_plain_identifier, markdown_sibling, normalize};
use crate::stdlib;

/// Builds the whole module graph from an already-read root `source`: interns
/// the root, walks its opens transitively, and computes the meta-phase
/// `seenDollar` gate.
///
/// # Errors
/// Any module-phase [`ResolveError`] or a parse failure (root or opened file).
pub(crate) fn run<L: ModuleLoader>(
    root_path: &str,
    source: String,
    loader: &L,
) -> Result<ModuleGraph, ResolveError> {
    let mut builder = Builder {
        loader,
        files: FileTable::new(),
        modules: Arena::new(),
        instances: BTreeMap::new(),
    };

    let path = normalize(root_path);
    let root_file = builder
        .files
        .intern(&path, source, synthetic_span())
        .map_err(|(err, span)| ResolveError::OpenedFileParse {
            path: path.clone(),
            span,
            source: err,
        })?;
    let module_name = module_name_of(builder.files.file(root_file).ast_ref(), None);
    let root = builder.modules.alloc(ModuleInstance {
        file: root_file,
        module_name,
        params: Vec::new(),
        opens: Vec::new(),
    });
    builder.instances.insert((root_file, Vec::new()), root);

    let mut chain = vec![root_file];
    builder.process_opens(root, &mut chain)?;

    // The reference threads its `seenDollar` accumulator through EVERY parsed
    // file (root and transitively-opened alike), so the scan covers them all.
    let mut dollars = BTreeSet::new();
    for (_, file) in builder.files.iter() {
        collect_dollar_segments(file.ast_ref(), &mut dollars);
    }
    Ok(ModuleGraph {
        files: builder.files,
        modules: builder.modules,
        root,
        dollar_names: dollars.into_iter().collect(),
    })
}

/// The synthetic span used where the module phase has no source location (the
/// root's own directive). Points at the root file, byte range 0..0.
pub(crate) fn synthetic_span() -> Span {
    Span::new(FileId::from_index(0), 0, 0)
}

/// Mutable state threaded through the recursive load.
struct Builder<'a, L: ModuleLoader> {
    loader: &'a L,
    files: FileTable,
    modules: Arena<ModuleId, ModuleInstance>,
    /// Instance dedup / merge (resolution-doc §2.3): `(file, arg-strings)` →
    /// instance. Membership/lookup only, so a `BTreeMap` is deterministic
    /// (STYLE D3).
    instances: BTreeMap<(FileId, Vec<String>), ModuleId>,
}

/// The outcome of resolving one `open` target's file through the search order.
struct Resolved {
    /// Normalized path (or synthetic `<stdlib>/…` path) of the target file.
    path: String,
    /// Fresh source to intern, or `None` when the file is already loaded.
    fresh: Option<String>,
}

impl<L: ModuleLoader> Builder<'_, L> {
    /// Walks a module instance's `open`s: instantiates each target (recursing),
    /// then computes aliases and stores the edges back onto the instance.
    fn process_opens(
        &mut self,
        module: ModuleId,
        chain: &mut Vec<FileId>,
    ) -> Result<(), ResolveError> {
        let file = self.modules[module].file;
        // Clone the data we need up front: the recursion mutates `self.modules`
        // (allocating child instances), so we cannot hold a borrow across it.
        // Synthetic opens (enum → `util/ordering`, `seq` field → `util/sequniv`)
        // are appended: the reference synthesizes these during parse (addEnum /
        // addSeq), so mettle materializes them here where the graph is built, so
        // the stdlib funcs resolve through the normal search order (§3.2/§4.5).
        let mut opens = self.files.file(file).ast_ref().opens.clone();
        let user_opens_len = opens.len();
        let (synthetic, synthetic_integer_idx) = synthetic_opens(self.files.file(file).ast_ref());
        let synthetic_integer_idx = synthetic_integer_idx.map(|i| user_opens_len + i);
        opens.extend(synthetic);
        let parent_name = self.modules[module].module_name.clone();
        let parent_path = self.files.file(file).path.clone();
        let parent_params = self.modules[module].params.clone();

        // Phase 1: resolve each open to a target instance (recursing).
        let mut targets: Vec<ModuleId> = Vec::with_capacity(opens.len());
        for open in &opens {
            let target =
                self.instantiate(open, &parent_name, &parent_path, &parent_params, chain)?;
            targets.push(target);
        }

        // Phase 2 + 3: aliases, then dedup / duplicate-alias reject.
        let aliases = compute_aliases(&opens, synthetic_integer_idx);
        let edges = build_edges(&opens, &targets, &aliases, &parent_params)?;
        self.modules[module].opens = edges;
        Ok(())
    }

    /// Resolves and instantiates one `open` target: search order → file →
    /// cycle check → argument binding → instance create-or-reuse (+ recurse).
    fn instantiate(
        &mut self,
        open: &Open,
        parent_name: &[String],
        parent_path: &str,
        parent_params: &[ParamBinding],
        chain: &mut Vec<FileId>,
    ) -> Result<ModuleId, ResolveError> {
        let target_str = join_segments(&open.module);

        // Bind arguments in the opener's parameter scope (single-hop
        // substitution; `none` and unresolved-name rejects live here).
        let mut args = Vec::with_capacity(open.args.len());
        for arg in &open.args {
            args.push(substitute_arg(arg, parent_params)?);
        }
        let arg_keys: Vec<String> = args.iter().map(ArgRef::joined).collect();

        // Search order (resolution-doc §2.1) → resolved path + maybe source.
        let resolved = self
            .search(parent_name, parent_path, &target_str)
            .ok_or_else(|| ResolveError::ModuleFileNotFound {
                target: target_str.clone(),
                span: open.span,
            })?;

        let target_file = match resolved.fresh {
            Some(src) => {
                self.files
                    .intern(&resolved.path, src, open.span)
                    .map_err(|(err, span)| ResolveError::OpenedFileParse {
                        path: resolved.path.clone(),
                        span,
                        source: err,
                    })?
            }
            None => self
                .files
                .get(&resolved.path)
                .unwrap_or_else(|| unreachable!("search reported a cached file that is absent")),
        };

        // Cycle: the target file already sits on the current open-chain
        // (resolution-doc §2.2). Checked before reuse so a cyclic re-open of an
        // ancestor still rejects.
        if chain.contains(&target_file) {
            return Err(ResolveError::CircularImport {
                path: resolved.path,
                span: open.span,
            });
        }

        // Instance identity = (file, resolved args). Reuse merges instances.
        let key = (target_file, arg_keys);
        if let Some(existing) = self.instances.get(&key) {
            return Ok(*existing);
        }

        // Fresh instance: bind params, create, recurse.
        let ast = self.files.file(target_file).ast_ref();
        let params = bind_params(ast, &open.args, &args, open.span)?;
        let module_name = module_name_of(ast, Some(&open.module));
        let id = self.modules.alloc(ModuleInstance {
            file: target_file,
            module_name,
            params,
            opens: Vec::new(),
        });
        self.instances.insert(key, id);

        chain.push(target_file);
        self.process_opens(id, chain)?;
        chain.pop();
        Ok(id)
    }

    /// The resolution-doc §2.1 file-search order. Returns the resolved path and
    /// whether fresh source must be interned, or `None` if every step misses.
    fn search(&self, parent_name: &[String], parent_path: &str, target: &str) -> Option<Resolved> {
        // Step 1: parent-relative computed path.
        let cp = compute_module_path(parent_name, parent_path, target);
        if self.files.get(&cp).is_some() {
            return Some(Resolved {
                path: cp,
                fresh: None,
            });
        }
        // Step 2: target verbatim, already loaded in memory.
        let verbatim = normalize(&format!("{target}.als"));
        if self.files.get(&verbatim).is_some() {
            return Some(Resolved {
                path: verbatim,
                fresh: None,
            });
        }
        // Step 3: computed path on disk.
        if let Some(src) = self.loader.load(&cp) {
            return Some(Resolved {
                path: cp,
                fresh: Some(src),
            });
        }
        // Step 4: computed path with `.als` → `.md`.
        if let Some(md) = markdown_sibling(&cp) {
            if let Some(src) = self.loader.load(&md) {
                return Some(Resolved {
                    path: md,
                    fresh: Some(src),
                });
            }
        }
        // Step 5: embedded stdlib fallback (empty until mt-015), on a stable
        // synthetic path so cycle/dedup keys stay well-formed.
        if let Some(src) = stdlib::source_for(target) {
            let vpath = normalize(&format!("<stdlib>/{target}.als"));
            if self.files.get(&vpath).is_some() {
                return Some(Resolved {
                    path: vpath,
                    fresh: None,
                });
            }
            return Some(Resolved {
                path: vpath,
                fresh: Some(src.to_owned()),
            });
        }
        None
    }
}

/// Applies aliases and the duplicate-alias reject to build the final edge
/// list. Identical re-opens (same alias, same instance) are silently
/// deduped; a same-alias/different-instance clash rejects (probe 26).
fn build_edges(
    opens: &[Open],
    targets: &[ModuleId],
    aliases: &[String],
    parent_params: &[ParamBinding],
) -> Result<Vec<OpenEdge>, ResolveError> {
    let mut edges = Vec::new();
    let mut by_alias: BTreeMap<String, (ModuleId, Span)> = BTreeMap::new();
    for ((open, &target), alias) in opens.iter().zip(targets).zip(aliases) {
        if let Some((existing, first_span)) = by_alias.get(alias) {
            if *existing != target {
                return Err(ResolveError::DuplicateAlias {
                    alias: alias.clone(),
                    span: open.span,
                    first_span: *first_span,
                });
            }
            continue; // identical re-open: silently allowed
        }
        by_alias.insert(alias.clone(), (target, open.span));
        let args = open
            .args
            .iter()
            .map(|a| substitute_arg(a, parent_params))
            .collect::<Result<Vec<_>, _>>()?;
        edges.push(OpenEdge {
            alias: alias.clone(),
            target,
            args,
            is_private: open.is_private,
            span: open.span,
        });
    }
    Ok(edges)
}

/// Computes each `open`'s alias (resolution-doc §2.4): explicit `as`, the
/// no-arg plain-filename auto-alias, else the `open$N` placeholder rewritten to
/// the target basename when that basename is a free legal identifier.
///
/// `synthetic_integer_idx` is the index within `opens` of the synthetic
/// `util/integer` auto-open (from `synthetic_opens`), or `None` for the
/// `util/integer` module itself. See the `open$N` counter comment below for
/// why it needs special handling here.
fn compute_aliases(opens: &[Open], synthetic_integer_idx: Option<usize>) -> Vec<String> {
    let mut aliases: Vec<Option<String>> = vec![None; opens.len()];

    // Pass 1: fixed aliases (explicit `as` and the plain-filename auto-alias).
    // The synthetic `util/integer` open is given an explicit `as` by
    // `synthetic_opens` (mirroring `util/sequniv as seq`), so it already
    // resolves here like any other aliased open — no special case needed in
    // this pass.
    for (i, open) in opens.iter().enumerate() {
        let path = join_segments(&open.module);
        if let Some(name) = &open.alias {
            aliases[i] = Some(name.text.clone());
        } else if open.args.is_empty() && is_plain_identifier(&path) {
            aliases[i] = Some(path);
        }
    }

    // Pass 2: placeholders → basename if the basename is free, else `open$N`.
    //
    // `CompModule.addOpen` (CompModule.java:1325) computes `"open$" + (1 +
    // opens.size())` at the point each open is inserted into the module's
    // own per-instance `opens` map, so the k-th (1-based) open placed there
    // gets `open$(k+1)`. `opens.size()` starts at 1, not 0:
    // `CompParser.alloy_parseStream` (decompiled from the pinned jar; ~line
    // 2662-2663 per its own embedded LineNumberTable) auto-opens
    // `util/integer` into every module except itself, with the fixed alias
    // `"integer"`, *before* the file's own tokens are parsed — so it always
    // occupies counter slot 1, ahead of every user- and enum-triggered open,
    // regardless of where in `ast.opens`/`synthetic_opens`'s *array* mettle
    // happens to place its own synthesized copy of that open (mt-133
    // einstein gate: `synthetic_opens` puts `util/integer` before the
    // enum-derived opens but after the file's own explicit opens, which
    // does not match the jar's "always first" placement whenever both an
    // explicit open and an enum are present — using the raw array index
    // there mis-numbered every enum-derived open by one). `counter` below
    // is therefore the 1-based position of this open among opens *other
    // than* the synthetic `util/integer` one, in array order (which does
    // match the jar's true source order for every other open, since a
    // module's own `open` declarations must all precede any paragraph,
    // enum declarations included) — `open$(counter + 1)` is the jar's
    // `open$(k+1)` for that k. Live-probe-confirmed (mt-133) — see
    // scratchpad/probe/mt133/NOTES.md.
    let mut used: BTreeSet<String> = aliases.iter().flatten().cloned().collect();
    let mut counter = 0usize;
    for (i, open) in opens.iter().enumerate() {
        if Some(i) == synthetic_integer_idx {
            continue;
        }
        counter += 1;
        if aliases[i].is_some() {
            continue;
        }
        let basename = open
            .module
            .segments
            .last()
            .map(|s| s.text.clone())
            .unwrap_or_default();
        if is_plain_identifier(&basename) && !used.contains(&basename) {
            used.insert(basename.clone());
            aliases[i] = Some(basename);
        } else {
            aliases[i] = Some(format!("open${}", counter + 1));
        }
    }

    aliases.into_iter().map(Option::unwrap_or_default).collect()
}

/// Binds an opened module's declared parameters to the supplied arguments
/// (resolution-doc §2.3): positional, with the arg-count reject.
fn bind_params(
    ast: &Ast,
    raw_args: &[QualName],
    resolved_args: &[ArgRef],
    span: Span,
) -> Result<Vec<ParamBinding>, ResolveError> {
    let decl = ast.header.as_ref().map_or(&[][..], |h| h.params.as_slice());
    if decl.len() != raw_args.len() {
        return Err(ResolveError::OpenArgCount {
            expected: decl.len(),
            found: raw_args.len(),
            span,
        });
    }
    Ok(decl
        .iter()
        .zip(resolved_args)
        .map(|(param, arg)| ParamBinding {
            param: join_segments(&param.name),
            is_exact: param.is_exact,
            arg: arg.clone(),
        })
        .collect())
}

/// Resolves one `open` argument in the opener's parameter scope: a bare name
/// matching an opener parameter is replaced by that parameter's (already
/// concrete) binding; `none` rejects; everything else is a concrete sig name
/// whose existence mt-018 checks (resolution-doc §2.3).
fn substitute_arg(arg: &QualName, parent_params: &[ParamBinding]) -> Result<ArgRef, ResolveError> {
    let segments: Vec<String> = arg.segments.iter().map(|i| i.text.clone()).collect();
    if segments.len() == 1 && segments[0] == "none" {
        return Err(ResolveError::NoneAsOpenArg { span: arg.span });
    }
    if segments.len() == 1 {
        if let Some(binding) = parent_params.iter().find(|p| p.param == segments[0]) {
            // The opener's binding is already concrete (bound in dependency
            // order), so one substitution grounds it — no fixpoint needed.
            return Ok(ArgRef {
                segments: binding.arg.segments.clone(),
                span: arg.span,
            });
        }
    }
    Ok(ArgRef {
        segments,
        span: arg.span,
    })
}

/// A module's declared name for `computeModulePath`: the header name if
/// present, else the path it was opened by (empty for a header-less root).
fn module_name_of(ast: &Ast, opened_as: Option<&QualName>) -> Vec<String> {
    if let Some(header) = &ast.header {
        header
            .name
            .segments
            .iter()
            .map(|s| s.text.clone())
            .collect()
    } else {
        opened_as
            .map(|q| q.segments.iter().map(|s| s.text.clone()).collect())
            .unwrap_or_default()
    }
}

/// Whether any name reference in one file's AST contains `$` (the meta-phase
/// gate, resolution-doc §1 phase 8, checked across every loaded file). A cheap
/// over-scan of `Name`/`AtName` leaves; mt-018 consumes
/// `ModuleGraph::dollar_names` to decide meta-sig synthesis.
///
/// Collects the `$`-bearing segments themselves, not just a flag: the gate can
/// only be decided once sigs exist, because `Vertex$` and `$Professor` are
/// indistinguishable at load time (mt-108).
fn collect_dollar_segments(ast: &Ast, out: &mut BTreeSet<String>) {
    // A leaf-name scan over the flat expression arena, not a node-dispatch
    // site: only `Name`/`AtName` carry names, so an `if let` over those two
    // (rather than an exhaustive `match`) is the right shape — there is no
    // per-variant behavior a new `ExprKind` would need to opt into here
    // (PORTING R1 targets dispatch `match`es, not membership predicates).
    for (_, expr) in ast.exprs.iter() {
        if let ExprKind::Name(q) | ExprKind::AtName(q) = &expr.kind {
            for seg in &q.segments {
                if seg.text.contains('$') {
                    out.insert(seg.text.clone());
                }
            }
        }
    }
}

/// The opens the reference synthesizes at parse time but which never appear in
/// the AST's `open` list (resolution-doc §3.2, §4.5):
/// - `util/integer`, auto-opened into every module (see below);
/// - each `enum N {…}` → `open util/ordering[N]` (auto-aliased `ordering`);
/// - any use of the `seq` field keyword → `open util/sequniv as seq`.
///
/// Materializing them here (rather than in the parser) keeps mt-011's AST a
/// faithful mirror of source and confines the desugaring to the graph layer
/// that owns module instantiation.
///
/// Returns the synthesized opens plus the index, within the returned `Vec`,
/// of the `util/integer` auto-open (`None` when this file *is*
/// `util/integer`, so nothing was synthesized for it) — mt-133 needs this so
/// `compute_aliases` can special-case its counter slot (see the comment at
/// its push site below).
fn synthetic_opens(ast: &Ast) -> (Vec<Open>, Option<usize>) {
    use als_syntax::ast::{Ident, Para};

    let mut out = Vec::new();

    // Alloy auto-opens `util/integer` into every module, so its arithmetic
    // funcs (`plus`, `add`, `gte`, …) are globally available without an explicit
    // `open` (jar-verified 2026-07-16: a model using `plus`/`add` with no open
    // resolves). Skip `util/integer` itself to avoid a self-cycle.
    //
    // Mechanism, pinned by mt-133 (scratchpad/probe/mt133/NOTES.md):
    // `CompParser.alloy_parseStream` calls this module's own `addOpen` with
    // the fixed alias `"integer"` before parsing the file's own tokens — an
    // ordinary `addOpen` call, just with an explicit alias, exactly like the
    // `util/sequniv as seq` open below. So this entry always keeps `integer`
    // in the jar (it never enters the `open$N` placeholder/rescue
    // competition at all) and always occupies the *first* counter slot,
    // before any user- or enum-triggered open. Giving it `alias:
    // Some("integer")` here (rather than `None`) mirrors that exactly: it
    // resolves through `compute_aliases`'s existing explicit-alias branch,
    // so a module that also writes an explicit, unaliased `open
    // util/integer` can never win the `integer` name away from it (their
    // keys differ, matching the jar's non-dedup). `compute_aliases` also
    // excludes this specific entry from the counter it uses to number
    // `open$N` placeholders for every *other* open, since — unlike this
    // entry — those others sit at whatever array position `ast.opens` plus
    // the enum loop below puts them at, which does not always match the
    // jar's "`util/integer` is always first" placement (mt-133 einstein
    // gate: 5 enum-derived opens after this one in the array need numbers
    // as if `util/integer` were still first).
    let self_name = ast
        .header
        .as_ref()
        .map(|h| join_segments(&h.name))
        .unwrap_or_default();
    let synthetic_integer_idx = if self_name == "util/integer" {
        None
    } else {
        let span = synthetic_span();
        out.push(Open {
            module: qual(&["util", "integer"], span),
            args: Vec::new(),
            alias: Some(Ident {
                text: "integer".to_owned(),
                span,
            }),
            is_private: false,
            span,
        });
        Some(0)
    };
    for &para_id in &ast.paragraphs {
        if let Para::Enum(e) = &ast.paras[para_id] {
            // `open util/ordering[N]` — target and arg are synthetic names
            // pointing at the enum's own span (diagnostics never surface here).
            out.push(Open {
                module: qual(&["util", "ordering"], e.name.span),
                args: vec![qual(&[e.name.text.as_str()], e.name.span)],
                alias: None,
                is_private: false,
                span: e.span,
            });
        }
    }

    if uses_seq_keyword(ast) {
        // A single `open util/sequniv as seq`; identical re-adds would dedup,
        // but one suffices (the reference's addSeq keys on file+args+alias).
        let span = synthetic_span();
        out.push(Open {
            module: qual(&["util", "sequniv"], span),
            args: Vec::new(),
            alias: Some(Ident {
                text: "seq".to_owned(),
                span,
            }),
            is_private: false,
            span,
        });
    }
    (out, synthetic_integer_idx)
}

/// Builds a [`QualName`] from string segments at a single span.
fn qual(segments: &[&str], span: Span) -> QualName {
    use als_syntax::ast::Ident;
    QualName {
        segments: segments
            .iter()
            .map(|s| Ident {
                text: (*s).to_owned(),
                span,
            })
            .collect(),
        span,
    }
}

/// Whether the `seq` field/param multiplicity keyword (`UnOp::SeqOf`) is used
/// anywhere in the file — the trigger for the `util/sequniv` synthetic open.
fn uses_seq_keyword(ast: &Ast) -> bool {
    use als_syntax::ast::UnOp;
    ast.exprs.iter().any(|(_, e)| {
        matches!(
            &e.kind,
            ExprKind::Unary {
                op: UnOp::SeqOf,
                ..
            }
        )
    })
}

/// Joins a qualified name's segments with `/`.
fn join_segments(name: &QualName) -> String {
    name.segments
        .iter()
        .map(|s| s.text.as_str())
        .collect::<Vec<_>>()
        .join("/")
}
