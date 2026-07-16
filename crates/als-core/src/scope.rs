//! Scopes → universe: the first translation phase (mt-029, translation-ref §1).
//!
//! [`compute_universe`] is a faithful port of the reference's `ScopeComputer`
//! (behavior, not structure — PORTING prime directive): it turns a command's
//! `for … but …` scopes into a concrete integer scope for every signature and
//! the **ordered list of atom names** that *is* the [`Universe`]. It is the
//! source of the one canonical atom order every downstream bead numbers from
//! (STYLE D2), so it never iterates a hash map near that numbering: sigs are
//! walked in `SigId` (declaration) order, ints ascending.
//!
//! What it produces:
//! - the [`Universe`] — sig atoms `<QualifiedName>$<index>` in declaration
//!   order, then the integer atoms ascending (`-8 … 7` at bitwidth 4);
//! - a per-sig [`ScopeTable`] (scope value, exactness, and the atom range each
//!   sig minted) — the seam [`crate::bounds`]'s builder (mt-030) consumes;
//! - the resolved `bitwidth` / `maxseq`.
//!
//! What it defers (ADR-0011): **String atoms** are not minted here — full
//! String support (referenced-literal collection, `maxstring` synthetic fill)
//! is Rung 4; a `String` scope is still validated (`must be exact`). `steps` /
//! range / increment growth scopes are captured on the command but not expanded
//! (temporal, Rung 6). `util/ordering` exact forcing is mt-035 — the seam is
//! [`als_types::ResolvedCommand::additional_exact`], already honored here.

use std::collections::{BTreeMap, BTreeSet};

use als_syntax::ast::SigMult;
use als_syntax::ArenaId;
use als_types::{ResolvedCommand, ResolvedWorld, SigId, SigKind};

use crate::bounds::{AtomId, Universe};
use crate::error::TranslateError;

/// The default overall scope when a command gives no overall and no per-sig
/// scope (translation-ref §1.1).
const DEFAULT_OVERALL: u32 = 3;
/// The default integer bitwidth (Int atoms `-8 … 7`).
const DEFAULT_BITWIDTH: u32 = 4;
/// The reference's hard ceiling on bitwidth.
const MAX_BITWIDTH: u32 = 30;

/// The atoms one sig minted into the [`Universe`] — its own pool, a contiguous
/// run `[first, first + count)` in universe order. A sig that draws all its
/// atoms from a parent (an inexact non-top-level sig) or a subset sig mints
/// nothing (`count == 0`, absent from the table's `minted`).
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct MintedAtoms {
    /// The first atom of the run.
    pub first: AtomId,
    /// How many atoms the run holds.
    pub count: u32,
}

/// One signature's resolved scope (translation-ref §1.2), the unit
/// [`crate::bounds`]'s builder consumes.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct ScopedSig {
    /// The sig this entry describes.
    pub sig: SigId,
    /// Its resolved integer scope (the upper bound on `#sig`).
    pub scope: u32,
    /// Whether the scope is **exact** (`#sig = scope`): a user `exactly`, a
    /// non-`var` `one`, or a `util/ordering`-forced sig (mt-035).
    pub is_exact: bool,
    /// The atoms this sig minted, if any.
    pub minted: Option<MintedAtoms>,
}

/// The per-sig scope table: every non-builtin primitive sig's [`ScopedSig`],
/// keyed and iterated in `SigId` (declaration) order (deterministic, STYLE C2).
/// Subset sigs and builtins are absent — they mint no atoms of their own.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ScopeTable {
    sigs: BTreeMap<SigId, ScopedSig>,
}

impl ScopeTable {
    /// The scope entry for `sig`, if it has one.
    #[must_use]
    pub fn get(&self, sig: SigId) -> Option<&ScopedSig> {
        self.sigs.get(&sig)
    }

    /// Iterates entries in `SigId` (declaration) order.
    pub fn iter(&self) -> impl Iterator<Item = &ScopedSig> {
        self.sigs.values()
    }

    /// Number of scoped sigs.
    #[must_use]
    pub fn len(&self) -> usize {
        self.sigs.len()
    }

    /// Whether the table is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.sigs.is_empty()
    }
}

/// The universe plus the per-sig scope table and integer/sequence parameters —
/// the whole output of the scope phase, and [`crate::bounds`]'s input.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ScopedUniverse {
    /// The ordered atom universe (sig atoms, then integer atoms).
    pub universe: Universe,
    /// Per-sig scopes.
    pub scopes: ScopeTable,
    /// The integer bitwidth (Int atoms span `-2^(bw-1) … 2^(bw-1) - 1`).
    pub bitwidth: u32,
    /// The maximum sequence length / `seq/Int` domain size.
    pub maxseq: u32,
    /// How many leading universe atoms are sig atoms (the rest are the integer
    /// atoms). Lets the bounds builder (mt-030) find the integer-atom run
    /// without re-deriving it.
    pub sig_atom_count: usize,
}

impl ScopedUniverse {
    /// The half-open range of universe indices holding the integer atoms
    /// (ascending, immediately after the sig atoms).
    #[must_use]
    pub fn int_atom_range(&self) -> std::ops::Range<usize> {
        self.sig_atom_count..self.universe.len()
    }
}

/// Computes the atom universe and per-sig scope table for one command
/// (translation-ref §1). A faithful port of `ScopeComputer.compute`: seed
/// explicit scopes (validating them), force `one`/`lone`/`some` multiplicities,
/// run the abstract-sum → overall → parent fixpoint, then walk the sig
/// hierarchy in declaration order to mint the ordered atom names.
///
/// # Errors
/// A [`TranslateError`] for any illegal scope (scope on `univ`/`none`/an enum/a
/// subset sig, a non-exact `String` scope, a `one`/`lone`/`some` multiplicity
/// conflict, an unresolvable per-sig scope, or a bitwidth over 30).
pub fn compute_universe(
    world: &ResolvedWorld,
    command: &ResolvedCommand,
) -> Result<ScopedUniverse, TranslateError> {
    let mut solver = ScopeSolver::new(world, command);
    solver.seed_explicit()?;
    solver.force_multiplicities();
    solver.run_fixpoint()?;
    solver.finish()
}

/// The mutable working state of the scope fixpoint. `scope[i]`/`exact[i]` are
/// indexed by `SigId`; `children[i]` lists a sig's primitive children (built
/// once, in declaration order).
struct ScopeSolver<'a> {
    world: &'a ResolvedWorld,
    command: &'a ResolvedCommand,
    scope: Vec<Option<u32>>,
    exact: Vec<bool>,
    children: Vec<Vec<SigId>>,
    /// The overall scope actually in force: the explicit `for N`, or 3 when no
    /// overall *and* no per-sig scope was given; `None` means "per-sig scopes
    /// were given without an overall", so an unscoped top-level sig is an error.
    effective_overall: Option<u32>,
}

impl<'a> ScopeSolver<'a> {
    fn new(world: &'a ResolvedWorld, command: &'a ResolvedCommand) -> Self {
        let n = world.sigs.len();
        let mut children = vec![Vec::new(); n];
        for (id, sig) in world.sigs.iter() {
            if let SigKind::Prim { parent: Some(p) } = &sig.kind {
                children[p.index()].push(id);
            }
        }
        let effective_overall = match command.overall {
            Some(n) => Some(n),
            None if command.scopes.is_empty() => Some(DEFAULT_OVERALL),
            None => None,
        };
        Self {
            world,
            command,
            scope: vec![None; n],
            exact: vec![false; n],
            children,
            effective_overall,
        }
    }

    /// A sig's single primitive parent, or `None` for `univ`/subset sigs.
    fn prim_parent(&self, sig: SigId) -> Option<SigId> {
        match &self.world.sigs[sig].kind {
            SigKind::Prim { parent } => *parent,
            SigKind::Subset { .. } => None,
        }
    }

    /// A primitive sig directly under `univ` (a top-level user sig).
    fn is_top_level(&self, sig: SigId) -> bool {
        self.prim_parent(sig) == Some(self.world.builtins.univ)
    }

    /// The sigs the fixpoint and universe walk range over: non-builtin
    /// primitive sigs (subset sigs and builtins mint no atoms of their own).
    fn is_scopable(&self, sig: SigId) -> bool {
        let s = &self.world.sigs[sig];
        !s.is_builtin && matches!(s.kind, SigKind::Prim { .. })
    }

    /// Seeds the explicit `but [exactly] N SIG` scopes, validating each against
    /// the reference's per-sig rules (translation-ref §1.2). Collects every
    /// error and returns the first by source position (STYLE D1).
    fn seed_explicit(&mut self) -> Result<(), TranslateError> {
        let b = &self.world.builtins;
        let mut errors: Vec<TranslateError> = Vec::new();
        for cs in &self.command.scopes {
            let sig = cs.sig;
            // The parser already rejects a scope on `univ`/`none`
            // (`ParseError`, before this phase, matching the jar); `Int`/
            // `seq/Int`/`String` are distinct `ScopeTarget` variants that never
            // arrive as sig scopes. Skip any builtin defensively — it mints no
            // atoms regardless.
            if sig == b.univ || sig == b.none || sig == b.int || sig == b.seq_int || sig == b.string
            {
                continue;
            }
            let rs = &self.world.sigs[sig];
            match &rs.kind {
                SigKind::Subset { .. } => {
                    errors.push(TranslateError::ScopeOnSubset {
                        name: rs.name.clone(),
                        span: cs.span,
                    });
                    continue;
                }
                SigKind::Prim { .. } => {}
            }
            if rs.is_enum {
                errors.push(TranslateError::ScopeOnEnum {
                    name: rs.name.clone(),
                    span: cs.span,
                });
                continue;
            }
            if !rs.is_var {
                if let Some(err) = mult_scope_error(&rs.name, rs.mult, cs.scope, cs.span) {
                    errors.push(err);
                    continue;
                }
            }
            self.scope[sig.index()] = Some(cs.scope);
            if cs.is_exact {
                self.exact[sig.index()] = true;
            }
        }
        // A `String` scope must be exact (translation-ref §1.2). The value is a
        // scalar on the command, not a sig scope.
        if self.command.maxstring.is_some() && !self.command.string_exact {
            errors.push(TranslateError::StringScopeNotExact {
                span: self.command.span,
            });
        }
        // `util/ordering` (mt-035) forces its sig exact via `additional_exact`.
        for &sig in &self.command.additional_exact {
            self.exact[sig.index()] = true;
        }
        first_by_position(errors)
    }

    /// Forces every non-`var` `one` sig to exactly 1 and non-`var` `lone` sig
    /// to ≤ 1 before the fixpoint (translation-ref §1.2).
    fn force_multiplicities(&mut self) {
        for (id, sig) in self.world.sigs.iter() {
            if sig.is_builtin || sig.is_var || !matches!(sig.kind, SigKind::Prim { .. }) {
                continue;
            }
            match sig.mult {
                Some(SigMult::One) => {
                    self.scope[id.index()] = Some(1);
                    self.exact[id.index()] = true;
                }
                Some(SigMult::Lone) => {
                    if self.scope[id.index()].is_none() {
                        self.scope[id.index()] = Some(1);
                    }
                }
                Some(SigMult::Some) | None => {}
            }
        }
    }

    /// Runs the abstract-sum → overall → parent derivation fixpoint in strict
    /// priority order: a higher rule is re-run to exhaustion before a lower one
    /// fires, and any change restarts from the top (translation-ref §1.2).
    fn run_fixpoint(&mut self) -> Result<(), TranslateError> {
        loop {
            if self.derive_abstract() {
                continue;
            }
            if self.derive_overall()? {
                continue;
            }
            if self.derive_parent() {
                continue;
            }
            break;
        }
        // Post-fixpoint: a non-`var` `some` sig must end up ≥ 1.
        for (id, sig) in self.world.sigs.iter() {
            if !sig.is_builtin
                && !sig.is_var
                && matches!(sig.mult, Some(SigMult::Some))
                && matches!(sig.kind, SigKind::Prim { .. })
            {
                let s = self.scope[id.index()].get_or_insert(1);
                *s = (*s).max(1);
            }
        }
        Ok(())
    }

    /// Rule 1: an abstract sig's scope is the **sum** of its children when it is
    /// unscoped and all children are scoped, or a missing child's scope is the
    /// **difference** (clamped at 0) when the abstract sig is scoped and all but
    /// one child is. Returns whether it changed anything.
    fn derive_abstract(&mut self) -> bool {
        for (id, sig) in self.world.sigs.iter() {
            if sig.is_builtin || !sig.is_abstract || self.children[id.index()].is_empty() {
                continue;
            }
            let kids = &self.children[id.index()];
            let unscoped: Vec<SigId> = kids
                .iter()
                .copied()
                .filter(|k| self.scope[k.index()].is_none())
                .collect();
            let scoped_sum: u32 = kids.iter().filter_map(|k| self.scope[k.index()]).sum();
            if self.scope[id.index()].is_none() && unscoped.is_empty() {
                self.scope[id.index()] = Some(scoped_sum);
                return true;
            }
            if let (Some(parent_scope), [missing]) = (self.scope[id.index()], unscoped.as_slice()) {
                self.scope[missing.index()] = Some(parent_scope.saturating_sub(scoped_sum));
                return true;
            }
        }
        false
    }

    /// Rule 2: an unscoped top-level sig takes the overall scope; an unscoped
    /// childless enum takes 0; an unscoped top-level sig with no overall (per-sig
    /// scopes only) is an error. Returns whether it changed anything.
    fn derive_overall(&mut self) -> Result<bool, TranslateError> {
        for (id, sig) in self.world.sigs.iter() {
            if !self.is_scopable(id) || self.scope[id.index()].is_some() || !self.is_top_level(id) {
                continue;
            }
            if sig.is_enum && self.children[id.index()].is_empty() {
                self.scope[id.index()] = Some(0);
                return Ok(true);
            }
            match self.effective_overall {
                Some(n) => {
                    self.scope[id.index()] = Some(n);
                    return Ok(true);
                }
                None => {
                    return Err(TranslateError::MustSpecifyScope {
                        name: sig.name.clone(),
                        span: self.command.span,
                    });
                }
            }
        }
        Ok(false)
    }

    /// Rule 3: an unscoped non-top-level sig inherits its (scoped) parent's
    /// scope. Returns whether it changed anything.
    fn derive_parent(&mut self) -> bool {
        for (id, _) in self.world.sigs.iter() {
            if !self.is_scopable(id) || self.scope[id.index()].is_some() || self.is_top_level(id) {
                continue;
            }
            if let Some(parent) = self.prim_parent(id) {
                if let Some(ps) = self.scope[parent.index()] {
                    self.scope[id.index()] = Some(ps);
                    return true;
                }
            }
        }
        false
    }

    /// Builds the ordered universe by walking top-level sigs in declaration
    /// order, and the scope table.
    fn finish(self) -> Result<ScopedUniverse, TranslateError> {
        // Any scopable sig still unscoped after the fixpoint could not be given
        // a scope (e.g. an unscoped parent in the per-sig form) — an error.
        for (id, sig) in self.world.sigs.iter() {
            if self.is_scopable(id) && self.scope[id.index()].is_none() {
                return Err(TranslateError::MustSpecifyScope {
                    name: sig.name.clone(),
                    span: self.command.span,
                });
            }
        }

        let bitwidth = self.command.bitwidth.unwrap_or(DEFAULT_BITWIDTH);
        if bitwidth > MAX_BITWIDTH {
            return Err(TranslateError::BitwidthTooLarge {
                bitwidth,
                span: self.command.span,
            });
        }

        // --- sig atoms: recursive declaration-order walk (translation-ref §1.3)
        let mut build = UniverseBuilder {
            solver: &self,
            atoms: Vec::new(),
            minted: BTreeMap::new(),
            used_labels: BTreeSet::new(),
        };
        for (id, _) in self.world.sigs.iter() {
            if self.is_scopable(id) && self.is_top_level(id) {
                build.walk(id);
            }
        }
        let UniverseBuilder {
            mut atoms, minted, ..
        } = build;
        let sig_atom_count = atoms.len();

        // --- integer atoms: decimal values, ascending (translation-ref §1.3)
        if bitwidth >= 1 {
            let half = 1i64 << (bitwidth - 1);
            for v in -half..half {
                atoms.push(v.to_string());
            }
        }

        // String atoms are Rung 4 (see module docs): not minted here.

        let maxseq = self.compute_maxseq(bitwidth);
        let scopes = self.build_scope_table(&minted);
        Ok(ScopedUniverse {
            universe: Universe::new(atoms),
            scopes,
            bitwidth,
            maxseq,
            sig_atom_count,
        })
    }

    /// The maximum sequence length: the explicit `seq` scope, else the explicit
    /// overall (raw, not defaulted), else 4 — clamped to the largest
    /// representable integer (translation-ref §1.1).
    fn compute_maxseq(&self, bitwidth: u32) -> u32 {
        let base = self
            .command
            .maxseq
            .unwrap_or_else(|| self.command.overall.unwrap_or(4));
        let max_int = if bitwidth >= 1 {
            (1i64 << (bitwidth - 1)) - 1
        } else {
            0
        };
        base.min(u32::try_from(max_int.max(0)).unwrap_or(u32::MAX))
    }

    fn build_scope_table(&self, minted: &BTreeMap<SigId, MintedAtoms>) -> ScopeTable {
        let mut sigs = BTreeMap::new();
        for (id, _) in self.world.sigs.iter() {
            if !self.is_scopable(id) {
                continue;
            }
            sigs.insert(
                id,
                ScopedSig {
                    sig: id,
                    scope: self.scope[id.index()].unwrap_or(0),
                    is_exact: self.exact[id.index()],
                    minted: minted.get(&id).copied(),
                },
            );
        }
        ScopeTable { sigs }
    }
}

/// Walks the sig hierarchy, appending atom names in universe order.
struct UniverseBuilder<'a> {
    solver: &'a ScopeSolver<'a>,
    atoms: Vec<String>,
    minted: BTreeMap<SigId, MintedAtoms>,
    /// Labels already used, so a (pathological) qualified-name collision cannot
    /// produce duplicate atoms. Membership-only, never iterated for output
    /// (STYLE D3); a `BTreeSet` avoids any hashing.
    used_labels: BTreeSet<String>,
}

impl UniverseBuilder<'_> {
    /// Appends `sig`'s subtree (children first) and returns its lower-bound
    /// atom count. A sig mints fresh atoms only when its scope exceeds the sum
    /// of its children's lowers **and** it is exact or top-level
    /// (translation-ref §1.3) — otherwise it draws atoms from its parent's pool.
    fn walk(&mut self, sig: SigId) -> u32 {
        let mut lower = 0;
        for i in 0..self.solver.children[sig.index()].len() {
            let kid = self.solver.children[sig.index()][i];
            if self.solver.is_scopable(kid) {
                lower += self.walk(kid);
            }
        }
        let n = self.solver.scope[sig.index()].unwrap_or(0);
        let mints = self.solver.exact[sig.index()] || self.solver.is_top_level(sig);
        if n > lower && mints {
            let count = n - lower;
            let label = self.unique_label(&self.solver.world.sigs[sig].qualified_name);
            let first = AtomId::from_index(self.atoms.len());
            for k in 0..count {
                self.atoms.push(format!("{label}${k}"));
            }
            self.minted.insert(sig, MintedAtoms { first, count });
            lower + count
        } else {
            lower
        }
    }

    /// Returns `label`, disambiguating a repeat with a numeric suffix. Real
    /// models never collide (module qualification makes labels globally
    /// unique); this only guards the pathological case so the universe never
    /// panics on a duplicate atom name.
    fn unique_label(&mut self, label: &str) -> String {
        if self.used_labels.insert(label.to_owned()) {
            return label.to_owned();
        }
        for suffix in 2.. {
            let candidate = format!("{label}_{suffix}");
            if self.used_labels.insert(candidate.clone()) {
                return candidate;
            }
        }
        unreachable!("suffix search is unbounded")
    }
}

/// The multiplicity/scope conflict error for an explicit scope, if any
/// (translation-ref §1.2).
fn mult_scope_error(
    name: &str,
    mult: Option<SigMult>,
    scope: u32,
    span: als_syntax::Span,
) -> Option<TranslateError> {
    match mult {
        Some(SigMult::One) if scope != 1 => Some(TranslateError::OneSigScope {
            name: name.to_owned(),
            scope,
            span,
        }),
        Some(SigMult::Lone) if scope > 1 => Some(TranslateError::LoneSigScope {
            name: name.to_owned(),
            scope,
            span,
        }),
        Some(SigMult::Some) if scope < 1 => Some(TranslateError::SomeSigScope {
            name: name.to_owned(),
            span,
        }),
        _ => None,
    }
}

/// The first error by source position (file, start offset), for a deterministic
/// single reported error (STYLE D1), or `Ok(())` if there were none.
fn first_by_position(errors: Vec<TranslateError>) -> Result<(), TranslateError> {
    match errors
        .into_iter()
        .min_by_key(|e| (e.span().file.index(), e.span().start))
    {
        Some(err) => Err(err),
        None => Ok(()),
    }
}
