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
//! **String atoms** (mt-045, translation-ref §13, LEDGER-007) are minted here,
//! last in the universe (after the int atoms): the referenced literals
//! (collected by [`crate::strings`] from the goal + facts + sig appended facts +
//! field bounds, recursing into called funcs only) become the quoted atoms
//! `"<content>"`, padded to an exact `for … but N String` scope with synthetic
//! `"String0"`, `"String1"`, … atoms (and expanded past `N` when the referenced
//! literals already exceed it). Their order among each other is the
//! deterministic lexicographic order of their contents — the jar's is a
//! nondeterministic `HashSet`, but string atoms are symmetric so verdict/SB-0
//! count are order-independent (LEDGER-007).
//!
//! What it defers (ADR-0011): `steps` / range / increment growth scopes are
//! captured on the command but not expanded (temporal, Rung 6). `util/ordering`
//! exact forcing is mt-035 — the seam is
//! [`als_types::ResolvedCommand::additional_exact`], already honored here.

use std::collections::{BTreeMap, BTreeSet};

use als_syntax::ast::SigMult;
use als_syntax::ArenaId;
use als_types::{ModuleGraph, ResolvedCommand, ResolvedWorld, SigId, SigKind};

use crate::bounds::{AtomId, Universe};
use crate::error::TranslateError;
use crate::strings::collect_referenced_literals;

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
    /// How many leading universe atoms are sig atoms (the sig atoms come first,
    /// then the integer atoms, then the string atoms). Lets the bounds builder
    /// (mt-030) find the integer-atom run without re-deriving it.
    pub sig_atom_count: usize,
    /// How many universe atoms are integer atoms (the run immediately after the
    /// sig atoms). The string atoms are whatever trails them (translation-ref
    /// §1.3: sigs, then ascending ints, then strings).
    pub int_atom_count: usize,
    /// Every **referenced** string literal (its content, no surrounding quotes)
    /// mapped to its universe atom (mt-045, translation-ref §13). The atom's
    /// *name* carries the quote characters (`"hi"` for content `hi`); this map
    /// keys on the bare content so the lowerer can resolve an `ExprKind::Str`.
    /// Padding atoms are not here — they are never referenced.
    pub string_literals: BTreeMap<String, AtomId>,
}

impl ScopedUniverse {
    /// The half-open range of universe indices holding the integer atoms
    /// (ascending, immediately after the sig atoms).
    #[must_use]
    pub fn int_atom_range(&self) -> std::ops::Range<usize> {
        self.sig_atom_count..self.sig_atom_count + self.int_atom_count
    }

    /// The half-open range of universe indices holding the string atoms
    /// (appended last — after sig atoms and integer atoms, translation-ref
    /// §1.3).
    #[must_use]
    pub fn string_atom_range(&self) -> std::ops::Range<usize> {
        self.sig_atom_count + self.int_atom_count..self.universe.len()
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
    graph: &ModuleGraph,
    command: &ResolvedCommand,
) -> Result<ScopedUniverse, TranslateError> {
    let mut solver = ScopeSolver::new(world, graph, command);
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
    graph: &'a ModuleGraph,
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
    fn new(world: &'a ResolvedWorld, graph: &'a ModuleGraph, command: &'a ResolvedCommand) -> Self {
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
            graph,
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
        // A `String` scope must be exact (translation-ref §1.2, §13, probe S1).
        // The value is a scalar on the command, not a sig scope. Padding/
        // expansion is applied in `finish` once the referenced literals are
        // collected (mt-045).
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
    /// priority order (translation-ref §1.2). Each rule is one **full pass**
    /// over all sigs (changes accumulate within the pass — the reference
    /// queries `sig2scope` live); a rule that changed anything is re-run to
    /// exhaustion, then control restarts from the top. Pass-at-a-time matters:
    /// with per-change restarts, `derive_parent` scoping one of two unscoped
    /// siblings would let the abstract-difference rule fire on the half-updated
    /// state and back-derive the other sibling to 0 — the mt-033 baseline
    /// divergence (11 wrong UNSAT verdicts; jar-verified probe S1, `abstract
    /// sig A; sig B, C extends A; for 3` gives B=C=3, never C=0).
    fn run_fixpoint(&mut self) -> Result<(), TranslateError> {
        loop {
            if self.derive_abstract() {
                while self.derive_abstract() {}
                continue;
            }
            if self.derive_overall()? {
                while self.derive_overall()? {}
                continue;
            }
            if self.derive_parent() {
                while self.derive_parent() {}
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

    /// Rule 1 (one full pass): an abstract sig's scope is the **sum** of its
    /// children when it is unscoped and all children are scoped, or a missing
    /// child's scope is the **difference** (clamped at 0) when the abstract sig
    /// is scoped and all but one child is. Returns whether the pass changed
    /// anything.
    fn derive_abstract(&mut self) -> bool {
        let mut changed = false;
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
                changed = true;
            } else if let (Some(parent_scope), [missing]) =
                (self.scope[id.index()], unscoped.as_slice())
            {
                self.scope[missing.index()] = Some(parent_scope.saturating_sub(scoped_sum));
                changed = true;
            }
        }
        changed
    }

    /// Rule 2 (one full pass): an unscoped top-level sig takes the overall
    /// scope; an unscoped childless enum takes 0 — which the reference does
    /// **not** count as a change for loop control; an unscoped top-level sig
    /// with no overall (per-sig scopes only) is an error, raised mid-pass as
    /// the reference does. Returns whether the pass changed anything.
    fn derive_overall(&mut self) -> Result<bool, TranslateError> {
        let mut changed = false;
        for (id, sig) in self.world.sigs.iter() {
            if !self.is_scopable(id) || self.scope[id.index()].is_some() || !self.is_top_level(id) {
                continue;
            }
            if sig.is_enum && self.children[id.index()].is_empty() {
                self.scope[id.index()] = Some(0);
                continue;
            }
            match self.effective_overall {
                Some(n) => {
                    self.scope[id.index()] = Some(n);
                    changed = true;
                }
                None => {
                    return Err(TranslateError::MustSpecifyScope {
                        name: sig.name.clone(),
                        span: self.command.span,
                    });
                }
            }
        }
        Ok(changed)
    }

    /// Rule 3 (one full pass): every unscoped non-top-level sig with a scoped
    /// parent inherits that scope — all such siblings in the same pass, which
    /// is what keeps the abstract-difference rule from mis-firing (see
    /// [`ScopeSolver::run_fixpoint`]). Returns whether the pass changed
    /// anything.
    fn derive_parent(&mut self) -> bool {
        let mut changed = false;
        for (id, _) in self.world.sigs.iter() {
            if !self.is_scopable(id) || self.scope[id.index()].is_some() || self.is_top_level(id) {
                continue;
            }
            if let Some(parent) = self.prim_parent(id) {
                if let Some(ps) = self.scope[parent.index()] {
                    self.scope[id.index()] = Some(ps);
                    changed = true;
                }
            }
        }
        changed
    }

    /// Builds the ordered universe by walking top-level sigs in declaration
    /// order, and the scope table.
    fn finish(mut self) -> Result<ScopedUniverse, TranslateError> {
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
        let mut build = UniverseState {
            atoms: Vec::new(),
            minted: BTreeMap::new(),
            used_labels: BTreeSet::new(),
        };
        for (id, _) in self.world.sigs.iter() {
            if self.is_scopable(id) && self.is_top_level(id) {
                self.walk(id, &mut build);
            }
        }
        let UniverseState {
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
        let int_atom_count = atoms.len() - sig_atom_count;

        // --- string atoms: referenced literals then synthetic padding, appended
        // last (translation-ref §13, LEDGER-007).
        let string_literals = self.mint_string_atoms(&mut atoms);

        let maxseq = self.compute_maxseq(bitwidth);
        let scopes = self.build_scope_table(&minted);
        Ok(ScopedUniverse {
            universe: Universe::new(atoms),
            scopes,
            bitwidth,
            maxseq,
            sig_atom_count,
            int_atom_count,
            string_literals,
        })
    }

    /// Mints the `String` sig's atoms onto the end of `atoms` (translation-ref
    /// §13, LEDGER-007) and returns the referenced-literal → atom map:
    ///
    /// 1. collect the **referenced** literals (the goal + all facts + sig
    ///    appended facts + field bounds, recursing into called funcs — probe
    ///    S6/S7), each becoming the quoted atom `"<content>"`;
    /// 2. with an exact `for … but N String` scope, **pad** with synthetic
    ///    `"String0"`, `"String1"`, … atoms until the population reaches `N`,
    ///    **skipping** any name a referenced literal already claims (a
    ///    `HashSet`-grow no-op in the jar, §13.3);
    /// 3. if the referenced literals already **exceed** `N`, the scope
    ///    **expands** to hold them all — no padding (probe S4).
    ///
    /// The atom names carry the surrounding quotes; the returned map keys on the
    /// bare content so the lowerer resolves an `ExprKind::Str` (its s2k map).
    fn mint_string_atoms(&self, atoms: &mut Vec<String>) -> BTreeMap<String, AtomId> {
        let mut string_literals = BTreeMap::new();
        // Names already used as string atoms, so padding can skip a collision
        // (membership-only, never iterated for output — STYLE D3).
        let mut used_names: BTreeSet<String> = BTreeSet::new();

        let referenced = collect_referenced_literals(self.world, self.graph, self.command);
        for content in &referenced {
            let name = quote_atom(content);
            let id = AtomId::from_index(atoms.len());
            atoms.push(name.clone());
            used_names.insert(name);
            string_literals.insert(content.clone(), id);
        }

        // Padding: fill to an exact `maxstring`; the expansion case
        // (`#referenced > maxstring`) adds nothing since the loop condition is
        // already met (translation-ref §13.4).
        if let Some(target) = self.command.maxstring {
            let target = target as usize;
            let mut string_count = referenced.len();
            let mut idx = 0u32;
            while string_count < target {
                let name = format!("\"String{idx}\"");
                idx += 1;
                if used_names.contains(&name) {
                    continue; // a referenced literal already claims this name
                }
                atoms.push(name.clone());
                used_names.insert(name);
                string_count += 1;
            }
        }

        string_literals
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

/// The universe being built by [`ScopeSolver::walk`]: atom names in universe
/// order plus the per-sig minted runs.
struct UniverseState {
    atoms: Vec<String>,
    minted: BTreeMap<SigId, MintedAtoms>,
    /// Labels already used, so a (pathological) qualified-name collision cannot
    /// produce duplicate atoms. Membership-only, never iterated for output
    /// (STYLE D3); a `BTreeSet` avoids any hashing.
    used_labels: BTreeSet<String>,
}

impl ScopeSolver<'_> {
    /// Appends `sig`'s subtree (children first) to the universe and returns its
    /// lower-bound atom count. A sig whose scope is **smaller** than the sum of
    /// its children's lowers has its scope silently **raised** to that sum,
    /// exactness preserved — the reference's `computeLowerBound` scope-raise
    /// (`if (n < lower) n = lower`), reported but never an error
    /// (translation-ref §1.2, probe B19: `for exactly 2 P, exactly 3 C` raises
    /// `P` to exactly 3 and solves SAT). A sig mints fresh atoms only when its
    /// (possibly raised) scope exceeds that sum **and** it is exact or
    /// top-level (translation-ref §1.3) — otherwise it draws atoms from its
    /// parent's pool.
    fn walk(&mut self, sig: SigId, u: &mut UniverseState) -> u32 {
        let mut lower = 0;
        for i in 0..self.children[sig.index()].len() {
            let kid = self.children[sig.index()][i];
            if self.is_scopable(kid) {
                lower += self.walk(kid, u);
            }
        }
        let mut n = self.scope[sig.index()].unwrap_or(0);
        if n < lower {
            n = lower;
            self.scope[sig.index()] = Some(n);
        }
        let mints = self.exact[sig.index()] || self.is_top_level(sig);
        if n > lower && mints {
            let count = n - lower;
            // Atom labels are jar-pinned bare (`A$0`, `mesh/Vertex$0`,
            // translation-ref §1.3 `Util.tailThis`) — strip the root's
            // `this/` relation-name marker (translation-ref §16.3) that
            // `qualified_name` now carries; it must never reach an atom name.
            let qualified_name = &self.world.sigs[sig].qualified_name;
            let bare_name = qualified_name
                .strip_prefix("this/")
                .unwrap_or(qualified_name);
            let label = unique_label(&mut u.used_labels, bare_name);
            let first = AtomId::from_index(u.atoms.len());
            for k in 0..count {
                u.atoms.push(format!("{label}${k}"));
            }
            u.minted.insert(sig, MintedAtoms { first, count });
            lower + count
        } else {
            lower
        }
    }
}

/// Returns `label`, disambiguating a repeat with a numeric suffix. Real
/// models never collide (module qualification makes labels globally
/// unique); this only guards the pathological case so the universe never
/// panics on a duplicate atom name.
fn unique_label(used: &mut BTreeSet<String>, label: &str) -> String {
    if used.insert(label.to_owned()) {
        return label.to_owned();
    }
    for suffix in 2.. {
        let candidate = format!("{label}_{suffix}");
        if used.insert(candidate.clone()) {
            return candidate;
        }
    }
    unreachable!("suffix search is unbounded")
}

/// The universe-atom name for a string literal of `content` (translation-ref
/// §13.1): the content with its surrounding quote characters re-added (the atom
/// for literal `"hi"` is the 4-char string `"hi"`). The lexer stores the
/// unescaped content; escapes in the rare quoted form are left as-is, matching
/// the jar's `"\"" + value + "\""` atom label.
fn quote_atom(content: &str) -> String {
    format!("\"{content}\"")
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
