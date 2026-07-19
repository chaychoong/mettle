//! A deterministic CDCL SAT solver (mt-032) — the default `Solver` backend.
//!
//! This is the hand-rolled, zero-dependency CDCL solver mandated by
//! [ADR-0011](../../../docs/adr/0011-rung3-translation-solving-architecture.md)
//! decision 2: determinism and a single static binary outrank raw speed, so we
//! own the solver rather than vendoring/FFI-ing one. Everything here is a fixed
//! function of the input `Cnf` (STYLE D1/D4): no wall-clock, no unseeded
//! randomness, no hash-map iteration, no pointer values. A fixed build gives
//! byte-identical verdicts and a byte-identical enumeration sequence on every
//! machine.
//!
//! # Algorithm
//! Textbook CDCL, `MiniSat`-shaped in behavior (not in structure — PORTING R1/R3):
//!
//! - **Unit propagation** with **two watched literals** ([`CdclSolver::propagate`]).
//!   Each clause of size ≥ 2 watches `lits[0]` and `lits[1]`; a variable going
//!   false only re-examines clauses watching the now-false literal.
//! - **Conflict analysis** produces a **1-UIP** learned clause
//!   ([`CdclSolver::analyze`]), followed by **self-subsuming resolution**
//!   minimization ([`CdclSolver::minimize`], ~40 lines, a large clause-size win).
//! - **Non-chronological backjumping**: after learning, cancel to the second
//!   -highest decision level in the learned clause and assert its UIP literal.
//! - **Restarts** on the **Luby** sequence ([`Luby`]) times a fixed base — a
//!   deterministic schedule with no wall-clock component.
//! - **Decision heuristic**: **integer VSIDS with phase saving**. Activities are
//!   `u64` (not `f64`) precisely so the heuristic is bit-identical across
//!   platforms (STYLE D1) — no IEEE-754 rounding to audit. Ties break to the
//!   **lowest variable index** (STYLE D2: a total, deterministic order), and the
//!   scan is a linear pass over the dense pool, which is ample for Rung-3 scope
//!   3–5 models and obviously order-stable.
//! - **Clause database**: learned clauses are kept by default and periodically
//!   thinned by a deterministic [`CdclSolver::reduce_db`] (mt-049). The reduction
//!   is a pure function of the input CNF: its schedule is keyed only to a
//!   cumulative conflict count (no wall-clock, no DB-address hashing), it ranks
//!   deletable clauses by an **integer LBD** (glue) metric with a lowest-index
//!   tie-break, and it deletes the least-useful half. **Only solver-learned
//!   clauses are ever deleted** — original clauses and every clause added through
//!   the public [`CdclSolver::add_clause`] / [`block`] enumeration seam are
//!   permanent (deleting a blocking clause would corrupt enumeration; deleting a
//!   learned resolvent is sound). A learned clause currently **locked** (the
//!   reason for an assigned variable) is never deleted. Deletion is by
//!   **tombstone**: the clause slot stays in the arena so every `ClauseRef`
//!   (held by `reason`/`watches`/the enumeration seam) stays stable — the
//!   clause's literals are freed and it is unwatched, so it stops costing
//!   propagation time and memory without any relocating garbage collector.
//!
//! # Soundness of retained learned clauses across incremental solves
//! Every learned clause is a **resolvent of the original clauses only** — it is
//! logically implied by them. Adding *more* clauses later (the enumeration
//! blocking clauses) cannot invalidate an implication of a subset, so retaining
//! learned clauses across [`CdclSolver::add_clause`] + re-[`CdclSolver::solve`]
//! is sound. We never *remove* clauses, so no learned clause is ever invalidated
//! by deletion either.
//!
//! # Enumeration recipe (for mt-033)
//! The incremental interface is [`CdclSolver`]:
//! ```text
//! let mut s = CdclSolver::new(&cnf);
//! while let Outcome::Sat(model) = s.solve() {
//!     record(&model);
//!     // Block this model over the *primary* variables only (mt-033 blocks the
//!     // relational/primary vars, NOT the Tseitin auxiliaries): the blocking
//!     // clause forces at least one of them to flip.
//!     let clause = block(&model, &primary_vars);
//!     if clause.is_empty() { break; } // no primaries ⇒ a single model
//!     s.add_clause(clause);
//! }
//! ```
//! [`block`] builds the clause; [`CdclSolver::add_clause`] integrates it (it
//! cancels to level 0 first, so a fresh `solve` picks up cleanly). Blocking over
//! *all* variables counts raw satisfying assignments (the SB-0 gauge); blocking
//! over a subset counts distinct **projections** onto that subset.
//!
//! Returned models are **total** over every minted variable (`Assignment`'s
//! contract): CDCL only declares SAT once every variable is assigned, so no
//! don't-care fill-in is needed, but [`CdclSolver::extract_model`] defends the
//! invariant with a `debug_assert!` and a saved-phase fallback.

// STYLE S2 over-cap justification: this file is one cohesive component — the
// CDCL solver as a single state machine over shared private trail/watch/activity
// arrays — where splitting the `impl CdclSolver` across files would fragment
// tightly-coupled state for no readability gain. Roughly a third of the length is
// rustdoc (the algorithm/enumeration contract mt-033 consumes).

use crate::{Assignment, Cnf, Lit, Outcome, Solver, Var};

/// Index of a clause in the [`CdclSolver`] clause arena.
///
/// Stable for the solver's whole lifetime: clauses are only ever appended
/// (keep-all), so a `ClauseRef` never dangles and `reason`/watch entries stay
/// valid without relocation (STYLE A1 — index-based arena).
type ClauseRef = usize;

/// A clause in the arena: its literals plus reduction bookkeeping.
///
/// The first two literals are the watched pair (for size ≥ 2). For a learned
/// clause, `lits[0]` is always the asserting (UIP) literal.
///
/// `learnt` distinguishes a solver-learned resolvent (deletable by
/// [`CdclSolver::reduce_db`]) from a **permanent** clause — an original problem
/// clause or a blocking clause added through the public [`CdclSolver::add_clause`]
/// enumeration seam, neither of which may ever be deleted (soundness /
/// enumeration correctness). `lbd` is the learned clause's integer glue metric
/// (distinct decision levels at learning time; lower = more useful), the
/// reduction ranking key. A `deleted` clause is a **tombstone**: its slot stays
/// so every `ClauseRef` remains valid, but its `lits` are freed and it is
/// unwatched, so it no longer costs propagation or memory.
#[derive(Debug)]
struct Clause {
    lits: Vec<Lit>,
    learnt: bool,
    lbd: u32,
    deleted: bool,
}

/// Base restart interval in conflicts, multiplied by the Luby term. Fixed by
/// the build (STYLE D4) — a small value keeps Rung-3 problems responsive.
const RESTART_BASE: u64 = 100;

/// VSIDS bump grows by 1/16 per conflict (≈ decay 0.94), integer-exact.
const VAR_INC_GROWTH_SHIFT: u32 = 4;
/// Rescale all activities down when the increment crosses this, to bound the
/// `u64` range. The shift below preserves relative order (low bits only lost).
const VAR_ACT_RESCALE_CAP: u64 = 1 << 40;
/// Right-shift applied to every activity (and the increment) on a rescale.
const VAR_ACT_RESCALE_SHIFT: u32 = 20;

/// First learned-clause reduction fires after this many cumulative conflicts.
/// High enough that everyday small problems (a handful of conflicts) never
/// reduce and stay byte-identical to the keep-all behaviour; the reductions
/// matter only on the long/hard runs the mt-049 budgets exist to bound.
const REDUCE_FIRST_DEFAULT: u64 = 2_000;
/// Each reduction widens the gap to the next by this many conflicts, so
/// reductions thin out as the run goes on (a fixed, wall-clock-free schedule).
const REDUCE_INC_DEFAULT: u64 = 300;

/// The deterministic CDCL solver, with an incremental clause interface.
///
/// Construct with [`CdclSolver::new`] from a [`Cnf`]; call [`CdclSolver::solve`]
/// for a verdict; after a `Sat` outcome, [`CdclSolver::add_clause`] a blocking
/// clause and `solve` again to enumerate (learned clauses are retained). See the
/// module docs for the enumeration recipe.
#[derive(Debug)]
pub struct CdclSolver {
    num_vars: usize,
    /// The clause arena (problem + learned), append-only.
    clauses: Vec<Clause>,
    /// `watches[lit.code()]` = clauses watching `lit` (i.e. `lit` is one of the
    /// two watched literals). Processed when `!lit` is enqueued (STYLE D2: order
    /// within a list is a fixed function of insertion, so it is deterministic).
    watches: Vec<Vec<ClauseRef>>,

    // -- assignment / trail --
    /// Per-variable value; `None` = unassigned.
    assign: Vec<Option<bool>>,
    /// Decision level at which each variable was assigned (valid iff assigned).
    level: Vec<usize>,
    /// Reason clause for each assigned variable; `None` for a decision or a
    /// level-0 unit.
    reason: Vec<Option<ClauseRef>>,
    /// Saved polarity for phase saving; survives backtracking (that is the point).
    phase: Vec<bool>,
    /// The assignment stack, in propagation order.
    trail: Vec<Lit>,
    /// `trail_lim[d]` = index into `trail` where decision level `d+1` begins.
    trail_lim: Vec<usize>,
    /// Next trail index to propagate.
    prop_head: usize,

    // -- VSIDS --
    activity: Vec<u64>,
    var_inc: u64,

    // -- analysis scratch (reused; invariant: all `false`/empty between calls) --
    seen: Vec<bool>,

    // -- learned-clause reduction schedule (mt-049) --
    /// Cumulative conflicts over the solver's whole life (across incremental
    /// re-solves), so a long enumeration reduces periodically. Distinct from the
    /// per-call conflict budget in [`CdclSolver::solve_within`].
    conflicts_total: u64,
    /// Conflict count at which the next [`CdclSolver::reduce_db`] fires.
    next_reduce: u64,
    /// Current gap between reductions (grows by [`CdclSolver::reduce_inc`]).
    reduce_interval: u64,
    /// How much [`CdclSolver::reduce_interval`] grows per reduction.
    reduce_inc: u64,

    /// Set once a level-0 conflict or an empty clause is seen: the formula is
    /// permanently UNSAT and every future `solve` short-circuits.
    unsat: bool,
}

impl CdclSolver {
    /// Builds a solver from a CNF, integrating every clause.
    ///
    /// Unit clauses are enqueued at level 0; tautologies are dropped; the empty
    /// clause marks the formula UNSAT. See [`CdclSolver::add_clause`].
    #[must_use]
    pub fn new(cnf: &Cnf) -> Self {
        let num_vars = cnf.num_vars() as usize;
        let mut solver = Self {
            num_vars,
            clauses: Vec::new(),
            watches: vec![Vec::new(); 2 * num_vars],
            assign: vec![None; num_vars],
            level: vec![0; num_vars],
            reason: vec![None; num_vars],
            phase: vec![false; num_vars],
            trail: Vec::new(),
            trail_lim: Vec::new(),
            prop_head: 0,
            activity: vec![0; num_vars],
            var_inc: 1,
            seen: vec![false; num_vars],
            conflicts_total: 0,
            next_reduce: REDUCE_FIRST_DEFAULT,
            reduce_interval: REDUCE_FIRST_DEFAULT,
            reduce_inc: REDUCE_INC_DEFAULT,
            unsat: false,
        };
        for clause in cnf.clauses() {
            solver.add_clause(clause.clone());
        }
        solver
    }

    /// Overrides the learned-clause reduction schedule (mt-049): the first
    /// reduction fires after `first` cumulative conflicts, and each reduction
    /// widens the gap to the next by `inc`. Call before solving.
    ///
    /// [`CdclSolver::new`] installs sane defaults ([`REDUCE_FIRST_DEFAULT`] /
    /// [`REDUCE_INC_DEFAULT`]); this exists for budget tuning and for the mt-032
    /// correctness fuzz, which forces a tiny `first` so reduction runs on nearly
    /// every conflict — deletion is exercised hard while the brute-force verdict
    /// and model-count parity checks still hold (reduction only ever deletes
    /// sound resolvents, so it changes neither).
    pub fn set_reduce_schedule(&mut self, first: u64, inc: u64) {
        self.reduce_interval = first;
        self.reduce_inc = inc;
        self.next_reduce = self.conflicts_total.saturating_add(first);
    }

    /// Adds a clause to the live solver, retaining all learned clauses.
    ///
    /// Cancels to level 0 first so the clause integrates against a clean trail
    /// (the enumeration seam: a blocking clause added between solves). Normalizes
    /// the clause — duplicate literals are removed and a tautology (`x ∨ ¬x`) is
    /// dropped as vacuously satisfied. An empty clause (after normalization, or
    /// as passed) makes the formula permanently UNSAT. A unit clause is enqueued
    /// at level 0.
    ///
    /// # Panics
    /// Panics (debug) if a literal names a variable outside the pool this solver
    /// was built for (STYLE I1 — the CNF builder keeps numbering dense).
    pub fn add_clause(&mut self, lits: Vec<Lit>) {
        self.cancel_until(0);
        let Some(lits) = self.normalize(lits) else {
            return; // tautology: constrains nothing.
        };
        match lits.len() {
            0 => self.unsat = true,
            1 => {
                if !self.enqueue(lits[0], None) {
                    // Contradicts an existing level-0 unit.
                    self.unsat = true;
                }
            }
            _ => self.install_clause(lits),
        }
    }

    /// Installs a size ≥ 2 clause, choosing watches among its **non-false**
    /// literals under the current (level-0) trail.
    ///
    /// On a fresh solver every literal is unassigned, so this reduces to
    /// watching `lits[0]`/`lits[1]`. But an incremental blocking clause is added
    /// against a trail that already fixes level-0 facts, so the clause may be
    /// already **falsified** (all literals false ⇒ UNSAT) or **unit** (one
    /// non-false literal ⇒ enqueue it). Handling that here is what makes
    /// re-solving after blocking correct — propagation alone never re-examines a
    /// clause whose variables are all already assigned.
    fn install_clause(&mut self, mut lits: Vec<Lit>) {
        debug_assert!(lits.len() >= 2, "install_clause requires size >= 2");
        // Bring a non-false literal to index 0 (else the clause is falsified).
        let Some(i0) = (0..lits.len()).find(|&k| self.value_lit(lits[k]) != Some(false)) else {
            self.unsat = true;
            return;
        };
        lits.swap(0, i0);
        // Bring a second non-false literal to index 1 if one exists.
        let second = (1..lits.len()).find(|&k| self.value_lit(lits[k]) != Some(false));
        let cref = self.clauses.len();
        // If a second non-false literal exists, watch it; otherwise the clause is
        // unit under the current trail. Either way we watch lits[0]/lits[1] — in
        // the unit case lits[1] is a false literal, which keeps the two-watch
        // invariant (a watched false literal is fine; it is unassigned on the
        // relevant backtrack).
        if let Some(i1) = second {
            lits.swap(1, i1);
        }
        self.watches[lits[0].code()].push(cref);
        self.watches[lits[1].code()].push(cref);
        let unit = lits[0];
        // Permanent: `install_clause` is only reached from the public
        // `add_clause` (original CNF or an enumeration blocking clause), never
        // for a learned resolvent. `reduce_db` never deletes a permanent clause.
        self.clauses.push(Clause {
            lits,
            learnt: false,
            lbd: 0,
            deleted: false,
        });
        if second.is_none() && self.value_lit(unit).is_none() {
            // Unit: force its only non-false literal true at level 0.
            let ok = self.enqueue(unit, Some(cref));
            debug_assert!(ok, "a fresh unit literal is unassigned");
        }
    }

    /// Normalizes a clause: drop duplicate literals (keep first occurrence for
    /// determinism), and return `None` if it is a tautology (`x` and `¬x` both
    /// present — the clause is always true and is dropped).
    fn normalize(&mut self, lits: Vec<Lit>) -> Option<Vec<Lit>> {
        // `seen` is our reused scratch (all-false on entry, restored on exit).
        // Here it marks *variables* by index (a repeat is a dup or a tautology,
        // told apart via `touched`); we clear exactly what we set.
        let mut out = Vec::with_capacity(lits.len());
        let mut touched: Vec<Lit> = Vec::new();
        let mut tautology = false;
        for lit in lits {
            debug_assert!(
                lit.var().index() < self.num_vars,
                "clause literal names variable outside the solver pool"
            );
            if self.seen[lit.var().index()] {
                // Same variable already seen at this position: dup or opposite.
                if touched.iter().any(|&t| t == !lit) {
                    tautology = true;
                    break;
                }
                // exact duplicate: skip.
                continue;
            }
            self.seen[lit.var().index()] = true;
            touched.push(lit);
            out.push(lit);
        }
        for lit in touched {
            self.seen[lit.var().index()] = false;
        }
        if tautology {
            None
        } else {
            Some(out)
        }
    }

    /// Decides the current formula, returning a total assignment on `Sat`.
    ///
    /// May be called repeatedly; after a `Sat` outcome, [`CdclSolver::add_clause`]
    /// a blocking clause to enumerate the next model (learned clauses persist).
    pub fn solve(&mut self) -> Outcome {
        match self.solve_within(u64::MAX) {
            Some(outcome) => outcome,
            // `u64::MAX` conflicts cannot be reached before the heat death of
            // the machine; the unbounded entry never observes exhaustion.
            None => unreachable!("u64::MAX conflict budget exhausted"),
        }
    }

    /// Decides the current formula within a **deterministic effort budget**:
    /// at most `conflict_limit` conflicts are analyzed before giving up.
    ///
    /// Returns `None` when the budget is exhausted without a verdict — the
    /// bounded analogue of a wall-clock timeout that is a fixed function of the
    /// input (STYLE D1/D4): the same formula with the same limit exhausts (or
    /// not) identically on every machine, unlike a kill-after-N-seconds harness.
    ///
    /// On exhaustion the solver backtracks to level 0 and **remains usable**:
    /// clauses learned so far are sound resolvents and are retained, so a later
    /// `solve`/`solve_within` (or `add_clause`) continues correctly. Nothing
    /// keeps running in the background — when this returns, all effort stops
    /// and interim search state above level 0 is freed. That containment is the
    /// point: callers that used to abandon a worker thread on a wall-clock
    /// timeout leaked a live, allocating search forever (the mt-035 corpus OOM).
    pub fn solve_within(&mut self, conflict_limit: u64) -> Option<Outcome> {
        if self.unsat {
            return Some(Outcome::Unsat);
        }
        // Level-0 propagation of any units added since the last solve.
        if self.propagate().is_some() {
            self.unsat = true;
            return Some(Outcome::Unsat);
        }
        let mut luby = Luby::new();
        let mut restart_limit = RESTART_BASE * luby.next();
        let mut conflicts_since_restart: u64 = 0;
        let mut total_conflicts: u64 = 0;

        loop {
            if let Some(confl) = self.propagate() {
                if self.decision_level() == 0 {
                    self.unsat = true;
                    return Some(Outcome::Unsat);
                }
                if total_conflicts >= conflict_limit {
                    // Budget exhausted: stop cleanly, keep what was learned.
                    self.cancel_until(0);
                    return None;
                }
                total_conflicts += 1;
                conflicts_since_restart += 1;
                self.conflicts_total += 1;
                let (learnt, bt_level, lbd) = self.analyze(confl);
                self.cancel_until(bt_level);
                self.learn_and_assert(learnt, lbd);
                self.decay_var_inc();
            } else {
                // Learned-clause reduction (mt-049): a pure function of the
                // cumulative conflict count, so it fires at the same points on
                // every machine and every run. Done at level 0 (like a restart),
                // where locked clauses are exactly the reasons of level-0 facts.
                if self.conflicts_total >= self.next_reduce {
                    self.cancel_until(0);
                    self.reduce_db();
                    self.reduce_interval = self.reduce_interval.saturating_add(self.reduce_inc);
                    self.next_reduce = self.conflicts_total.saturating_add(self.reduce_interval);
                    conflicts_since_restart = 0;
                    continue;
                }
                if conflicts_since_restart >= restart_limit {
                    self.cancel_until(0);
                    conflicts_since_restart = 0;
                    restart_limit = RESTART_BASE * luby.next();
                    continue;
                }
                match self.pick_branch() {
                    None => return Some(Outcome::Sat(self.extract_model())),
                    Some(lit) => {
                        self.trail_lim.push(self.trail.len());
                        let ok = self.enqueue(lit, None);
                        debug_assert!(ok, "branching on an unassigned var cannot conflict");
                    }
                }
            }
        }
    }

    /// Two-watched-literal unit propagation.
    ///
    /// Returns the conflicting clause if propagation hits a falsified clause,
    /// else `None` (fixpoint reached). Only clauses watching a newly-false
    /// literal are examined.
    fn propagate(&mut self) -> Option<ClauseRef> {
        let mut conflict = None;
        'trail: while self.prop_head < self.trail.len() {
            let p = self.trail[self.prop_head];
            self.prop_head += 1;
            let false_lit = !p; // this literal just became false
            let false_code = false_lit.code();

            // Take the watch list out to sidestep the borrow checker; nothing we
            // do inside pushes into this same list (a replacement literal is
            // never `false_lit`), so this is sound (STYLE D2: order preserved).
            let mut ws = std::mem::take(&mut self.watches[false_code]);
            let mut i = 0; // read cursor
            let mut j = 0; // write cursor (compaction of retained watchers)
            while i < ws.len() {
                let cref = ws[i];
                // Ensure the now-false literal sits at index 1, the other at 0.
                if self.clauses[cref].lits[0] == false_lit {
                    self.clauses[cref].lits.swap(0, 1);
                }
                let other = self.clauses[cref].lits[0];
                if self.value_lit(other) == Some(true) {
                    // Clause already satisfied by its other watch: keep watching.
                    ws[j] = cref;
                    i += 1;
                    j += 1;
                    continue;
                }
                // Hunt for a non-false literal in lits[2..] to watch instead.
                let len = self.clauses[cref].lits.len();
                let mut replaced = false;
                for k in 2..len {
                    let cand = self.clauses[cref].lits[k];
                    if self.value_lit(cand) != Some(false) {
                        self.clauses[cref].lits[1] = cand;
                        self.clauses[cref].lits[k] = false_lit;
                        self.watches[cand.code()].push(cref);
                        replaced = true;
                        break;
                    }
                }
                if replaced {
                    // Migrated: drop from this list (do not advance `j`).
                    i += 1;
                    continue;
                }
                // No replacement: `other` is the last hope.
                if self.value_lit(other) == Some(false) {
                    // Conflict: retain this and all remaining watchers, then stop.
                    while i < ws.len() {
                        ws[j] = ws[i];
                        i += 1;
                        j += 1;
                    }
                    ws.truncate(j);
                    self.watches[false_code] = ws;
                    conflict = Some(cref);
                    break 'trail;
                }
                // Unit: force `other` true, keep watching here.
                let ok = self.enqueue(other, Some(cref));
                debug_assert!(ok, "enqueue of an unassigned unit literal cannot conflict");
                ws[j] = cref;
                i += 1;
                j += 1;
            }
            ws.truncate(j);
            self.watches[false_code] = ws;
        }
        conflict
    }

    /// 1-UIP conflict analysis with self-subsuming minimization.
    ///
    /// Returns the learned clause (its asserting literal at index 0, its second
    /// watch — the highest-level remaining literal — at index 1), the backjump
    /// level, and the clause's **LBD** (distinct decision levels among its
    /// literals — the reduction usefulness metric, mt-049). Bumps the activity of
    /// every variable resolved through.
    fn analyze(&mut self, conflict: ClauseRef) -> (Vec<Lit>, usize, u32) {
        let cur_level = self.decision_level();
        let mut learnt: Vec<Lit> = vec![Lit::positive(Var::from_index(0))]; // slot 0
        let mut to_clear: Vec<Var> = Vec::new();
        let mut path = 0usize;
        let mut trail_idx = self.trail.len();
        let mut confl = conflict;
        let mut resolved: Option<Lit> = None;

        loop {
            // For the conflict clause include all literals; for a reason clause
            // skip index 0 (the literal it implied, i.e. `resolved`).
            let start = usize::from(resolved.is_some());
            let len = self.clauses[confl].lits.len();
            for k in start..len {
                let q = self.clauses[confl].lits[k];
                let v = q.var();
                if !self.seen[v.index()] && self.level[v.index()] > 0 {
                    self.bump(v);
                    self.seen[v.index()] = true;
                    if self.level[v.index()] >= cur_level {
                        path += 1;
                    } else {
                        learnt.push(q);
                        to_clear.push(v);
                    }
                }
            }
            // Walk the trail down to the next literal we resolved on.
            loop {
                trail_idx -= 1;
                if self.seen[self.trail[trail_idx].var().index()] {
                    break;
                }
            }
            let p = self.trail[trail_idx];
            self.seen[p.var().index()] = false;
            path -= 1;
            if path == 0 {
                resolved = Some(p);
                break;
            }
            confl = match self.reason[p.var().index()] {
                Some(c) => c,
                None => unreachable!("intermediate UIP literal must have a reason clause"),
            };
            resolved = Some(p);
        }
        // `resolved` is the UIP; its negation is the asserting literal.
        let Some(uip) = resolved else {
            unreachable!("analysis always resolves to a UIP")
        };
        learnt[0] = !uip;

        // Minimize (self-subsuming resolution) before choosing the second watch.
        self.minimize(&mut learnt, &mut to_clear);

        let bt_level = self.order_second_watch(&mut learnt);

        // Restore the `seen` scratch to all-false (invariant for the next call).
        for v in to_clear {
            self.seen[v.index()] = false;
        }

        debug_assert!(
            learnt.iter().all(|&l| self.value_lit(l) == Some(false)),
            "every literal of a freshly learned clause must be false under the trail"
        );
        // LBD (glue): distinct decision levels among the literals, valid here
        // because every literal is false with a live `level` (asserted above).
        let lbd = self.literal_block_distance(&learnt);
        (learnt, bt_level, lbd)
    }

    /// The **literal block distance** of a clause: the count of distinct decision
    /// levels among its literals (mt-049 reduction metric). All integer, a pure
    /// function of the current levels — deterministic (STYLE D1). Callers pass a
    /// clause all of whose literals are assigned (levels valid).
    fn literal_block_distance(&self, lits: &[Lit]) -> u32 {
        let mut levels: Vec<usize> = lits.iter().map(|l| self.level[l.var().index()]).collect();
        levels.sort_unstable();
        levels.dedup();
        // Clause sizes are tiny; `usize → u32` cannot overflow a realistic level
        // count, and the cap keeps it total.
        u32::try_from(levels.len()).unwrap_or(u32::MAX)
    }

    /// Drops literals of `learnt[1..]` that are redundant by self-subsuming
    /// resolution: a literal is removable if every literal of its reason clause
    /// is already in the clause (`seen`) or itself recursively removable.
    ///
    /// On entry `seen` is `true` for exactly the vars of `learnt[1..]`; this
    /// method also marks `learnt[0]`'s var and any proven-removable vars, all
    /// tracked in `to_clear` so [`CdclSolver::analyze`] restores the scratch.
    fn minimize(&mut self, learnt: &mut Vec<Lit>, to_clear: &mut Vec<Var>) {
        // Mark the asserting literal too, so it counts as "already present".
        self.seen[learnt[0].var().index()] = true;
        to_clear.push(learnt[0].var());

        let mut write = 1;
        for read in 1..learnt.len() {
            let lit = learnt[read];
            let keep =
                self.reason[lit.var().index()].is_none() || !self.lit_redundant(lit, to_clear);
            if keep {
                learnt[write] = lit;
                write += 1;
            }
        }
        learnt.truncate(write);
    }

    /// Whether `lit` is redundant: a DFS over reason clauses, marking proven
    /// vars in `seen` (memoized via `to_clear`). Rolls back marks made for this
    /// specific query if it fails, matching `MiniSat`'s `litRedundant`.
    fn lit_redundant(&mut self, lit: Lit, to_clear: &mut Vec<Var>) -> bool {
        let rollback_from = to_clear.len();
        let mut stack: Vec<Lit> = vec![lit];
        while let Some(l) = stack.pop() {
            let Some(cref) = self.reason[l.var().index()] else {
                // A decision literal: not resolvable away — fail, roll back.
                for &v in &to_clear[rollback_from..] {
                    self.seen[v.index()] = false;
                }
                to_clear.truncate(rollback_from);
                return false;
            };
            let len = self.clauses[cref].lits.len();
            for k in 1..len {
                let q = self.clauses[cref].lits[k];
                let v = q.var();
                if self.seen[v.index()] || self.level[v.index()] == 0 {
                    continue; // already accounted for, or a level-0 fixed literal
                }
                if self.reason[v.index()].is_some() {
                    self.seen[v.index()] = true;
                    to_clear.push(v);
                    stack.push(q);
                } else {
                    // Hits a decision literal not in the clause: not redundant.
                    for &vv in &to_clear[rollback_from..] {
                        self.seen[vv.index()] = false;
                    }
                    to_clear.truncate(rollback_from);
                    return false;
                }
            }
        }
        true
    }

    /// Moves the highest-level literal of `learnt[1..]` to index 1 (the second
    /// watch) and returns the backjump level (0 for a learned unit).
    fn order_second_watch(&self, learnt: &mut [Lit]) -> usize {
        if learnt.len() == 1 {
            return 0;
        }
        let mut max_i = 1;
        let mut max_level = self.level[learnt[1].var().index()];
        for (i, &lit) in learnt.iter().enumerate().skip(2) {
            let l = self.level[lit.var().index()];
            if l > max_level {
                max_level = l;
                max_i = i;
            }
        }
        learnt.swap(1, max_i);
        max_level
    }

    /// Installs a freshly learned clause and asserts its UIP literal.
    ///
    /// A learned unit is enqueued at level 0 with no reason; a larger clause is
    /// appended (marked `learnt`, so [`CdclSolver::reduce_db`] may later delete
    /// it), watched on its first two literals, and its UIP literal (index 0)
    /// enqueued with the clause as reason.
    fn learn_and_assert(&mut self, learnt: Vec<Lit>, lbd: u32) {
        if learnt.len() == 1 {
            let ok = self.enqueue(learnt[0], None);
            debug_assert!(ok, "a learned unit asserts a fresh literal at level 0");
            return;
        }
        let cref = self.clauses.len();
        self.watches[learnt[0].code()].push(cref);
        self.watches[learnt[1].code()].push(cref);
        let asserting = learnt[0];
        self.clauses.push(Clause {
            lits: learnt,
            learnt: true,
            lbd,
            deleted: false,
        });
        let ok = self.enqueue(asserting, Some(cref));
        debug_assert!(ok, "the asserting literal is unassigned after backjump");
    }

    /// Deterministically thins the learned-clause database (mt-049): deletes the
    /// least-useful half of the deletable learned clauses, ranked by integer LBD
    /// (lower = keep) with a lowest-`ClauseRef` tie-break.
    ///
    /// **Soundness.** Only `learnt` clauses are candidates — original and
    /// blocking clauses are permanent, so verdicts and the enumeration model set
    /// are untouched (a learned clause is a resolvent of the permanents; deleting
    /// it removes no models). A **locked** clause (the reason of a currently
    /// -assigned variable) is never deleted, so conflict analysis never chases a
    /// dangling reason. Runs at decision level 0, where the only assigned
    /// variables are level-0 facts, so "locked" is precisely "reason of a level-0
    /// literal".
    ///
    /// **Stability.** Deletion is a tombstone: the arena slot stays, keeping every
    /// `ClauseRef` (in `reason`, in `watches`, held across the enumeration seam)
    /// valid. The deleted clause's literals are freed and it is dropped from every
    /// watch list, so it stops costing propagation time and memory.
    fn reduce_db(&mut self) {
        debug_assert_eq!(self.decision_level(), 0, "reduce_db must run at level 0");
        let mut candidates: Vec<ClauseRef> = Vec::new();
        for cref in 0..self.clauses.len() {
            let c = &self.clauses[cref];
            if !c.learnt || c.deleted {
                continue; // permanent or already a tombstone
            }
            // Locked: the reason of an assigned variable (MiniSat `locked`).
            let uip = c.lits[0];
            let locked =
                self.value_lit(uip) == Some(true) && self.reason[uip.var().index()] == Some(cref);
            if !locked {
                candidates.push(cref);
            }
        }
        // Keep the most useful half: lowest LBD first, lowest ClauseRef to break
        // ties — a total, deterministic order (STYLE D2). The worst half is
        // deleted.
        candidates.sort_by_key(|&c| (self.clauses[c].lbd, c));
        let keep = candidates.len() / 2;
        for &cref in &candidates[keep..] {
            let c = &mut self.clauses[cref];
            c.deleted = true;
            c.lits = Vec::new(); // reclaim the bulk of the memory
        }
        // One pass over the watch lists drops every tombstoned clause, order
        // preserved (STYLE D2). Taken out to sidestep the borrow checker.
        let mut watches = std::mem::take(&mut self.watches);
        for list in &mut watches {
            list.retain(|&cref| !self.clauses[cref].deleted);
        }
        self.watches = watches;
    }

    /// Assigns `lit` true with the given reason, pushing it on the trail.
    ///
    /// Returns `false` (without assigning) if `lit` is already false — a
    /// conflict at the point of enqueue (used for level-0 unit integration).
    fn enqueue(&mut self, lit: Lit, reason: Option<ClauseRef>) -> bool {
        match self.value_lit(lit) {
            Some(true) => true,
            Some(false) => false,
            None => {
                let v = lit.var();
                self.assign[v.index()] = Some(lit.is_positive());
                self.phase[v.index()] = lit.is_positive();
                self.level[v.index()] = self.decision_level();
                self.reason[v.index()] = reason;
                self.trail.push(lit);
                true
            }
        }
    }

    /// Backtracks to `level`, unassigning everything above it (phases are kept —
    /// that is phase saving). Idempotent when already at or below `level`.
    fn cancel_until(&mut self, level: usize) {
        if self.decision_level() <= level {
            return;
        }
        let target = self.trail_lim[level];
        while self.trail.len() > target {
            let Some(lit) = self.trail.pop() else { break };
            let v = lit.var();
            self.assign[v.index()] = None;
            self.reason[v.index()] = None;
            // `phase[v]` intentionally retained.
        }
        self.trail_lim.truncate(level);
        self.prop_head = self.trail.len();
    }

    /// Picks the next decision literal: the unassigned variable of highest
    /// activity (ties → lowest index), branched on its saved phase.
    ///
    /// Linear scan over the dense pool — deterministic by construction and more
    /// than fast enough at Rung-3 scope (STYLE D2 note in the module docs).
    fn pick_branch(&self) -> Option<Lit> {
        let mut best: Option<usize> = None;
        let mut best_act = 0u64;
        for v in 0..self.num_vars {
            if self.assign[v].is_none() {
                let act = self.activity[v];
                // Strict `>` with an ascending scan makes the lowest index win
                // ties — a total, deterministic order (STYLE D2).
                if best.is_none() || act > best_act {
                    best = Some(v);
                    best_act = act;
                }
            }
        }
        best.map(|v| {
            let var = Var::from_index(v);
            if self.phase[v] {
                Lit::positive(var)
            } else {
                Lit::negative(var)
            }
        })
    }

    /// Extracts the total model at a `Sat` fixpoint.
    ///
    /// CDCL declares SAT only when every variable is assigned, so this is total;
    /// the `debug_assert!` pins that invariant and the saved-phase fallback keeps
    /// the returned `Assignment` total even were the invariant ever violated.
    fn extract_model(&self) -> Assignment {
        let values: Vec<bool> = (0..self.num_vars)
            .map(|v| {
                debug_assert!(
                    self.assign[v].is_some(),
                    "SAT model must assign every variable"
                );
                self.assign[v].unwrap_or(self.phase[v])
            })
            .collect();
        Assignment::new(values)
    }

    /// The value of a literal under the current assignment.
    fn value_lit(&self, lit: Lit) -> Option<bool> {
        self.assign[lit.var().index()].map(|b| b == lit.is_positive())
    }

    /// Current decision level = number of decisions on the trail.
    fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }

    /// Bumps a variable's VSIDS activity, rescaling all activities if the
    /// increment would grow the range past the cap. Integer-exact (STYLE D1).
    fn bump(&mut self, var: Var) {
        self.activity[var.index()] = self.activity[var.index()].saturating_add(self.var_inc);
        if self.activity[var.index()] > VAR_ACT_RESCALE_CAP {
            self.rescale_activities();
        }
    }

    /// Grows the activity increment (the integer analogue of decay): future
    /// bumps count for more, so recently-active variables sort higher.
    fn decay_var_inc(&mut self) {
        self.var_inc = self
            .var_inc
            .saturating_add(self.var_inc >> VAR_INC_GROWTH_SHIFT);
        if self.var_inc > VAR_ACT_RESCALE_CAP {
            self.rescale_activities();
        }
    }

    /// Shifts every activity (and the increment) down, bounding the `u64` range
    /// while preserving order well enough for the heuristic (low bits only lost;
    /// the lowest-index tie-break is exact regardless).
    fn rescale_activities(&mut self) {
        for a in &mut self.activity {
            *a >>= VAR_ACT_RESCALE_SHIFT;
        }
        self.var_inc = (self.var_inc >> VAR_ACT_RESCALE_SHIFT).max(1);
    }
}

/// The reluctant-doubling generator for the **Luby** restart sequence
/// (Knuth 2012): `1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, …`.
///
/// Purely arithmetic state — no wall-clock, no randomness (STYLE D4). Each
/// [`Luby::next`] yields the next term; the solver multiplies it by
/// [`RESTART_BASE`] to get the conflict budget until the next restart.
#[derive(Debug)]
struct Luby {
    u: u64,
    v: u64,
}

impl Luby {
    fn new() -> Self {
        Self { u: 1, v: 1 }
    }

    fn next(&mut self) -> u64 {
        let value = self.v;
        if self.u & self.u.wrapping_neg() == self.v {
            self.u += 1;
            self.v = 1;
        } else {
            self.v *= 2;
        }
        value
    }
}

/// Builds a **blocking clause** that rules out `assignment`'s projection onto
/// `vars`: the disjunction of each variable's *currently-false* literal, so any
/// satisfying extension must flip at least one of them.
///
/// The enumeration primitive for mt-033 (see the module docs). Passing every
/// variable blocks the exact model (raw-count / SB-0 enumeration); passing a
/// subset blocks the projection (distinct-projection enumeration). An empty
/// `vars` yields an empty clause — the caller should treat that as "no further
/// models to distinguish" and stop.
#[must_use]
pub fn block(assignment: &Assignment, vars: &[Var]) -> Vec<Lit> {
    vars.iter()
        .map(|&v| {
            if assignment.value(v) {
                Lit::negative(v)
            } else {
                Lit::positive(v)
            }
        })
        .collect()
}

/// The one-shot [`Solver`] backend: the default CDCL solver behind the trait
/// seam (ADR-0011 keeps `Solver` as the open boundary for a future optional FFI
/// backend). For enumeration, construct a [`CdclSolver`] directly.
#[derive(Debug, Default, Clone, Copy)]
pub struct Cdcl;

impl Solver for Cdcl {
    fn solve(&mut self, cnf: &Cnf) -> Outcome {
        CdclSolver::new(cnf).solve()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(cnf: &mut Cnf) -> Var {
        cnf.fresh_var()
    }

    #[test]
    fn empty_cnf_is_sat_with_empty_model() {
        let cnf = Cnf::new();
        match CdclSolver::new(&cnf).solve() {
            Outcome::Sat(a) => assert_eq!(a, Assignment::new(vec![])),
            Outcome::Unsat => panic!("empty CNF must be SAT"),
        }
    }

    #[test]
    fn empty_clause_is_unsat() {
        let mut cnf = Cnf::new();
        let _ = var(&mut cnf);
        cnf.add_clause(vec![]);
        assert_eq!(CdclSolver::new(&cnf).solve(), Outcome::Unsat);
    }

    #[test]
    fn contradictory_units_are_unsat() {
        let mut cnf = Cnf::new();
        let x = var(&mut cnf);
        cnf.add_clause(vec![Lit::positive(x)]);
        cnf.add_clause(vec![Lit::negative(x)]);
        assert_eq!(CdclSolver::new(&cnf).solve(), Outcome::Unsat);
    }

    #[test]
    fn tautological_clause_is_dropped() {
        let mut cnf = Cnf::new();
        let x = var(&mut cnf);
        // (x ∨ ¬x) constrains nothing; the formula stays SAT.
        cnf.add_clause(vec![Lit::positive(x), Lit::negative(x)]);
        assert!(matches!(CdclSolver::new(&cnf).solve(), Outcome::Sat(_)));
    }

    #[test]
    fn duplicate_literals_are_handled() {
        let mut cnf = Cnf::new();
        let x = var(&mut cnf);
        let y = var(&mut cnf);
        // (x ∨ x ∨ ¬y) with a dup; plus ¬x forces y false.
        cnf.add_clause(vec![Lit::positive(x), Lit::positive(x), Lit::negative(y)]);
        cnf.add_clause(vec![Lit::negative(x)]);
        match CdclSolver::new(&cnf).solve() {
            Outcome::Sat(a) => {
                assert!(!a.value(x));
                assert!(!a.value(y));
            }
            Outcome::Unsat => panic!("must be SAT"),
        }
    }

    #[test]
    fn unit_only_problem() {
        let mut cnf = Cnf::new();
        let x = var(&mut cnf);
        let y = var(&mut cnf);
        cnf.add_clause(vec![Lit::positive(x)]);
        cnf.add_clause(vec![Lit::negative(y)]);
        match CdclSolver::new(&cnf).solve() {
            Outcome::Sat(a) => {
                assert!(a.value(x));
                assert!(!a.value(y));
            }
            Outcome::Unsat => panic!("must be SAT"),
        }
    }

    #[test]
    fn resolve_after_blocking_only_model_is_unsat() {
        // (x) ∧ (y): the single model is x=1,y=1. Block it, re-solve ⇒ UNSAT.
        let mut cnf = Cnf::new();
        let x = var(&mut cnf);
        let y = var(&mut cnf);
        cnf.add_clause(vec![Lit::positive(x)]);
        cnf.add_clause(vec![Lit::positive(y)]);
        let mut solver = CdclSolver::new(&cnf);
        let model = match solver.solve() {
            Outcome::Sat(a) => a,
            Outcome::Unsat => panic!("first solve must be SAT"),
        };
        assert!(model.value(x) && model.value(y));
        solver.add_clause(block(&model, &[x, y]));
        assert_eq!(solver.solve(), Outcome::Unsat);
    }

    #[test]
    fn solve_within_exhausts_and_recovers() {
        // (x∨y)(x∨¬y)(¬x∨y)(¬x∨¬y): UNSAT, and no verdict is reachable without
        // analyzing at least one conflict.
        let mut cnf = Cnf::new();
        let x = var(&mut cnf);
        let y = var(&mut cnf);
        cnf.add_clause(vec![Lit::positive(x), Lit::positive(y)]);
        cnf.add_clause(vec![Lit::positive(x), Lit::negative(y)]);
        cnf.add_clause(vec![Lit::negative(x), Lit::positive(y)]);
        cnf.add_clause(vec![Lit::negative(x), Lit::negative(y)]);
        let mut solver = CdclSolver::new(&cnf);
        // Zero budget: the first conflict exhausts it — no verdict.
        assert_eq!(solver.solve_within(0), None);
        // The solver stays usable: an unbounded solve completes correctly.
        assert_eq!(solver.solve(), Outcome::Unsat);
    }

    #[test]
    fn solve_within_no_conflicts_ignores_budget() {
        // A unit-only problem solves by propagation alone: zero budget suffices.
        let mut cnf = Cnf::new();
        let x = var(&mut cnf);
        cnf.add_clause(vec![Lit::positive(x)]);
        let mut solver = CdclSolver::new(&cnf);
        match solver.solve_within(0) {
            Some(Outcome::Sat(a)) => assert!(a.value(x)),
            other => panic!("expected SAT within zero conflicts, got {other:?}"),
        }
    }

    /// Pigeonhole PHP(pigeons, holes): UNSAT when pigeons > holes, and hard
    /// enough (many conflicts) to drive several reductions.
    fn pigeonhole(cnf: &mut Cnf, pigeons: usize, holes: usize) {
        let p: Vec<Vec<Var>> = (0..pigeons)
            .map(|_| (0..holes).map(|_| cnf.fresh_var()).collect())
            .collect();
        for row in &p {
            cnf.add_clause(row.iter().map(|&v| Lit::positive(v)).collect());
        }
        for i in 0..pigeons {
            for j in (i + 1)..pigeons {
                for (&pih, &pjh) in p[i].iter().zip(&p[j]) {
                    cnf.add_clause(vec![Lit::negative(pih), Lit::negative(pjh)]);
                }
            }
        }
    }

    #[test]
    fn reduce_db_deletes_only_learned_and_stays_correct() {
        // PHP(7,6): UNSAT, learning-heavy. Forcing reduction on nearly every
        // conflict must (a) keep the correct verdict and (b) actually tombstone
        // learned clauses — proving reduce_db is exercised, not merely enabled —
        // while (c) never deleting a permanent (problem/blocking) clause.
        let mut cnf = Cnf::new();
        pigeonhole(&mut cnf, 7, 6);
        let mut s = CdclSolver::new(&cnf);
        s.set_reduce_schedule(1, 1);
        assert_eq!(s.solve(), Outcome::Unsat, "PHP(7,6) is UNSAT");
        assert!(
            s.clauses.iter().any(|c| c.deleted),
            "reduce_db must have tombstoned at least one learned clause"
        );
        assert!(
            s.clauses.iter().all(|c| !c.deleted || c.learnt),
            "only learned clauses may ever be tombstoned"
        );
    }

    #[test]
    fn reduce_db_preserves_enumeration_count() {
        // A small SAT problem with several models: forcing frequent reduction
        // must not change the raw (SB-0) model count — reduction deletes only
        // sound resolvents, which removes no models.
        let mut cnf = Cnf::new();
        let vars: Vec<Var> = (0..4).map(|_| cnf.fresh_var()).collect();
        // (x0 ∨ x1) ∧ (x2 ∨ x3): 3×3 = 9 satisfying assignments over 4 vars.
        cnf.add_clause(vec![Lit::positive(vars[0]), Lit::positive(vars[1])]);
        cnf.add_clause(vec![Lit::positive(vars[2]), Lit::positive(vars[3])]);
        let count = |reduce: Option<(u64, u64)>| {
            let mut s = CdclSolver::new(&cnf);
            if let Some((f, i)) = reduce {
                s.set_reduce_schedule(f, i);
            }
            let mut n = 0u64;
            while let Outcome::Sat(m) = s.solve() {
                n += 1;
                s.add_clause(block(&m, &vars));
            }
            n
        };
        assert_eq!(count(None), 9, "baseline count");
        assert_eq!(
            count(Some((1, 1))),
            9,
            "count invariant under forced reduction"
        );
    }

    #[test]
    fn luby_sequence_prefix() {
        let mut luby = Luby::new();
        let got: Vec<u64> = (0..15).map(|_| luby.next()).collect();
        assert_eq!(got, vec![1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8]);
    }
}
