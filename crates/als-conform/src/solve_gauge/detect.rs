//! The SB-0 count-divergence classifier (ordered-abstract partition) and the
//! mettle defer-reason classifier for the solve gauge (mt-037).
//!
//! The count classifier exists to keep the counting net **honest**: it carves
//! out the goal family where mettle's raw SB-0 count legitimately differs from
//! the jar's (documented in LIMITATIONS, translation-ref §10.1), so the net
//! never fabricates a `COUNT_MISMATCH`. Following the gauge's contract (a wrong
//! skip only loses coverage; a wrong inclusion fabricates a disagreement) it is
//! written to **over-skip** when in doubt. (First-order skolemization now counts
//! exactly, mt-047, so its former `skip_fo_skolem` family is gone.)

use als_core::ScopedUniverse;
use als_core::TranslateError;
use als_types::{ResolvedWorld, SigId, SigKind};

/// Whether this command opens `util/ordering` over a sig whose population is a
/// **free partition** — an ordered sig with at least one non-exact prim
/// (`extends`) child (the T14a / T14d family, translation-ref §10.1). At
/// symmetry 0 the jar mints atoms per child and counts each atom→child
/// labelling separately; mettle mints canonical parent atoms, so the counts
/// diverge by a permutation factor while the verdict agrees (LIMITATIONS).
///
/// Over-skips deliberately: any ordered sig with a non-exact prim descendant
/// disqualifies the command from the counting net, whether or not the parent is
/// `abstract` (T14a's non-abstract ordered sig diverges too). Determinate-
/// population cases — all children exact (T14b/c/e), or no children at all
/// (T10–T13, T15) — are **not** skipped and count exactly.
#[must_use]
pub fn ordered_abstract_partition(world: &ResolvedWorld, scoped: &ScopedUniverse) -> bool {
    world
        .ordering
        .iter()
        .any(|oi| has_nonexact_prim_child(world, scoped, oi.elem))
}

/// The single prim (`extends`) parent of `sig`, or `None` for a root prim sig
/// or a subset (`in`/`=`) sig (which never partitions an ordered pool).
fn prim_parent(world: &ResolvedWorld, sig: SigId) -> Option<SigId> {
    match &world.sigs[sig].kind {
        SigKind::Prim { parent } => *parent,
        SigKind::Subset { .. } => None,
    }
}

/// Whether any sig is a transitive prim descendant of `elem` and non-exact in
/// this command's scope. A sig with no scope entry is treated as non-exact
/// (free) — the conservative direction.
fn has_nonexact_prim_child(world: &ResolvedWorld, scoped: &ScopedUniverse, elem: SigId) -> bool {
    for (sig, _) in world.sigs.iter() {
        if sig == elem {
            continue;
        }
        if !is_prim_descendant(world, sig, elem) {
            continue;
        }
        let exact = scoped.scopes.get(sig).is_some_and(|sc| sc.is_exact);
        if !exact {
            return true;
        }
    }
    false
}

/// Whether `sig`'s prim-parent chain reaches `ancestor`. Bounded by the sig
/// count so a (resolve-rejected, but defensively guarded) inheritance cycle
/// cannot loop forever.
fn is_prim_descendant(world: &ResolvedWorld, sig: SigId, ancestor: SigId) -> bool {
    let mut current = prim_parent(world, sig);
    for _ in 0..world.sigs.len() {
        match current {
            Some(p) if p == ancestor => return true,
            Some(p) => current = prim_parent(world, p),
            None => return false,
        }
    }
    false
}

/// The stable class of a **lowering** defer (`lower_command`'s typed error), for
/// the gauge's `mettle_defer:lower:<class>` sub-bucket. Scope-phase and
/// encode-phase defers are bucketed by the caller from their own phase, so those
/// variants are not expected here — but the classifier stays total (`PORTING`
/// R1: no catch-all) so a new `TranslateError` variant is a compile error, not a
/// silently mis-bucketed defer.
#[must_use]
pub fn lower_defer_class(err: &TranslateError) -> &'static str {
    match err {
        TranslateError::TemporalUnsupported { .. } => "temporal",
        TranslateError::LoweringUnsupported { .. } => "lowering",
        TranslateError::HigherOrder { .. } => "higher_order",
        TranslateError::CapacityExceeded { .. } => "capacity",
        TranslateError::ScopeOnSubset { .. }
        | TranslateError::ScopeOnEnum { .. }
        | TranslateError::StringScopeNotExact { .. }
        | TranslateError::OneSigScope { .. }
        | TranslateError::LoneSigScope { .. }
        | TranslateError::SomeSigScope { .. }
        | TranslateError::MustSpecifyScope { .. }
        | TranslateError::BitwidthTooLarge { .. } => "scope",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use als_core::{compute_universe, ScopedUniverse};
    use als_types::{MapLoader, ModuleGraph, ResolvedWorld};

    // --- ordered-abstract detector, via the real pipeline -----------------

    /// Resolves `source` (with the embedded stdlib as fallback) and computes the
    /// scoped universe of command 0.
    fn pipeline(source: &str) -> (ResolvedWorld, ScopedUniverse) {
        let loader = MapLoader::new();
        let graph = ModuleGraph::load_with_source("mem/model.als", source.to_owned(), &loader)
            .unwrap_or_else(|e| panic!("load failed: {e:?}"));
        let resolved =
            als_types::resolve(&graph).unwrap_or_else(|e| panic!("resolve failed: {e:?}"));
        let world = resolved.world;
        let scoped = compute_universe(&world, &graph, &world.commands[0])
            .unwrap_or_else(|e| panic!("compute_universe failed: {e:?}"));
        (world, scoped)
    }

    #[test]
    fn ordered_no_children_is_not_skipped() {
        let (world, scoped) = pipeline("open util/ordering[S]\nsig S {}\nrun {} for 3");
        assert!(!ordered_abstract_partition(&world, &scoped));
    }

    #[test]
    fn ordered_abstract_nonexact_children_is_skipped() {
        // The T14d shape: abstract A, two non-exact children.
        let (world, scoped) = pipeline(
            "open util/ordering[A]\nabstract sig A {}\nsig B extends A {}\nsig C extends A {}\nrun {} for 4 A",
        );
        assert!(ordered_abstract_partition(&world, &scoped));
    }

    #[test]
    fn ordered_all_children_exact_is_not_skipped() {
        // T14c-style: every child exactly scoped → determinate population.
        let (world, scoped) = pipeline(
            "open util/ordering[A]\nabstract sig A {}\nsig B extends A {}\nsig C extends A {}\nrun {} for 3 A, exactly 2 B, exactly 1 C",
        );
        assert!(!ordered_abstract_partition(&world, &scoped));
    }

    #[test]
    fn no_ordering_is_not_skipped() {
        let (world, scoped) = pipeline("sig A {}\nsig B extends A {}\nrun {} for 3");
        assert!(!ordered_abstract_partition(&world, &scoped));
    }
}
