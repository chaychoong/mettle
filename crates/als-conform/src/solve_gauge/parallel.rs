//! Deterministic parallel fan-out (mt-054 (a)).
//!
//! [`parallel_fold`] runs `work` over `items` on up to `jobs` scoped worker
//! threads and returns a `Vec<Option<R>>` indexed by the item's position — so
//! the caller folds results in a fixed order (sorted-item order), never in
//! completion order (STYLE D5). Workers never outlive the call ([`std::thread::scope`]);
//! a worker always runs its item to completion before checking the stop flag
//! (the mt-039 no-abandoned-work rule).
//!
//! Progress is streamed back over an `mpsc` channel and replayed on the *calling*
//! thread, so the caller's `&mut dyn FnMut(&str)` progress sink stays
//! single-threaded and needs no `Send`/`Sync` bound — the library stays
//! render-free (STYLE E3), the bin composes stderr + status there.
//!
//! **Fail-fast:** when `fail_fast` is set, the first completed result for which
//! `trigger` returns `Some` stops *dispatch* of new items (in-flight items still
//! finish and fold), and the trigger string is returned. A fail-fast partial run
//! is therefore not byte-stable across job counts; a full run is (every item is
//! dispatched and folded in position order regardless of `jobs`).
//!
//! **Scheduling vs. folding (mt-057 item 2).** [`lpt_order`] computes a
//! longest-processing-time-first dispatch permutation from recorded costs, and
//! [`parallel_fold_ordered`] dispatches in that order while returning results
//! indexed by the item's **original** position. Execution order therefore has no
//! way to reach the caller's fold, which is what makes reordering provably
//! byte-neutral (STYLE D1/D5).

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::mpsc;
use std::thread;

/// A worker→coordinator message: a transient progress line, or a finished item.
enum Msg<R> {
    Progress(String),
    Done(usize, R),
}

/// Runs `work` over `items` across `jobs` scoped threads, folding results into a
/// position-indexed `Vec`. Returns `(results, fail_fast_trigger)`.
///
/// - `progress` and `on_result` run only on the calling thread (no `Send` bound).
/// - `on_result(i, &r)` fires as each item completes (e.g. an incremental
///   interruption-safe write); it sees completion order, so it must not depend
///   on order for correctness.
/// - `label(&item)` names the item in the `[k/N]` progress line.
/// - `work(&item, &mut send)` runs on a worker; `send` streams heartbeat lines.
/// - `trigger(&r)` (fail-fast only) decides whether a result stops dispatch.
#[allow(clippy::too_many_arguments, reason = "one cohesive fan-out primitive")]
pub(crate) fn parallel_fold<T, R>(
    items: &[T],
    jobs: usize,
    fail_fast: bool,
    progress: &mut dyn FnMut(&str),
    label: impl Fn(&T) -> String,
    on_result: &mut dyn FnMut(usize, &R),
    work: impl Fn(&T, &mut dyn FnMut(&str)) -> R + Sync,
    trigger: impl Fn(&R) -> Option<String>,
) -> (Vec<Option<R>>, Option<String>)
where
    T: Sync,
    R: Send,
{
    let n = items.len();
    let mut results: Vec<Option<R>> = Vec::with_capacity(n);
    results.resize_with(n, || None);
    let mut trig: Option<String> = None;

    let next = AtomicUsize::new(0);
    let stop = AtomicBool::new(false);
    let jobs = jobs.max(1);
    let work = &work;
    let next = &next;
    let stop = &stop;

    thread::scope(|scope| {
        let (tx, rx) = mpsc::channel::<Msg<R>>();
        for _ in 0..jobs {
            let tx = tx.clone();
            scope.spawn(move || loop {
                // Only *new* dispatch is gated by the stop flag; an item already
                // fetched always runs to completion (mt-039: no abandoned work).
                if fail_fast && stop.load(Ordering::Acquire) {
                    break;
                }
                let i = next.fetch_add(1, Ordering::Relaxed);
                if i >= n {
                    break;
                }
                let mut send = |line: &str| {
                    let _ = tx.send(Msg::Progress(line.to_owned()));
                };
                let r = work(&items[i], &mut send);
                let _ = tx.send(Msg::Done(i, r));
            });
        }
        drop(tx); // so `rx` closes once every worker has finished

        let mut completed = 0usize;
        while let Ok(msg) = rx.recv() {
            match msg {
                Msg::Progress(line) => progress(&line),
                Msg::Done(i, r) => {
                    completed += 1;
                    progress(&format!("[{completed}/{n}] {}", label(&items[i])));
                    on_result(i, &r);
                    if fail_fast && trig.is_none() {
                        if let Some(t) = trigger(&r) {
                            trig = Some(t);
                            stop.store(true, Ordering::Release);
                        }
                    }
                    results[i] = Some(r);
                }
            }
        }
    });

    (results, trig)
}

/// The longest-processing-time-first dispatch permutation over `items`.
///
/// Returns positions into `items`, most expensive first, so the tail starts
/// instead of finishing last (classic LPT list scheduling). An item with **no
/// recorded cost sorts first**, ahead of every measured item: an unmeasured item
/// is one whose runtime we cannot bound at all — usually new or just-edited —
/// so treating it as `+inf` is the choice that minimizes the risk of it becoming
/// the straggler. Ties (including all-unknown) break on the original position,
/// so the permutation is a total order and identical run to run.
pub(crate) fn lpt_order<T>(items: &[T], cost: impl Fn(&T) -> Option<u64>) -> Vec<usize> {
    let mut order: Vec<usize> = (0..items.len()).collect();
    // `None` → `u64::MAX` puts unknowns first under the descending sort.
    let key = |i: &usize| cost(&items[*i]).unwrap_or(u64::MAX);
    order.sort_by(|a, b| key(b).cmp(&key(a)).then_with(|| a.cmp(b)));
    order
}

/// [`parallel_fold`], but dispatching `items` in `order` while returning results
/// indexed by each item's **original** position.
///
/// This is the whole reason LPT cannot move a byte: the caller still folds
/// `results[0..n]` in position order, exactly as if nothing had been reordered.
/// `on_result` likewise receives original positions.
#[allow(clippy::too_many_arguments, reason = "one cohesive fan-out primitive")]
pub(crate) fn parallel_fold_ordered<T, R>(
    items: &[T],
    order: &[usize],
    jobs: usize,
    fail_fast: bool,
    progress: &mut dyn FnMut(&str),
    label: impl Fn(&T) -> String,
    on_result: &mut dyn FnMut(usize, &R),
    work: impl Fn(&T, &mut dyn FnMut(&str)) -> R + Sync,
    trigger: impl Fn(&R) -> Option<String>,
) -> (Vec<Option<R>>, Option<String>)
where
    T: Sync,
    R: Send,
{
    debug_assert_eq!(
        order.len(),
        items.len(),
        "dispatch order must be a permutation of the items"
    );
    let scheduled: Vec<&T> = order.iter().map(|&i| &items[i]).collect();
    let mut on_scheduled = |slot: usize, r: &R| on_result(order[slot], r);
    let (by_slot, trig) = parallel_fold(
        &scheduled,
        jobs,
        fail_fast,
        progress,
        |t: &&T| label(t),
        &mut on_scheduled,
        |t: &&T, send: &mut dyn FnMut(&str)| work(t, send),
        trigger,
    );

    // Invert the permutation: slot `j` carried the item at original position
    // `order[j]`.
    let mut by_position: Vec<Option<R>> = Vec::with_capacity(items.len());
    by_position.resize_with(items.len(), || None);
    for (slot, r) in by_slot.into_iter().enumerate() {
        by_position[order[slot]] = r;
    }
    (by_position, trig)
}

#[cfg(test)]
#[allow(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "test fixtures assert on known-good values"
)]
mod tests {
    use super::*;

    #[test]
    fn folds_in_position_order_at_any_job_count() {
        let items: Vec<usize> = (0..50).collect();
        let seq = |jobs| {
            let mut noop = |_: usize, _: &usize| {};
            let (results, trig) = parallel_fold(
                &items,
                jobs,
                false,
                &mut |_| {},
                ToString::to_string,
                &mut noop,
                |t, _send| t * t,
                |_| None,
            );
            assert!(trig.is_none());
            results.into_iter().map(Option::unwrap).collect::<Vec<_>>()
        };
        let one = seq(1);
        assert_eq!(one, seq(4));
        assert_eq!(one, seq(8));
        assert_eq!(one, (0..50).map(|i| i * i).collect::<Vec<_>>());
    }

    #[test]
    fn fail_fast_stops_dispatch_and_reports_trigger() {
        let items: Vec<usize> = (0..2000).collect();
        let mut noop = |_: usize, _: &usize| {};
        let (results, trig) = parallel_fold(
            &items,
            4,
            true,
            &mut |_| {},
            ToString::to_string,
            &mut noop,
            // A small per-item cost so the coordinator observes the trigger and
            // sets the stop flag well before all 2000 items are dispatched.
            |t, _send| {
                std::thread::sleep(std::time::Duration::from_micros(200));
                *t
            },
            |r| (*r == 3).then(|| format!("hit {r}")),
        );
        assert_eq!(trig.as_deref(), Some("hit 3"));
        // Dispatch stops after the trigger fires: not every item runs (partial).
        assert!(results.iter().filter(|r| r.is_some()).count() < 2000);
    }

    #[test]
    fn lpt_puts_unknowns_first_then_descending_cost() {
        // (name, recorded cost): "a"/"d" tie at 10, "b"/"e" are both unknown.
        let items = [
            ("a", Some(10)),
            ("b", None),
            ("c", Some(500)),
            ("d", Some(10)),
            ("e", None),
        ];
        // Unknowns (b, e) first in original order, then 500, then the 10-tie in
        // original order.
        assert_eq!(lpt_order(&items, |t| t.1), vec![1, 4, 2, 0, 3]);
    }

    #[test]
    fn lpt_order_is_a_permutation_and_stable() {
        let items: Vec<u64> = (0..64).collect();
        // Deliberately degenerate costs: all equal → the original order.
        assert_eq!(lpt_order(&items, |_| Some(7)), (0..64).collect::<Vec<_>>());
        // And identical across calls with a mixed cost function.
        let cost = |t: &u64| (!t.is_multiple_of(3)).then_some((*t * 37) % 101);
        assert_eq!(lpt_order(&items, cost), lpt_order(&items, cost));
        let mut sorted = lpt_order(&items, cost);
        sorted.sort_unstable();
        assert_eq!(sorted, (0..64).collect::<Vec<_>>());
    }

    /// The determinism gate for mt-057 item 2: reordering dispatch must not move
    /// a single folded byte, at any job count.
    #[test]
    fn dispatch_order_never_changes_the_folded_result() {
        let items: Vec<u64> = (0..64).collect();
        let run = |order: &[usize], jobs: usize| {
            let mut seen: Vec<usize> = Vec::new();
            let mut on_result = |i: usize, _: &String| seen.push(i);
            let (results, trig) = parallel_fold_ordered(
                &items,
                order,
                jobs,
                false,
                &mut |_| {},
                ToString::to_string,
                &mut on_result,
                |t: &u64, _send: &mut dyn FnMut(&str)| format!("item-{t}"),
                |_| None,
            );
            assert!(trig.is_none());
            // Every original position is reported back exactly once.
            let mut sorted = seen;
            sorted.sort_unstable();
            assert_eq!(sorted, (0..64).collect::<Vec<_>>());
            results
                .into_iter()
                .map(Option::unwrap)
                .collect::<Vec<String>>()
        };

        let identity: Vec<usize> = (0..64).collect();
        let expected = run(&identity, 1);
        assert_eq!(expected[0], "item-0");
        assert_eq!(expected[63], "item-63");

        // A reversed schedule, an LPT schedule, and a pathological one all fold
        // to the same position-ordered vector, at 1, 4 and 8 workers.
        let reversed: Vec<usize> = (0..64).rev().collect();
        let lpt = lpt_order(&items, |t| (!t.is_multiple_of(5)).then_some(64 - *t));
        for order in [&identity, &reversed, &lpt] {
            for jobs in [1, 4, 8] {
                assert_eq!(run(order, jobs), expected, "order/jobs must not matter");
            }
        }
    }
}
