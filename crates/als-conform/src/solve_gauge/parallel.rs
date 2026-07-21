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
}
