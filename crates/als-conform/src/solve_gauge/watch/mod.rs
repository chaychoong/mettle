//! `conform watch` (mt-094): a live HTML dashboard over a `solve-gauge
//! --progress-jsonl` file.
//!
//! Two routes, `127.0.0.1`-only, hand-rolled on `std::net` — see
//! [`server`]'s module doc for why this does not depend on `als-sterling`
//! (STYLE P1/P2):
//! - `GET /` — the embedded dashboard page ([`server::PAGE`]).
//! - `GET /data` — the live JSON feed [`data::assemble`] builds by re-reading
//!   the JSONL file on every request and joining it against the run's
//!   [`super::sweep_baseline`] artifact for historical wall times.
//!
//! The dashboard can be started before the sweep it watches — `/data`
//! answers an honest "waiting for run" payload until the JSONL file has a
//! `run_start` event in it (see [`data::assemble`]).

mod data;
mod server;

pub use server::WatchServer;
