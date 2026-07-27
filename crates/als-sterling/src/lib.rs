//! **The `mettle serve` provider backend** (mt-072): the Sterling
//! data-provider protocol over WebSocket, plus the one-port HTTP server that
//! ships the frontend alongside it.
//!
//! The protocol is pinned in `docs/reference/sterling.md` §2 — an
//! **external-tool contract, never jar authority**. The reference jar contains
//! no Sterling code at all, so nothing in this crate is a conformance surface
//! and no divergence here is a conformance bug; divergences are measured
//! against that document and this crate's own spec (ADR-0016 Decision 2).
//!
//! # Layering
//!
//! - [`protocol`] — the wire types and the parse of one received frame. No I/O.
//! - [`session`] — [`ServeSession`], the one trait the socket asks questions
//!   through. This crate holds no solver state: the solved artifacts, the
//!   instance enumerator and the evaluator live in the CLI crate
//!   (`mettle::serve`), which implements this trait. That split is what lets
//!   the protocol be tested with no solver and the session with no socket.
//! - [`server`] — accept, route, upgrade, and the request/response loop.
//! - `handshake` (private) — the `Sec-WebSocket-Accept` derivation, hand-rolled
//!   so that `tungstenite` can be taken for framing alone (see its
//!   `Cargo.toml` justification).
//! - [`frontend`] — the placeholder page, until mt-075.
//!
//! # What the provider answers
//!
//! | verb | mettle's answer |
//! |---|---|
//! | `data` | the current instance as Alloy instance XML (mt-071's writer, jar-shape-exact), joined as `enter` plus an `update` retiring the previous datum |
//! | `eval` | the expression evaluated against that instance, rendered exactly as `mettle exec --repl` renders it |
//! | `click` | one of the enumeration verbs below |
//! | `meta` | name, evaluator availability, offered views, the served command |
//! | `ping` | `pong`, as a bare text frame (§2.1) |
//!
//! ## The `click` verbs
//!
//! Enumeration is not a protocol verb: §2.3's `Button.onClick` strings are
//! provider-defined, and the provider owns what they mean. mettle defines
//! five, named after the reference GUI's own exploration commands rather than
//! after Forge's `next`/`next-P`/`next-C` (mettle's frontend is the first-party
//! consumer, and self-describing beats terse):
//!
//! | `onClick` | meaning | today |
//! |---|---|---|
//! | [`CLICK_NEXT`] | the next distinct instance of a static command | implemented, via `als_core`'s `InstanceEnumerator` |
//! | [`CLICK_NEXT_TRACE`] | the next lasso trace, configuration held | typed refusal until mt-076 |
//! | [`CLICK_NEXT_CONFIG`] | the next trace with a different configuration | typed refusal until mt-076 |
//! | [`CLICK_NEW_INIT`] | re-solve from a different initial state (`fork(0)`) | typed refusal until mt-076 |
//! | [`CLICK_NEW_FORK`] | fork at the current state (`fork(current+1)`) | typed refusal until mt-076 |
//!
//! A temporal session offers **no buttons at all** while those four are
//! unimplemented (ADR-0016 Decision 2: absent, never a button that produces a
//! wrong trace) — but the verbs are still accepted on the wire, so a client
//! that sends one gets a sentence naming the bead rather than
//! "unknown action".

mod handshake;

pub mod frontend;
pub mod protocol;
pub mod server;
pub mod session;

pub use frontend::stub_index_html;
pub use protocol::{
    parse_request, Button, Click, DataJoin, Datum, DatumMeta, ErrorPayload, EvalExpression,
    EvalResult, ProtocolError, ProviderMeta, Request, Response, PING, PONG, PROTOCOL_VERSION,
};
pub use server::{Provider, ServeEvent, StaticAssets};
pub use session::{ClickRefused, ServeSession, SessionDatum};

/// The `onClick` string for "next instance" (static commands).
pub const CLICK_NEXT: &str = "next";

/// The `onClick` string for "next trace, same configuration" (mt-076).
pub const CLICK_NEXT_TRACE: &str = "next-trace";

/// The `onClick` string for "next trace, different configuration" (mt-076).
pub const CLICK_NEXT_CONFIG: &str = "next-config";

/// The `onClick` string for "new initial state" — `fork(0)` (mt-076).
pub const CLICK_NEW_INIT: &str = "new-init";

/// The `onClick` string for "fork at the current state" — `fork(current+1)`
/// (mt-076).
pub const CLICK_NEW_FORK: &str = "new-fork";

/// The four temporal exploration verbs, in the order a UI would show them.
/// Named here so the session that refuses them and the button set that
/// eventually offers them cannot drift apart.
pub const TEMPORAL_CLICKS: [&str; 4] = [
    CLICK_NEXT_TRACE,
    CLICK_NEXT_CONFIG,
    CLICK_NEW_INIT,
    CLICK_NEW_FORK,
];
