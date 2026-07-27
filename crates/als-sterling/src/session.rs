//! The seam between the wire and mettle's solver: what a provider session must
//! be able to answer.
//!
//! This crate deliberately knows nothing about `Ir`, instances, or the
//! evaluator. Those live in the CLI crate, where the solved artifacts and the
//! REPL machinery already are (`mettle::serve`), and reach the socket through
//! this one trait — so the protocol can be tested against a stub session with
//! no solver in the loop, and the session can be tested with no socket.

use crate::protocol::{Button, Datum, ProviderMeta};

/// The current instance, as the client should see it.
///
/// The [`Datum`] itself is assembled by the server (it owns `format` and the
/// enter/update join); the session owns everything that depends on what was
/// solved.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SessionDatum {
    /// A provider-assigned id, unique per instance shown. It **changes** every
    /// time the session advances — that is how a client tells that its
    /// evaluator is now pointed at a different instance.
    pub id: String,
    /// The generator that produced it: for mettle, the served command.
    pub generator_name: String,
    /// The Alloy instance XML (`format = "alloy"`).
    pub xml: String,
    /// The actions currently offered. Empty is a meaningful answer: an
    /// exhausted enumeration, or a temporal trace whose fork/init/config
    /// operators do not exist yet, offers nothing rather than offering a
    /// button that cannot work (ADR-0016 Decision 2).
    pub buttons: Vec<Button>,
}

impl SessionDatum {
    /// The wire [`Datum`] for this instance.
    #[must_use]
    pub fn to_datum(&self) -> Datum {
        Datum {
            generator_name: self.generator_name.clone(),
            id: self.id.clone(),
            // The only format that means "Alloy instance XML" to a Sterling
            // client (§2.3); `raw` would show the document as text.
            format: "alloy".to_owned(),
            data: self.xml.clone(),
            buttons: self.buttons.clone(),
            evaluator: true,
        }
    }
}

/// Why a `click` did not happen.
///
/// Carried to the client as an `error` message rather than swallowed: a button
/// that appears to do nothing is the failure mode this type exists to prevent.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ClickRefused {
    /// A stable machine-readable code the frontend can branch on.
    pub code: &'static str,
    /// One finished human-readable sentence.
    pub message: String,
}

impl ClickRefused {
    /// A verb this provider does not define at all.
    #[must_use]
    pub fn unknown(on_click: &str) -> Self {
        ClickRefused {
            code: "unknown-click",
            message: format!("`{on_click}` is not an action this provider defines."),
        }
    }
}

/// One `mettle serve` session: the solved command, and everything the four
/// protocol verbs can ask of it.
///
/// `&mut self` on [`eval`](ServeSession::eval) and
/// [`click`](ServeSession::click) is the honest signature — evaluating lowers
/// fresh nodes into the session's own arena, and a click advances the
/// enumeration. The server holds the session behind a mutex for exactly that
/// reason, so two browser tabs cannot interleave inside one solve.
pub trait ServeSession {
    /// The provider's self-description, for the `meta` verb.
    fn meta(&self) -> ProviderMeta;

    /// The instance to display right now, for the `data` verb.
    fn datum(&self) -> SessionDatum;

    /// Evaluates `expression` against the current instance, returning the text
    /// the evaluator pane should show. The protocol has exactly one result
    /// slot, so a rejected expression renders its diagnostic here — the same
    /// text the REPL would have printed.
    ///
    /// `datum_id` is the datum the client *thinks* it is asking about; a
    /// session that has moved on since is entitled to say so rather than
    /// answer about a different instance.
    fn eval(&mut self, datum_id: &str, expression: &str) -> String;

    /// Acts on a provider-defined action string.
    ///
    /// `state` is the client's displayed trace-state index
    /// ([`Click::state`](crate::protocol::Click::state), mt-075): `Some` from
    /// mettle's own frontend, whose stepper is the only thing that knows where
    /// in a lasso the user is looking, and `None` from any client that does not
    /// send it — for which the session falls back to the state its evaluator
    /// pane sits at. A verb that is not about a trace position ignores it.
    ///
    /// # Errors
    /// A [`ClickRefused`] when the verb is unknown, not yet implemented, or
    /// cannot be honoured right now (an exhausted enumeration, a state outside
    /// the displayed trace). `Ok` means the session advanced and the server
    /// should push the new datum.
    fn click(&mut self, on_click: &str, state: Option<usize>) -> Result<(), ClickRefused>;
}
