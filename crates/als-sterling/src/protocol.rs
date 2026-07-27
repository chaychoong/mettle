//! The wire types of the Sterling data-provider protocol
//! (`docs/reference/sterling.md` §2), and the parse of one received text frame.
//!
//! The envelope is `{type, version, payload?}` JSON, sent as WebSocket **text**
//! frames, with the literal strings `"ping"`/`"pong"` riding the same socket
//! outside the JSON layer entirely (§2.1). Field names are the TypeScript
//! source's, verbatim — `#[serde(rename_all = "camelCase")]` where they differ
//! from Rust's, spelled out per-field where only one differs — so this module
//! is the single place mettle states the contract.
//!
//! **One deliberate extension.** §2.2's four message types give a provider no
//! way to say "I could not do that": a refused `click` or an unparseable frame
//! would otherwise have to be answered with silence or a dropped connection,
//! and mettle does neither (STYLE E5). [`OUTGOING_ERROR`] is a fifth,
//! mettle-defined outgoing type carrying a typed [`ErrorPayload`]. It is safe
//! for the upstream client too: `sterling-connection`'s `onMessage` dispatches
//! on exactly `data`/`eval`/`meta` and silently ignores anything else
//! (verified against `receive/onMessage.ts`), so an external Sterling sees a
//! no-op where mettle's own frontend sees a diagnosable failure.

use serde::{Deserialize, Serialize};

/// The `version` field every message carries. There is no negotiation
/// handshake anywhere in the protocol — both the TypeScript client and Forge's
/// provider hardcode `1` (§2.2) — so mettle sends `1` and does not police what
/// it receives: rejecting an unknown version would invent a compatibility rule
/// the contract does not have.
pub const PROTOCOL_VERSION: u32 = 1;

/// The keepalive request the client sends every 3s, as a bare text frame.
pub const PING: &str = "ping";

/// The keepalive answer, likewise bare (§2.1).
pub const PONG: &str = "pong";

/// The `type` of mettle's own error message (see the module docs).
pub const OUTGOING_ERROR: &str = "error";

/// One decoded client → provider message.
///
/// The four protocol verbs plus the bare keepalive. Anything else is a
/// [`ProtocolError`], never a silently dropped frame.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Request {
    /// `"ping"` — answer with [`PONG`].
    Ping,
    /// `data` with no payload: send the current instance.
    Data,
    /// `click` — a provider-defined action string (§2.3).
    Click(Click),
    /// `eval` — an expression to evaluate against a datum.
    Eval(EvalExpression),
    /// `meta` with no payload: describe the provider.
    Meta,
}

/// Why a received frame is not a [`Request`].
///
/// Each variant is answerable: the server turns it into an [`ErrorPayload`]
/// and replies, so a malformed client never gets silence (STYLE E1/E5).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ProtocolError {
    /// The frame was not JSON, or not a `{type, version, payload?}` object.
    Malformed(String),
    /// A well-formed envelope whose `type` is none of the four verbs.
    UnknownType(String),
    /// A verb that requires a payload (`click`, `eval`) arrived without a
    /// usable one.
    BadPayload {
        /// The message type whose payload did not decode.
        message_type: String,
        /// serde's account of what was wrong.
        detail: String,
    },
}

impl ProtocolError {
    /// The stable machine-readable code the wire carries.
    #[must_use]
    pub fn code(&self) -> &'static str {
        match self {
            ProtocolError::Malformed(_) => "malformed-message",
            ProtocolError::UnknownType(_) => "unknown-message-type",
            ProtocolError::BadPayload { .. } => "bad-payload",
        }
    }
}

impl std::fmt::Display for ProtocolError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProtocolError::Malformed(detail) => {
                write!(f, "not a Sterling protocol message: {detail}")
            }
            ProtocolError::UnknownType(ty) => write!(
                f,
                "unknown message type `{ty}`; expected one of data, click, eval, meta"
            ),
            ProtocolError::BadPayload {
                message_type,
                detail,
            } => write!(
                f,
                "`{message_type}` message has no usable payload: {detail}"
            ),
        }
    }
}

impl std::error::Error for ProtocolError {}

/// The raw envelope, before the payload is interpreted.
///
/// `payload` stays a [`serde_json::Value`] through this step on purpose: the
/// payload's shape depends on `type`, and decoding it eagerly would turn a
/// wrong-shaped `click` into "this is not a message at all".
#[derive(Deserialize, Debug)]
struct Envelope {
    #[serde(rename = "type")]
    message_type: String,
    #[serde(default)]
    payload: Option<serde_json::Value>,
}

/// Decodes one received text frame.
///
/// # Errors
/// A [`ProtocolError`] for anything that is not one of the five recognized
/// shapes; the caller answers it on the wire rather than closing the socket.
pub fn parse_request(frame: &str) -> Result<Request, ProtocolError> {
    if frame.trim() == PING {
        return Ok(Request::Ping);
    }
    let envelope: Envelope =
        serde_json::from_str(frame).map_err(|e| ProtocolError::Malformed(e.to_string()))?;
    let payload = |message_type: &str| -> Result<serde_json::Value, ProtocolError> {
        envelope
            .payload
            .clone()
            .ok_or_else(|| ProtocolError::BadPayload {
                message_type: message_type.to_owned(),
                detail: "the `payload` field is missing".to_owned(),
            })
    };
    match envelope.message_type.as_str() {
        // `data` and `meta` are sent payload-less by the client
        // (`newSendDataMsg`/`newSendMetaMsg` omit the field); a payload that
        // arrives anyway is ignored, not rejected — there is nothing it could
        // mean.
        "data" => Ok(Request::Data),
        "meta" => Ok(Request::Meta),
        "click" => Ok(Request::Click(decode("click", payload("click")?)?)),
        "eval" => Ok(Request::Eval(decode("eval", payload("eval")?)?)),
        other => Err(ProtocolError::UnknownType(other.to_owned())),
    }
}

/// Decodes one verb's payload, naming the verb in the failure.
fn decode<T: serde::de::DeserializeOwned>(
    message_type: &str,
    value: serde_json::Value,
) -> Result<T, ProtocolError> {
    serde_json::from_value(value).map_err(|e| ProtocolError::BadPayload {
        message_type: message_type.to_owned(),
        detail: e.to_string(),
    })
}

/// A provider → client message, ready to serialize.
///
/// Modeled as one enum with an internally-tagged `type` so that the envelope
/// can never disagree with the payload it carries.
#[derive(Serialize, Clone, PartialEq, Eq, Debug)]
#[serde(tag = "type")]
pub enum Response {
    /// The instance data join (§2.2).
    #[serde(rename = "data")]
    Data {
        /// Always [`PROTOCOL_VERSION`].
        version: u32,
        /// The datums entering, updating and leaving the display.
        payload: DataJoin,
    },
    /// One evaluated expression's result.
    #[serde(rename = "eval")]
    Eval {
        /// Always [`PROTOCOL_VERSION`].
        version: u32,
        /// The result, keyed by the request's own id.
        payload: EvalResult,
    },
    /// The provider's self-description.
    #[serde(rename = "meta")]
    Meta {
        /// Always [`PROTOCOL_VERSION`].
        version: u32,
        /// What this provider supports.
        payload: ProviderMeta,
    },
    /// mettle's extension (see the module docs): a typed refusal.
    #[serde(rename = "error")]
    Error {
        /// Always [`PROTOCOL_VERSION`].
        version: u32,
        /// What went wrong, and what the client can do about it.
        payload: ErrorPayload,
    },
}

impl Response {
    /// A `data` response carrying one join.
    #[must_use]
    pub fn data(payload: DataJoin) -> Self {
        Response::Data {
            version: PROTOCOL_VERSION,
            payload,
        }
    }

    /// An `eval` response for the expression id `id`.
    #[must_use]
    pub fn eval(id: String, result: String) -> Self {
        Response::Eval {
            version: PROTOCOL_VERSION,
            payload: EvalResult { id, result },
        }
    }

    /// A `meta` response.
    #[must_use]
    pub fn meta(payload: ProviderMeta) -> Self {
        Response::Meta {
            version: PROTOCOL_VERSION,
            payload,
        }
    }

    /// An `error` response.
    #[must_use]
    pub fn error(code: impl Into<String>, message: impl Into<String>) -> Self {
        Response::Error {
            version: PROTOCOL_VERSION,
            payload: ErrorPayload {
                code: code.into(),
                message: message.into(),
            },
        }
    }

    /// The message as the text frame that goes on the wire.
    ///
    /// Infallible by construction: every field below is a `String`, a number,
    /// or a `Vec`/`Option` of those, and `serde_json` only fails on a
    /// serializer error (a non-string map key, a `NaN`) that none of them can
    /// produce.
    #[must_use]
    pub fn to_frame(&self) -> String {
        serde_json::to_string(self).unwrap_or_else(|_| {
            unreachable!("every Response field serializes infallibly (no map keys, no floats)")
        })
    }
}

/// The `click` payload (§2.3): the button's opaque action string, plus the
/// datum it was attached to.
#[derive(Serialize, Deserialize, Clone, PartialEq, Eq, Debug)]
#[serde(rename_all = "camelCase")]
pub struct Click {
    /// The datum whose button was clicked. Optional in the TypeScript type —
    /// "not all buttons will necessarily be clicked before an active datum is
    /// present."
    #[serde(default)]
    pub id: Option<String>,
    /// The provider-defined action string, echoed back verbatim.
    pub on_click: String,
    /// Optional provider-defined context. Carried through untouched; mettle
    /// defines no context today.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub context: Option<serde_json::Value>,
}

/// The `eval` request payload (§5).
#[derive(Serialize, Deserialize, Clone, PartialEq, Eq, Debug)]
#[serde(rename_all = "camelCase")]
pub struct EvalExpression {
    /// The client's id for this expression; echoed in the result.
    pub id: String,
    /// The datum the expression is asked about.
    pub datum_id: String,
    /// The expression text, opaque on the wire.
    pub expression: String,
}

/// The `eval` response payload (§5) — both fields opaque strings.
#[derive(Serialize, Deserialize, Clone, PartialEq, Eq, Debug)]
pub struct EvalResult {
    /// The id of the [`EvalExpression`] this answers.
    pub id: String,
    /// The rendered result (or the rendered error — the protocol has one slot).
    pub result: String,
}

/// The `data` payload: a D3-style join over the displayed datums (§2.2).
#[derive(Serialize, Deserialize, Clone, PartialEq, Eq, Debug, Default)]
pub struct DataJoin {
    /// Datums entering the display.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub enter: Vec<Datum>,
    /// Metadata updates to datums already displayed.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub update: Vec<DatumMeta>,
    /// Ids of datums leaving the display.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub exit: Vec<String>,
}

/// One displayable datum (§2.3).
#[derive(Serialize, Deserialize, Clone, PartialEq, Eq, Debug)]
#[serde(rename_all = "camelCase")]
pub struct Datum {
    /// The provider's name for the generator that produced this datum — for
    /// mettle, the command being served.
    pub generator_name: String,
    /// A provider-assigned unique id.
    pub id: String,
    /// `"alloy"` (parsed as Alloy instance XML) or `"raw"`; the client drops
    /// anything else (§2.3).
    pub format: String,
    /// The raw payload — Alloy instance XML for `format = "alloy"`.
    pub data: String,
    /// Provider-defined action buttons.
    #[serde(default)]
    pub buttons: Vec<Button>,
    /// Whether this datum supports the evaluator pane.
    pub evaluator: bool,
}

/// A [`Datum`] without its data — the shape an `update` entry takes
/// (`DatumMeta = Omit<Datum, 'data' | 'format'>`).
#[derive(Serialize, Deserialize, Clone, PartialEq, Eq, Debug)]
#[serde(rename_all = "camelCase")]
pub struct DatumMeta {
    /// The datum being updated.
    pub id: String,
    /// Unchanged, but part of the type.
    pub generator_name: String,
    /// The datum's buttons after the update (empty = no actions left).
    #[serde(default)]
    pub buttons: Vec<Button>,
    /// Whether the datum still supports the evaluator.
    pub evaluator: bool,
}

/// An action button the client renders next to a datum (§2.3).
#[derive(Serialize, Deserialize, Clone, PartialEq, Eq, Debug)]
pub struct Button {
    /// The label.
    pub text: String,
    /// The opaque string sent back in the [`Click`] payload.
    #[serde(rename = "onClick")]
    pub on_click: String,
    /// Tooltip text.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub mouseover: Option<String>,
}

/// The provider's self-description (§2.2).
///
/// `evaluator` is a **boolean** here. The upstream TypeScript type declares it
/// `string`, while its own `JSDoc` ("whether the provider supports a REPL") and
/// its only known producer (Forge, which sends `#t`) both say boolean —
/// sterling.md §10 flags that as an upstream inconsistency, not something for
/// mettle to resolve. Following the two agreeing witnesses over the one
/// disagreeing type annotation is the conservative read.
#[derive(Serialize, Deserialize, Clone, PartialEq, Eq, Debug)]
pub struct ProviderMeta {
    /// The provider's name.
    pub name: String,
    /// Whether an evaluator pane is available.
    pub evaluator: bool,
    /// The views the provider wants offered (`graph`/`table`/`script`/`edit`).
    pub views: Vec<String>,
    /// The instance generators available — for mettle, the served command.
    pub generators: Vec<String>,
}

/// mettle's extension payload: a refusal the client can render and act on.
#[derive(Serialize, Deserialize, Clone, PartialEq, Eq, Debug)]
pub struct ErrorPayload {
    /// A stable machine-readable code (`unknown-click`, `not-yet-supported`,
    /// `malformed-message`, …).
    pub code: String,
    /// One human-readable sentence, already final — the client displays it.
    pub message: String,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_the_bare_keepalive() {
        assert_eq!(parse_request("ping"), Ok(Request::Ping));
        // The client sends it unadorned; tolerating surrounding whitespace
        // costs nothing and a bare `"ping"` JSON string is still not a message.
        assert_eq!(parse_request(" ping\n"), Ok(Request::Ping));
        assert!(matches!(
            parse_request("\"ping\""),
            Err(ProtocolError::Malformed(_))
        ));
    }

    #[test]
    fn parses_the_payload_less_verbs() {
        assert_eq!(
            parse_request(r#"{"type":"data","version":1}"#),
            Ok(Request::Data)
        );
        assert_eq!(
            parse_request(r#"{"type":"meta","version":1}"#),
            Ok(Request::Meta)
        );
    }

    #[test]
    fn parses_click_and_eval_payloads() {
        assert_eq!(
            parse_request(r#"{"type":"click","version":1,"payload":{"id":"d0","onClick":"next"}}"#),
            Ok(Request::Click(Click {
                id: Some("d0".to_owned()),
                on_click: "next".to_owned(),
                context: None,
            }))
        );
        // `id` is optional in the upstream type, so a click with no active
        // datum still parses.
        assert_eq!(
            parse_request(r#"{"type":"click","version":1,"payload":{"onClick":"next"}}"#),
            Ok(Request::Click(Click {
                id: None,
                on_click: "next".to_owned(),
                context: None,
            }))
        );
        assert_eq!(
            parse_request(
                r##"{"type":"eval","version":1,"payload":{"id":"e1","datumId":"d0","expression":"#A"}}"##
            ),
            Ok(Request::Eval(EvalExpression {
                id: "e1".to_owned(),
                datum_id: "d0".to_owned(),
                expression: "#A".to_owned(),
            }))
        );
    }

    #[test]
    fn every_malformed_shape_is_a_typed_error_not_a_panic() {
        assert!(matches!(
            parse_request("{not json"),
            Err(ProtocolError::Malformed(_))
        ));
        assert!(matches!(
            parse_request("[1,2,3]"),
            Err(ProtocolError::Malformed(_))
        ));
        assert!(matches!(
            parse_request(r#"{"version":1}"#),
            Err(ProtocolError::Malformed(_)),
        ));
        assert!(matches!(
            parse_request(r#"{"type":"nonsense","version":1}"#),
            Err(ProtocolError::UnknownType(t)) if t == "nonsense"
        ));
        assert!(matches!(
            parse_request(r#"{"type":"click","version":1}"#),
            Err(ProtocolError::BadPayload { .. })
        ));
        assert!(matches!(
            parse_request(r#"{"type":"eval","version":1,"payload":{"id":"e1"}}"#),
            Err(ProtocolError::BadPayload { .. })
        ));
        // An unexpected `version` is not policed: there is no negotiation in
        // the protocol to police it against.
        assert_eq!(
            parse_request(r#"{"type":"data","version":99}"#),
            Ok(Request::Data)
        );
    }

    #[test]
    fn every_error_shape_has_a_stable_code_and_a_sentence() {
        for err in [
            ProtocolError::Malformed("eof".to_owned()),
            ProtocolError::UnknownType("x".to_owned()),
            ProtocolError::BadPayload {
                message_type: "click".to_owned(),
                detail: "missing field".to_owned(),
            },
        ] {
            assert!(!err.code().is_empty());
            assert!(err.to_string().len() > err.code().len());
        }
    }

    fn a_datum() -> Datum {
        Datum {
            generator_name: "run p".to_owned(),
            id: "mettle:0".to_owned(),
            format: "alloy".to_owned(),
            data: "<alloy/>".to_owned(),
            buttons: vec![Button {
                text: "Next".to_owned(),
                on_click: "next".to_owned(),
                mouseover: Some("(Get the next instance)".to_owned()),
            }],
            evaluator: true,
        }
    }

    #[test]
    fn data_response_carries_the_upstream_field_names() {
        let frame = Response::data(DataJoin {
            enter: vec![a_datum()],
            update: vec![DatumMeta {
                id: "mettle:0".to_owned(),
                generator_name: "run p".to_owned(),
                buttons: Vec::new(),
                evaluator: false,
            }],
            exit: Vec::new(),
        })
        .to_frame();
        let value: serde_json::Value = serde_json::from_str(&frame).expect("valid JSON");
        assert_eq!(value["type"], "data");
        assert_eq!(value["version"], 1);
        assert_eq!(value["payload"]["enter"][0]["generatorName"], "run p");
        assert_eq!(value["payload"]["enter"][0]["format"], "alloy");
        assert_eq!(
            value["payload"]["enter"][0]["buttons"][0]["onClick"],
            "next"
        );
        assert_eq!(value["payload"]["enter"][0]["evaluator"], true);
        assert_eq!(value["payload"]["update"][0]["evaluator"], false);
        // An empty `exit` is omitted rather than sent as `[]` — the client
        // treats a missing key and an empty array identically, and the
        // upstream client's own senders omit absent fields.
        assert!(value["payload"].get("exit").is_none());
    }

    #[test]
    fn every_response_round_trips_through_its_own_field_names() {
        let responses = [
            Response::data(DataJoin {
                enter: vec![a_datum()],
                ..DataJoin::default()
            }),
            Response::eval("e1".to_owned(), "{A$0}".to_owned()),
            Response::meta(ProviderMeta {
                name: "mettle".to_owned(),
                evaluator: true,
                views: vec!["graph".to_owned(), "table".to_owned()],
                generators: vec!["[0] run p".to_owned()],
            }),
            Response::error("unknown-click", "no such action"),
        ];
        for response in responses {
            let frame = response.to_frame();
            let value: serde_json::Value = serde_json::from_str(&frame).expect("valid JSON");
            if matches!(response, Response::Error { .. }) {
                // The serde rename and the documented constant are the same
                // string, and this is what keeps them so.
                assert_eq!(value["type"], OUTGOING_ERROR, "{frame}");
            }
            assert_eq!(value["version"], 1, "{frame}");
            assert!(value["type"].is_string(), "{frame}");
            assert!(value["payload"].is_object(), "{frame}");
            // The payload decodes back into the same Rust value it came from:
            // the rename attributes are the contract, so a typo in one would
            // show up here as a failed round trip.
            match &response {
                Response::Data { payload, .. } => {
                    let back: DataJoin =
                        serde_json::from_value(value["payload"].clone()).expect("DataJoin");
                    assert_eq!(&back, payload);
                }
                Response::Eval { payload, .. } => {
                    let back: EvalResult =
                        serde_json::from_value(value["payload"].clone()).expect("EvalResult");
                    assert_eq!(&back, payload);
                }
                Response::Meta { payload, .. } => {
                    let back: ProviderMeta =
                        serde_json::from_value(value["payload"].clone()).expect("ProviderMeta");
                    assert_eq!(&back, payload);
                }
                Response::Error { payload, .. } => {
                    let back: ErrorPayload =
                        serde_json::from_value(value["payload"].clone()).expect("ErrorPayload");
                    assert_eq!(&back, payload);
                }
            }
        }
    }

    #[test]
    fn a_click_request_round_trips_through_the_wire_spelling() {
        let click = Click {
            id: Some("mettle:2".to_owned()),
            on_click: "next".to_owned(),
            context: None,
        };
        let frame = format!(
            r#"{{"type":"click","version":1,"payload":{}}}"#,
            serde_json::to_string(&click).expect("serializes")
        );
        assert_eq!(parse_request(&frame), Ok(Request::Click(click)));
    }
}
