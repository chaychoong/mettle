//! The protocol as it actually behaves **on a socket** (mt-072).
//!
//! The session here is a stub: no solver, no evaluator, no XML — those are
//! covered end to end against the real binary in `crates/mettle/tests/serve.rs`.
//! What this file pins is everything between the TCP accept and the
//! [`ServeSession`] call: the HTTP routing, the WebSocket handshake and
//! framing, the request/response pairing, and — the point of the exercise —
//! that no malformed client input can panic the server, close the socket
//! without a word, or produce silence.
//!
//! Every listener binds port 0, so the tests never collide with each other or
//! with a developer's running `mettle serve`.

use std::io::{BufRead as _, BufReader, Read as _, Write as _};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::sync::Mutex;

use als_sterling::protocol::{DataJoin, ErrorPayload, EvalResult, ProviderMeta};
use als_sterling::{
    Button, ClickRefused, Provider, ServeEvent, ServeSession, SessionDatum, StaticAssets,
    CLICK_NEW_FORK, CLICK_NEXT, CLICK_NEXT_TRACE,
};
use tungstenite::{Message, WebSocket};

const INDEX_HTML: &str = "<!doctype html><title>stub</title>";

/// A session with no solver behind it: an index that a `next` click advances,
/// and an evaluator that echoes.
#[derive(Default, Debug)]
struct StubSession {
    index: usize,
    /// Set once the enumeration is declared exhausted, to exercise the
    /// refusal path that a real exhausted enumerator takes.
    exhausted: bool,
}

impl ServeSession for StubSession {
    fn meta(&self) -> ProviderMeta {
        ProviderMeta {
            name: "mettle".to_owned(),
            evaluator: true,
            views: vec!["graph".to_owned(), "table".to_owned()],
            generators: vec!["[0] run p".to_owned()],
        }
    }

    fn datum(&self) -> SessionDatum {
        SessionDatum {
            id: format!("stub:{}", self.index),
            generator_name: "[0] run p".to_owned(),
            xml: format!("<alloy><instance n=\"{}\"/></alloy>", self.index),
            buttons: vec![Button {
                text: "Next".to_owned(),
                on_click: CLICK_NEXT.to_owned(),
                mouseover: None,
            }],
        }
    }

    fn eval(&mut self, datum_id: &str, expression: &str) -> String {
        format!("{datum_id}|{expression}|{}", self.index)
    }

    fn click(&mut self, on_click: &str, state: Option<usize>) -> Result<(), ClickRefused> {
        match on_click {
            // Stands in for a real fork: the point here is only that the
            // client's displayed state (mt-075's optional `click.state`)
            // reaches the session intact, and that its absence is a *different*
            // value from any state a client could send.
            CLICK_NEW_FORK => {
                self.index = state.map_or(900, |state| state + 1);
                Ok(())
            }
            CLICK_NEXT if self.exhausted => Err(ClickRefused {
                code: "no-more-instances",
                message: "no more".to_owned(),
            }),
            CLICK_NEXT => {
                self.index += 1;
                if self.index == 2 {
                    self.exhausted = true;
                }
                Ok(())
            }
            // A stub, so this refusal stands in for any provider-defined
            // refusal — what the wire test cares about is that the code and
            // message survive the round trip, not which verb produced them.
            CLICK_NEXT_TRACE => Err(ClickRefused {
                code: "no-more-instances",
                message: "this stub has exactly one trace.".to_owned(),
            }),
            other => Err(ClickRefused::unknown(other)),
        }
    }
}

/// Runs a provider over `connections` accepted connections while `body` drives
/// it as a client, then joins.
fn on_wire(connections: usize, body: impl FnOnce(SocketAddr)) {
    let session = Mutex::new(StubSession::default());
    let mut assets = StaticAssets::default();
    assets.add(
        "/",
        "text/html; charset=utf-8",
        INDEX_HTML.as_bytes().to_vec(),
    );
    let report = |_: &ServeEvent<'_>| {};
    let provider = Provider::new(&assets, &session, &report);
    let listener = TcpListener::bind(("127.0.0.1", 0)).expect("bind an ephemeral port");
    let addr = listener.local_addr().expect("local addr");
    std::thread::scope(|scope| {
        scope.spawn(|| {
            for _ in 0..connections {
                let (stream, _) = listener.accept().expect("accept");
                provider.handle(stream);
            }
        });
        body(addr);
    });
}

type Client = WebSocket<tungstenite::stream::MaybeTlsStream<TcpStream>>;

fn connect(addr: SocketAddr) -> Client {
    let (socket, _) = tungstenite::connect(format!("ws://{addr}/ws")).expect("websocket handshake");
    socket
}

/// Sends one text frame and returns the next text frame back.
fn exchange(client: &mut Client, frame: &str) -> String {
    client
        .send(Message::text(frame.to_owned()))
        .expect("send frame");
    loop {
        match client.read().expect("read frame") {
            Message::Text(text) => return text.to_string(),
            // Control frames are not answers; keep reading past them.
            Message::Ping(_) | Message::Pong(_) => (),
            other => panic!("expected a text frame, got {other:?}"),
        }
    }
}

fn json(frame: &str) -> serde_json::Value {
    serde_json::from_str(frame).unwrap_or_else(|e| panic!("not JSON: {e}\nframe: {frame}"))
}

#[test]
fn the_keepalive_is_a_bare_pong() {
    on_wire(1, |addr| {
        let mut client = connect(addr);
        assert_eq!(exchange(&mut client, "ping"), "pong");
        // …and the socket keeps working afterwards.
        assert_eq!(
            json(&exchange(&mut client, r#"{"type":"meta","version":1}"#))["type"],
            "meta"
        );
    });
}

#[test]
fn meta_describes_the_provider() {
    on_wire(1, |addr| {
        let mut client = connect(addr);
        let reply = json(&exchange(&mut client, r#"{"type":"meta","version":1}"#));
        assert_eq!(reply["type"], "meta");
        assert_eq!(reply["version"], 1);
        let meta: ProviderMeta = serde_json::from_value(reply["payload"].clone()).expect("meta");
        assert_eq!(meta.name, "mettle");
        assert!(meta.evaluator);
        assert_eq!(meta.generators, vec!["[0] run p".to_owned()]);
    });
}

#[test]
fn data_enters_the_current_datum() {
    on_wire(1, |addr| {
        let mut client = connect(addr);
        let reply = json(&exchange(&mut client, r#"{"type":"data","version":1}"#));
        assert_eq!(reply["type"], "data");
        let join: DataJoin = serde_json::from_value(reply["payload"].clone()).expect("join");
        assert_eq!(join.enter.len(), 1);
        assert_eq!(join.enter[0].id, "stub:0");
        assert_eq!(join.enter[0].format, "alloy");
        assert_eq!(join.enter[0].data, "<alloy><instance n=\"0\"/></alloy>");
        assert!(join.enter[0].evaluator);
        assert_eq!(join.enter[0].buttons[0].on_click, CLICK_NEXT);
        // Nothing was displayed before, so nothing is retired.
        assert!(join.update.is_empty());
    });
}

#[test]
fn a_next_click_advances_and_retires_the_previous_datum() {
    on_wire(1, |addr| {
        let mut client = connect(addr);
        let first = json(&exchange(&mut client, r#"{"type":"data","version":1}"#));
        assert_eq!(first["payload"]["enter"][0]["id"], "stub:0");

        let advanced = json(&exchange(
            &mut client,
            r#"{"type":"click","version":1,"payload":{"id":"stub:0","onClick":"next"}}"#,
        ));
        assert_eq!(advanced["type"], "data");
        let join: DataJoin = serde_json::from_value(advanced["payload"].clone()).expect("join");
        assert_eq!(join.enter[0].id, "stub:1");
        assert_eq!(join.enter[0].data, "<alloy><instance n=\"1\"/></alloy>");
        // The superseded datum keeps its place in the client's history with its
        // actions and evaluator switched off.
        assert_eq!(join.update.len(), 1);
        assert_eq!(join.update[0].id, "stub:0");
        assert!(!join.update[0].evaluator);
        assert!(join.update[0].buttons.is_empty());

        // A plain re-`data` of the same instance re-enters it and retires
        // nothing (there is nothing to retire).
        let again = json(&exchange(&mut client, r#"{"type":"data","version":1}"#));
        assert_eq!(again["payload"]["enter"][0]["id"], "stub:1");
        assert!(again["payload"].get("update").is_none());
    });
}

#[test]
fn eval_pairs_the_result_with_the_request_id() {
    on_wire(1, |addr| {
        let mut client = connect(addr);
        let reply = json(&exchange(
            &mut client,
            r#"{"type":"eval","version":1,"payload":{"id":"e7","datumId":"stub:0","expression":"some A"}}"#,
        ));
        assert_eq!(reply["type"], "eval");
        let result: EvalResult = serde_json::from_value(reply["payload"].clone()).expect("result");
        assert_eq!(result.id, "e7", "the expression id must round-trip");
        assert_eq!(result.result, "stub:0|some A|0");
    });
}

#[test]
fn every_refused_click_answers_with_a_typed_error() {
    on_wire(1, |addr| {
        let mut client = connect(addr);
        let cases = [
            (CLICK_NEXT_TRACE, "no-more-instances"),
            ("nonsense", "unknown-click"),
        ];
        for (verb, code) in cases {
            let reply = json(&exchange(
                &mut client,
                &format!(r#"{{"type":"click","version":1,"payload":{{"onClick":"{verb}"}}}}"#),
            ));
            assert_eq!(reply["type"], "error", "verb {verb}");
            let payload: ErrorPayload =
                serde_json::from_value(reply["payload"].clone()).expect("error payload");
            assert_eq!(payload.code, code);
            assert!(!payload.message.is_empty(), "a refusal must say something");
        }
        // An exhausted enumeration refuses the same way rather than looping.
        for _ in 0..2 {
            exchange(
                &mut client,
                r#"{"type":"click","version":1,"payload":{"onClick":"next"}}"#,
            );
        }
        let exhausted = json(&exchange(
            &mut client,
            r#"{"type":"click","version":1,"payload":{"onClick":"next"}}"#,
        ));
        assert_eq!(exhausted["payload"]["code"], "no-more-instances");
    });
}

/// mt-075's payload extension, at the wire level: the optional `state` a
/// client sends reaches the session, and omitting it is distinguishable from
/// sending any value (which is what keeps the provider's own fallback
/// reachable for a client that never learned about the field).
#[test]
fn a_clicks_optional_state_reaches_the_session() {
    on_wire(1, |addr| {
        let mut client = connect(addr);
        let with_state = json(&exchange(
            &mut client,
            r#"{"type":"click","version":1,"payload":{"onClick":"new-fork","state":3}}"#,
        ));
        assert_eq!(with_state["payload"]["enter"][0]["id"], "stub:4");

        let without_state = json(&exchange(
            &mut client,
            r#"{"type":"click","version":1,"payload":{"onClick":"new-fork"}}"#,
        ));
        assert_eq!(without_state["payload"]["enter"][0]["id"], "stub:900");
    });
}

#[test]
fn no_malformed_frame_panics_disconnects_or_goes_unanswered() {
    on_wire(1, |addr| {
        let mut client = connect(addr);
        let malformed = [
            ("", "malformed-message"),
            ("{", "malformed-message"),
            ("null", "malformed-message"),
            ("[1,2,3]", "malformed-message"),
            ("\"ping\"", "malformed-message"),
            (r#"{"version":1}"#, "malformed-message"),
            (r#"{"type":42,"version":1}"#, "malformed-message"),
            (r#"{"type":"bogus","version":1}"#, "unknown-message-type"),
            (r#"{"type":"click","version":1}"#, "bad-payload"),
            (
                r#"{"type":"click","version":1,"payload":{}}"#,
                "bad-payload",
            ),
            (
                r#"{"type":"eval","version":1,"payload":"nope"}"#,
                "bad-payload",
            ),
        ];
        for (frame, code) in malformed {
            let reply = json(&exchange(&mut client, frame));
            assert_eq!(reply["type"], "error", "frame {frame:?}");
            assert_eq!(reply["payload"]["code"], code, "frame {frame:?}");
        }
        // The socket survived all of it: a good request still works.
        let reply = json(&exchange(&mut client, r#"{"type":"data","version":1}"#));
        assert_eq!(reply["payload"]["enter"][0]["id"], "stub:0");
    });
}

#[test]
fn a_binary_frame_is_refused_in_words_rather_than_ignored() {
    on_wire(1, |addr| {
        let mut client = connect(addr);
        client
            .send(Message::binary(vec![0x00, 0x01]))
            .expect("send binary");
        let Message::Text(text) = client.read().expect("read") else {
            panic!("expected a text answer to a binary frame");
        };
        assert_eq!(json(&text)["payload"]["code"], "malformed-message");
    });
}

/// Sends a raw HTTP request and returns `(status line, body)`.
fn http_get(addr: SocketAddr, target: &str) -> (String, String) {
    let mut stream = TcpStream::connect(addr).expect("connect");
    write!(
        stream,
        "GET {target} HTTP/1.1\r\nHost: {addr}\r\nConnection: close\r\n\r\n"
    )
    .expect("write request");
    stream.flush().expect("flush");
    let mut reader = BufReader::new(stream);
    let mut status = String::new();
    reader.read_line(&mut status).expect("status line");
    let mut rest = String::new();
    reader.read_to_string(&mut rest).expect("body");
    let body = rest
        .split_once("\r\n\r\n")
        .map_or("", |(_, b)| b)
        .to_owned();
    (status.trim_end().to_owned(), body)
}

#[test]
fn the_same_port_serves_assets() {
    on_wire(3, |addr| {
        let (status, body) = http_get(addr, "/");
        assert_eq!(status, "HTTP/1.1 200 OK");
        assert_eq!(body, INDEX_HTML);

        // The upstream SPA's `?<port>` handoff is not part of the path.
        let (status, body) = http_get(addr, "/?4321");
        assert_eq!(status, "HTTP/1.1 200 OK");
        assert_eq!(body, INDEX_HTML);

        let (status, _) = http_get(addr, "/does-not-exist");
        assert_eq!(status, "HTTP/1.1 404 Not Found");
    });
}

#[test]
fn an_external_sterling_may_upgrade_on_the_root_path() {
    // Free interop with the stock frontend, whose `getWebSocketURLFromLocation`
    // builds `ws://localhost:<port>` with no path at all (sterling.md §2.1).
    on_wire(1, |addr| {
        let (mut socket, response) =
            tungstenite::connect(format!("ws://{addr}/")).expect("handshake on /");
        assert_eq!(response.status().as_u16(), 101);
        socket.send(Message::text("ping")).expect("send");
        let Message::Text(text) = socket.read().expect("read") else {
            panic!("expected pong");
        };
        assert_eq!(text.as_str(), "pong");
    });
}
