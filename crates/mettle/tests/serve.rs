//! End-to-end integration tests for `mettle serve` (mt-072): the **built
//! binary**, a real ephemeral port, and a real WebSocket client.
//!
//! The point of testing at this level rather than against the session type is
//! the two identities that matter to a user, neither of which can be checked
//! without running the whole thing:
//!
//! 1. `data` hands over **byte-identical** XML to what `mettle exec --xml`
//!    writes for the same command (mt-071 is the one writer; serve is not
//!    allowed to have a dialect of its own);
//! 2. `eval` answers **exactly** what `mettle exec --eval` answers, `:state`
//!    included (the REPL is the one evaluator).
//!
//! Everything binds `--port 0`, so tests never collide with each other or with
//! a developer's running server. Each test spawns its own server and kills it
//! on the way out, whether it passed or panicked ([`Server`]'s `Drop`).

use std::io::{BufRead as _, BufReader};
use std::net::{SocketAddr, TcpStream};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::time::Duration;

use tungstenite::stream::MaybeTlsStream;
use tungstenite::{Message, WebSocket};

/// A hung server must fail the test rather than hang the suite.
const READ_TIMEOUT: Duration = Duration::from_mins(1);

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/serve")
        .join(name)
}

/// A running `mettle serve`, killed when the test's binding goes out of scope.
struct Server {
    child: Child,
    address: SocketAddr,
    /// Everything the server printed before it started listening — the verdict
    /// block, which some tests check.
    banner: String,
}

impl Drop for Server {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// Spawns `mettle serve <file> [extra…] --port 0` and waits for its URL line.
fn serve(file: &Path, extra: &[&str]) -> Server {
    let mut child = Command::new(env!("CARGO_BIN_EXE_mettle"))
        .arg("serve")
        .arg(file)
        .args(extra)
        .args(["--port", "0"])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn mettle serve");

    let stdout = child.stdout.take().expect("piped stdout");
    let mut reader = BufReader::new(stdout);
    let mut banner = String::new();
    let mut line = String::new();
    let address = loop {
        line.clear();
        let read = reader.read_line(&mut line).expect("read serve stdout");
        assert!(read > 0, "mettle serve exited before listening:\n{banner}");
        if let Some(url) = line
            .trim()
            .strip_prefix("mettle serve: listening on http://")
        {
            break url.parse::<SocketAddr>().expect("a socket address");
        }
        banner.push_str(&line);
    };
    Server {
        child,
        address,
        banner,
    }
}

type Client = WebSocket<MaybeTlsStream<TcpStream>>;

fn connect(server: &Server) -> Client {
    let (socket, _) = tungstenite::connect(format!("ws://{}/ws", server.address))
        .expect("provider websocket handshake");
    if let MaybeTlsStream::Plain(stream) = socket.get_ref() {
        stream
            .set_read_timeout(Some(READ_TIMEOUT))
            .expect("set read timeout");
    }
    socket
}

/// Sends one text frame, returns the next text frame's decoded JSON.
fn request(client: &mut Client, frame: &str) -> serde_json::Value {
    let text = raw_request(client, frame);
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("not JSON: {e}\nframe: {text}"))
}

fn raw_request(client: &mut Client, frame: &str) -> String {
    client
        .send(Message::text(frame.to_owned()))
        .expect("send frame");
    loop {
        match client.read().expect("read frame") {
            Message::Text(text) => return text.to_string(),
            Message::Ping(_) | Message::Pong(_) => (),
            other => panic!("expected a text frame, got {other:?}"),
        }
    }
}

fn data(client: &mut Client) -> serde_json::Value {
    request(client, r#"{"type":"data","version":1}"#)
}

fn click(client: &mut Client, on_click: &str) -> serde_json::Value {
    request(
        client,
        &format!(r#"{{"type":"click","version":1,"payload":{{"onClick":"{on_click}"}}}}"#),
    )
}

/// A click carrying mt-075's optional displayed-state index.
fn click_at(client: &mut Client, on_click: &str, state: usize) -> serde_json::Value {
    request(
        client,
        &format!(
            r#"{{"type":"click","version":1,"payload":{{"onClick":"{on_click}","state":{state}}}}}"#
        ),
    )
}

fn eval(client: &mut Client, datum_id: &str, expression: &str) -> String {
    let payload = serde_json::json!({
        "type": "eval",
        "version": 1,
        "payload": { "id": "e0", "datumId": datum_id, "expression": expression },
    });
    let reply = request(client, &payload.to_string());
    assert_eq!(reply["type"], "eval", "{reply}");
    assert_eq!(
        reply["payload"]["id"], "e0",
        "the expression id round-trips"
    );
    reply["payload"]["result"]
        .as_str()
        .expect("a string result")
        .to_owned()
}

fn entered(reply: &serde_json::Value) -> &serde_json::Value {
    assert_eq!(reply["type"], "data", "{reply}");
    &reply["payload"]["enter"][0]
}

/// Runs `mettle exec` with the given arguments and returns its stdout.
fn exec(args: &[&str]) -> String {
    let out = Command::new(env!("CARGO_BIN_EXE_mettle"))
        .arg("exec")
        .args(args)
        .output()
        .expect("failed to spawn mettle exec");
    assert!(
        out.status.success(),
        "mettle exec {args:?} failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).expect("utf-8 stdout")
}

/// (1) The served XML is mt-071's, byte for byte — same writer, same
/// `filename=`, same instance.
#[test]
fn data_is_byte_identical_to_the_xml_export() {
    let file = fixture("enumerable.als");
    let path = file.to_str().expect("utf-8 path");
    let export = std::env::temp_dir().join(format!("mettle-serve-xml-{}.xml", std::process::id()));
    let export_path = export.to_str().expect("utf-8 path");
    exec(&[path, "--xml", export_path]);
    let expected = std::fs::read_to_string(&export).expect("the exported XML");
    let _ = std::fs::remove_file(&export);

    let server = serve(&file, &[]);
    let mut client = connect(&server);
    let entering = entered(&data(&mut client)).clone();
    assert_eq!(entering["format"], "alloy");
    assert_eq!(
        entering["data"].as_str().expect("xml string"),
        expected,
        "serve must hand over exactly what --xml writes"
    );
    // The verdict block printed at startup is `exec`'s, too.
    assert!(server.banner.contains("SAT"), "{}", server.banner);
    assert!(
        server
            .banner
            .contains("this/Node.color = {Node$0->Green$0}"),
        "{}",
        server.banner
    );
}

/// (2) `eval` is the REPL's answer, not a second evaluator.
#[test]
fn eval_matches_the_repl_exactly() {
    let file = fixture("enumerable.als");
    let path = file.to_str().expect("utf-8 path");
    let server = serve(&file, &[]);
    let mut client = connect(&server);
    let datum_id = entered(&data(&mut client))["id"]
        .as_str()
        .expect("a datum id")
        .to_owned();

    for expression in ["#Node", "Node.color", "some Node", "Node.color = Red"] {
        let over_the_wire = eval(&mut client, &datum_id, expression);
        let at_the_prompt = exec(&[path, "--eval", expression]);
        assert_eq!(
            over_the_wire,
            at_the_prompt.lines().last().expect("a result line"),
            "expression {expression}"
        );
    }

    // A rejected expression carries the REPL's own caret diagnostic into the
    // one result slot the protocol has, rather than a bare "error".
    let rejected = eval(&mut client, &datum_id, "no such name");
    assert!(rejected.contains("error"), "{rejected}");
    assert!(rejected.contains("<repl>"), "{rejected}");
    assert!(!rejected.ends_with('\n'), "one field, not a terminal line");
}

/// (3) A `next` click advances the enumeration, re-`data` shows the new
/// instance, and running out is a typed refusal rather than a repeat.
#[test]
fn next_advances_the_enumeration_then_refuses_honestly() {
    let file = fixture("enumerable.als");
    let server = serve(&file, &[]);
    let mut client = connect(&server);

    let first = entered(&data(&mut client)).clone();
    assert_eq!(first["buttons"][0]["onClick"], "next");

    let advanced = click(&mut client, "next");
    let second = entered(&advanced).clone();
    assert_ne!(second["id"], first["id"], "the datum id must change");
    assert_ne!(
        second["data"], first["data"],
        "a distinct instance must have distinct XML"
    );
    // The previous datum is retired rather than left live alongside the new one.
    assert_eq!(advanced["payload"]["update"][0]["id"], first["id"]);
    assert_eq!(advanced["payload"]["update"][0]["evaluator"], false);

    // A plain re-`data` now shows the advanced instance.
    let re_read = entered(&data(&mut client)).clone();
    assert_eq!(re_read["id"], second["id"]);
    assert_eq!(re_read["data"], second["data"]);

    // The fixture has exactly two instances, so the third click runs out.
    let exhausted = click(&mut client, "next");
    assert_eq!(exhausted["type"], "error", "{exhausted}");
    assert_eq!(exhausted["payload"]["code"], "no-more-instances");

    // …and the button is gone from the datum afterwards, so a UI cannot
    // offer an action that is known not to work.
    let after = entered(&data(&mut client)).clone();
    assert_eq!(
        after["buttons"].as_array().map(Vec::len),
        Some(0),
        "{after}"
    );

    // The four trace verbs are implemented (mt-076) but mean nothing here, so
    // a static session refuses them as unknown *for this command* — not as
    // "not yet supported", which would be false.
    for verb in ["next-trace", "next-config", "new-init", "new-fork"] {
        let reply = click(&mut client, verb);
        assert_eq!(reply["type"], "error", "verb {verb}: {reply}");
        assert_eq!(reply["payload"]["code"], "unknown-click", "verb {verb}");
        assert!(
            reply["payload"]["message"]
                .as_str()
                .expect("message")
                .contains("not temporal"),
            "the refusal says why: {reply}"
        );
    }
}

/// (4) The evaluator follows the enumeration: after an advance, the old datum
/// id is refused and the new one answers about the new instance.
#[test]
fn the_evaluator_follows_the_advance_and_refuses_a_stale_datum() {
    let file = fixture("enumerable.als");
    let server = serve(&file, &[]);
    let mut client = connect(&server);

    let first_id = entered(&data(&mut client))["id"]
        .as_str()
        .expect("id")
        .to_owned();
    let first_colour = eval(&mut client, &first_id, "Node.color");

    let second_id = entered(&click(&mut client, "next"))["id"]
        .as_str()
        .expect("id")
        .to_owned();
    let second_colour = eval(&mut client, &second_id, "Node.color");
    assert_ne!(
        first_colour, second_colour,
        "the evaluator must have moved with the instance"
    );

    let stale = eval(&mut client, &first_id, "Node.color");
    assert!(stale.contains(&second_id), "{stale}");
    assert!(stale.contains("superseded"), "{stale}");
}

/// (5) A temporal command serves its whole lasso, evaluates per state through
/// the REPL's `:state`, and — as of mt-076 — answers every enumeration verb.
///
/// This fixture's four verbs mostly *refuse*, and each refusal is a pinned
/// jar behavior rather than a gap: its only static relation is `one sig
/// Counter` (exact-bounded, so "New Config" is probe P-076-1's
/// no-free-static-primaries case) and its state 0 is pinned by `fact { no A }`
/// (so "New Init" is probe P-076-6's UNSAT case). The reachable-enumeration
/// side is `a_temporal_command_enumerates_traces_and_configurations` below.
#[test]
fn a_temporal_command_serves_its_trace_and_answers_every_verb() {
    let file = fixture("temporal.als");
    let path = file.to_str().expect("utf-8 path");
    let server = serve(&file, &[]);
    let mut client = connect(&server);

    let datum = entered(&data(&mut client)).clone();
    let xml = datum["data"].as_str().expect("xml");
    assert_eq!(
        xml.matches("<instance").count(),
        2,
        "a two-state lasso is two <instance> blocks: {xml}"
    );
    // Buttons now exist. All four, because the evaluator starts at state 0 of
    // a two-state trace, so `current + 1 = 1` is a real state to fork at.
    let buttons: Vec<String> = datum["buttons"]
        .as_array()
        .expect("buttons")
        .iter()
        .map(|b| b["onClick"].as_str().expect("onClick").to_owned())
        .collect();
    assert_eq!(
        buttons,
        ["next-trace", "next-config", "new-init", "new-fork"]
    );

    let datum_id = datum["id"].as_str().expect("id").to_owned();
    // The session starts at state 0, exactly as `--eval` does.
    assert_eq!(
        eval(&mut client, &datum_id, "some A"),
        exec(&[path, "--eval", "some A"])
            .lines()
            .last()
            .expect("result")
    );
    // …and `:state N` moves it, exactly as `--state N` does.
    let moved = eval(&mut client, &datum_id, ":state 1");
    assert!(moved.contains("state 1"), "{moved}");
    assert_eq!(
        eval(&mut client, &datum_id, "some A"),
        exec(&[path, "--eval", "some A", "--state", "1"])
            .lines()
            .last()
            .expect("result")
    );

    // Every verb answers in the pinned way, and none of them says "not yet".
    for verb in ["next", "next-trace", "next-config", "new-init", "new-fork"] {
        let reply = click(&mut client, verb);
        assert_eq!(reply["type"], "error", "verb {verb}: {reply}");
        let code = reply["payload"]["code"].as_str().expect("code");
        assert_eq!(
            code, "no-more-instances",
            "verb {verb} is refused because the jar refuses it here, not \
             because it is unimplemented: {reply}"
        );
        assert!(
            !reply["payload"]["message"]
                .as_str()
                .expect("message")
                .contains("mt-076"),
            "no defer names a bead any more: {reply}"
        );
    }
    // An unknown verb is still an unknown verb.
    assert_eq!(
        click(&mut client, "next-universe")["payload"]["code"],
        "unknown-click"
    );
}

/// (5a) The reachable half of mt-076: a temporal command with both a real path
/// space and a real configuration space enumerates through both.
///
/// The numbers are the jar's own, from probes P-076-1/P-076-5 against this
/// fixture's shape: **8 traces** inside the first configuration, then
/// exhaustion; **2 configurations** in total (`|X|` = 1, 2 at this scope), each
/// shown once.
#[test]
fn a_temporal_command_enumerates_traces_and_configurations() {
    let server = serve(&fixture("temporal-enum.als"), &[]);
    let mut client = connect(&server);

    let first = entered(&data(&mut client)).clone();
    let mut ids = vec![first["id"].as_str().expect("id").to_owned()];
    let mut xmls = vec![first["data"].as_str().expect("xml").to_owned()];

    // "New Trace" walks the whole path space of one configuration and then
    // retires its own button.
    loop {
        let reply = click(&mut client, "next-trace");
        if reply["type"] == "error" {
            assert_eq!(reply["payload"]["code"], "no-more-instances", "{reply}");
            break;
        }
        let datum = entered(&reply).clone();
        ids.push(datum["id"].as_str().expect("id").to_owned());
        xmls.push(datum["data"].as_str().expect("xml").to_owned());
        assert!(ids.len() <= 16, "enumeration did not terminate");
    }
    assert_eq!(
        ids.len(),
        8,
        "probe P-076-5: 8 traces inside one configuration"
    );
    let mut unique = xmls.clone();
    unique.sort();
    unique.dedup();
    assert_eq!(unique.len(), 8, "every trace shown is a different trace");
    let mut unique_ids = ids.clone();
    unique_ids.sort();
    unique_ids.dedup();
    assert_eq!(unique_ids.len(), 8, "every advance mints a fresh datum id");

    // The exhausted verb's button is gone; the other three remain, because
    // they ask different questions of the same command.
    let buttons: Vec<String> = entered(&data(&mut client))["buttons"]
        .as_array()
        .expect("buttons")
        .iter()
        .map(|b| b["onClick"].as_str().expect("onClick").to_owned())
        .collect();
    assert!(!buttons.contains(&"next-trace".to_owned()), "{buttons:?}");
    assert!(buttons.contains(&"next-config".to_owned()), "{buttons:?}");

    // "New Config" still works, and moves to the second configuration.
    let second_config = entered(&click(&mut client, "next-config")).clone();
    assert_ne!(
        second_config["data"].as_str().expect("xml"),
        xmls[0],
        "a new configuration is a different picture"
    );
    // …and then there is no third.
    let refused = click(&mut client, "next-config");
    assert_eq!(refused["type"], "error", "{refused}");
    assert_eq!(refused["payload"]["code"], "no-more-instances");
}

/// (5c) mt-075's `click.state`: mettle's own frontend steps through a lasso
/// client-side, so its stepper — not the evaluator pane — is what says where a
/// "New Fork" forks. The field is optional, and its absence must still reach
/// the pane-driven arrangement an external client depends on.
#[test]
fn new_fork_forks_at_the_state_the_client_says_it_is_showing() {
    let server = serve(&fixture("temporal-enum.als"), &[]);
    let mut client = connect(&server);
    let first = entered(&data(&mut client)).clone();
    let first_id = first["id"].as_str().expect("id").to_owned();
    assert_eq!(
        first["data"]
            .as_str()
            .expect("xml")
            .matches("<instance")
            .count(),
        2,
        "this fixture is a two-state lasso"
    );

    // Forking *after* the last state has nowhere to go (probe P-076-6). That
    // this refuses is what proves the sent index was used at all: the session's
    // own fallback sits at state 0, where the same verb succeeds below.
    let refused = click_at(&mut client, "new-fork", 1);
    assert_eq!(refused["type"], "error", "{refused}");
    assert_eq!(refused["payload"]["code"], "no-more-instances");

    // A state this trace does not have is refused as such, never guessed at.
    let out_of_range = click_at(&mut client, "new-fork", 7);
    assert_eq!(out_of_range["type"], "error", "{out_of_range}");
    assert_eq!(out_of_range["payload"]["code"], "state-out-of-range");
    assert!(
        out_of_range["payload"]["message"]
            .as_str()
            .expect("message")
            .contains("2 states"),
        "the refusal says how many states there are: {out_of_range}"
    );

    // …and at state 0 the same verb forks.
    let forked = entered(&click_at(&mut client, "new-fork", 0)).clone();
    let forked_id = forked["id"].as_str().expect("id").to_owned();
    assert_ne!(forked_id, first_id, "a fork mints a fresh datum");

    // With the field omitted the provider reads its evaluator pane instead —
    // the arrangement mt-072 shipped and an external Sterling still gets. The
    // fresh datum's pane starts at state 0, so `:state 1` moves it, and
    // "New Fork" then refuses exactly as the explicit state 1 did.
    let moved = eval(&mut client, &forked_id, ":state 1");
    assert!(moved.contains("state 1"), "{moved}");
    let fallback = click(&mut client, "new-fork");
    assert_eq!(fallback["type"], "error", "{fallback}");
    assert_eq!(fallback["payload"]["code"], "no-more-instances");
}

/// (5b) Two clients at once — the shape a second browser tab produces. Both
/// are served (thread per connection), and both see one shared session: an
/// advance driven by one is visible to the other.
#[test]
fn two_clients_share_one_session_without_interleaving() {
    let server = serve(&fixture("enumerable.als"), &[]);
    let mut first = connect(&server);
    let mut second = connect(&server);

    let start = entered(&data(&mut first))["id"].clone();
    assert_eq!(
        entered(&data(&mut second))["id"],
        start,
        "both tabs open on the same instance"
    );

    let advanced = entered(&click(&mut first, "next"))["id"].clone();
    assert_ne!(advanced, start);
    // The second connection has its own datum history — so it both sees the
    // new instance and is told the one it was showing is superseded.
    let seen = data(&mut second);
    assert_eq!(entered(&seen)["id"], advanced);
    assert_eq!(seen["payload"]["update"][0]["id"], start);

    // Both sockets still work afterwards.
    assert_eq!(raw_request(&mut first, "ping"), "pong");
    assert_eq!(raw_request(&mut second, "ping"), "pong");
}

/// (6) `meta` and `ping` — the two verbs with no instance in them.
#[test]
fn meta_and_ping_answer_without_touching_the_instance() {
    let server = serve(&fixture("enumerable.als"), &[]);
    let mut client = connect(&server);
    assert_eq!(raw_request(&mut client, "ping"), "pong");

    let meta = request(&mut client, r#"{"type":"meta","version":1}"#);
    assert_eq!(meta["type"], "meta");
    assert_eq!(meta["payload"]["name"], "mettle");
    assert_eq!(meta["payload"]["evaluator"], true);
    assert_eq!(
        meta["payload"]["views"],
        serde_json::json!(["graph", "table"])
    );
    assert!(meta["payload"]["generators"][0]
        .as_str()
        .expect("a generator name")
        .starts_with("[0] run"));
}

/// (7) Malformed input is answered, not fatal: the session survives and keeps
/// serving the same instance.
#[test]
fn a_malformed_client_cannot_take_the_session_down() {
    let server = serve(&fixture("enumerable.als"), &[]);
    let mut client = connect(&server);
    let before = entered(&data(&mut client))["id"].clone();

    for frame in [
        "{",
        "[]",
        r#"{"type":"eval","version":1}"#,
        r#"{"type":"whatever","version":1}"#,
        r#"{"type":"click","version":1,"payload":{"onClick":"do-something-else"}}"#,
    ] {
        let reply = request(&mut client, frame);
        assert_eq!(reply["type"], "error", "frame {frame}");
        assert!(!reply["payload"]["message"]
            .as_str()
            .expect("a message")
            .is_empty());
    }

    let after = entered(&data(&mut client))["id"].clone();
    assert_eq!(before, after, "the session must be unmoved");
}

/// (8) The page and the socket share one port, and the page is the app —
/// shell, stylesheet, and the ES modules it imports, all off this one origin
/// (mt-075: an embedded frontend that reaches the network is not one).
#[test]
fn one_port_serves_both_the_app_and_the_provider() {
    let file = fixture("enumerable.als");
    let server = serve(&file, &[]);
    let body = http_get(server.address, "/");
    assert!(body.starts_with("<!doctype html>"), "{body}");
    assert!(body.contains("enumerable.als"), "{body}");
    assert!(
        body.contains(r#"<script type="module" src="/app.js">"#),
        "the page must boot the app: {body}"
    );
    // The panes the app is made of, asserted by their own anchors rather than
    // by prose that could drift.
    for anchor in [
        r#"id="instance""#,
        r#"id="evaluator""#,
        r#"id="stepper""#,
        r#"id="actions""#,
        r#"id="show-builtins""#,
        r#"id="views""#,
    ] {
        assert!(body.contains(anchor), "the shell is missing {anchor}");
    }
    assert!(!body.contains("{{"), "an unfilled template slot: {body}");

    // Every module the browser will fetch is served, with a type it will
    // actually execute.
    for (target, content_type) in [
        ("/app.css", "text/css"),
        ("/graph.css", "text/css"),
        ("/app.js", "text/javascript"),
        ("/protocol.js", "text/javascript"),
        ("/instance.js", "text/javascript"),
        ("/tables.js", "text/javascript"),
        ("/layout.js", "text/javascript"),
        ("/graph.js", "text/javascript"),
        ("/ui.js", "text/javascript"),
    ] {
        let response = http_response(server.address, target);
        assert!(
            response.starts_with("HTTP/1.1 200 OK"),
            "{target}: {response}"
        );
        assert!(
            response.contains(&format!("Content-Type: {content_type}")),
            "{target} must be served as {content_type}: {response}"
        );
    }

    // The same address upgrades.
    let mut client = connect(&server);
    assert_eq!(raw_request(&mut client, "ping"), "pong");
}

fn http_get(address: SocketAddr, target: &str) -> String {
    let response = http_response(address, target);
    assert!(
        response.starts_with("HTTP/1.1 200 OK"),
        "unexpected response: {response}"
    );
    response
        .split_once("\r\n\r\n")
        .map_or("", |(_, body)| body)
        .to_owned()
}

/// The whole response, headers included.
fn http_response(address: SocketAddr, target: &str) -> String {
    use std::io::{Read as _, Write as _};
    let mut stream = TcpStream::connect(address).expect("connect");
    stream
        .set_read_timeout(Some(READ_TIMEOUT))
        .expect("read timeout");
    write!(
        stream,
        "GET {target} HTTP/1.1\r\nHost: {address}\r\nConnection: close\r\n\r\n"
    )
    .expect("write request");
    let mut response = String::new();
    stream.read_to_string(&mut response).expect("read response");
    response
}

/// (9) A file with several commands needs `--command`, and the selection
/// works — the same convention `--xml` uses.
#[test]
fn a_multi_command_file_needs_a_command_selection() {
    let file = fixture("multi.als");
    let out = Command::new(env!("CARGO_BIN_EXE_mettle"))
        .arg("serve")
        .arg(&file)
        .args(["--port", "0"])
        .output()
        .expect("spawn");
    assert!(!out.status.success());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("this file has 2 commands"), "{stderr}");
    assert!(stderr.contains("--command"), "{stderr}");

    let server = serve(&file, &["--command", "1"]);
    let mut client = connect(&server);
    let meta = request(&mut client, r#"{"type":"meta","version":1}"#);
    assert_eq!(meta["payload"]["generators"][0], "[1] run q for 2");
}

/// (10) Nothing to visualize is a loud refusal, not a server onto an empty
/// page — the `--xml` posture.
#[test]
fn an_unsatisfiable_command_refuses_to_serve() {
    let out = Command::new(env!("CARGO_BIN_EXE_mettle"))
        .arg("serve")
        .arg(fixture("unsat.als"))
        .args(["--port", "0"])
        .output()
        .expect("spawn");
    assert!(!out.status.success());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("nothing to visualize"), "{stderr}");
}

/// (11) `--bind 0.0.0.0` is what a container needs (mettle listens on
/// loopback only by default): the listener really does come up on the
/// unspecified address, and a client can still reach it — `connect()`
/// resolving `0.0.0.0:PORT` to loopback, exactly as the OS does for the
/// browser a `docker run -p` forwards from.
#[test]
fn bind_0_0_0_0_accepts_a_connection() {
    let server = serve(&fixture("enumerable.als"), &["--bind", "0.0.0.0"]);
    assert_eq!(
        server.address.ip(),
        std::net::IpAddr::V4(std::net::Ipv4Addr::UNSPECIFIED)
    );

    let mut client = connect(&server);
    let reply = data(&mut client);
    assert_eq!(entered(&reply)["format"], "alloy");
}

/// (11a) The unspecified address is not itself a URL a browser can open, so
/// the extra banner line names one that is.
#[test]
fn bind_0_0_0_0_banner_names_a_url_a_browser_can_open() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_mettle"))
        .arg("serve")
        .arg(fixture("enumerable.als"))
        .args(["--bind", "0.0.0.0"])
        .args(["--port", "0"])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn");
    let stdout = child.stdout.take().expect("piped stdout");
    let mut reader = BufReader::new(stdout);
    let mut lines = String::new();
    let mut line = String::new();
    let found = loop {
        line.clear();
        let read = reader.read_line(&mut line).expect("read stdout");
        assert!(
            read > 0,
            "server exited before printing the banner:\n{lines}"
        );
        lines.push_str(&line);
        if line.contains("bound to all interfaces") {
            break line.clone();
        }
        assert!(
            lines.matches('\n').count() < 40,
            "banner never arrived:\n{lines}"
        );
    };
    let _ = child.kill();
    let _ = child.wait();
    assert!(found.contains("http://127.0.0.1:"), "{found}");
}

/// (12) `--bind` is validated like every other option: a value that is not an
/// IP address is a usage error (exit 2), not a panic or a silent fallback.
#[test]
fn bind_garbage_is_a_usage_error() {
    let out = Command::new(env!("CARGO_BIN_EXE_mettle"))
        .arg("serve")
        .arg(fixture("enumerable.als"))
        .args(["--bind", "not-an-address"])
        .args(["--port", "0"])
        .output()
        .expect("spawn");
    assert_eq!(out.status.code(), Some(2), "{out:?}");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("--bind expects an IP address"), "{stderr}");
    assert!(stderr.contains("not-an-address"), "{stderr}");
}
