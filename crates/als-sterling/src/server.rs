//! The one-port provider server: static assets over HTTP, the Sterling
//! protocol over WebSocket, on a single [`TcpListener`].
//!
//! **Why the HTTP side is hand-rolled.** The whole HTTP surface is "GET a
//! handful of embedded files"; a framework would be a large dependency for a
//! ~60-line responsibility (STYLE P1/P2). The WebSocket side is *not*
//! hand-rolled — RFC 6455 framing is where the real risk is, and that is
//! [`tungstenite`]'s job. Its handshake *echo* is ours (`crate::handshake`),
//! which is what lets the dependency be taken without its `handshake` feature.
//!
//! **Why one port.** sterling.md §2.1 records that the upstream SPA derives its
//! provider URL from its own query string (`http://…:4000?1234` ⇒
//! `ws://localhost:1234`), which is why Forge runs two servers. mettle serves
//! its own frontend (ADR-0016 Resolution 1), so it can route on the request
//! instead: **any** request carrying `Upgrade: websocket` becomes a provider
//! socket, whatever its path, and everything else is an asset. That keeps the
//! upstream two-port shape working as free interop (an external Sterling
//! pointed at `ws://localhost:<port>` upgrades on `/`) while mettle's own
//! frontend just opens `/ws` on the page's own origin.
//!
//! Concurrency is one blocking thread per connection ([`std::thread::scope`],
//! so no `'static` bound is forced on the borrowed solve artifacts), with the
//! session behind a [`Mutex`] — two browser tabs must not interleave inside one
//! enumeration.

use std::io::{self, BufRead as _, BufReader, Read as _, Write as _};
use std::net::{TcpListener, TcpStream};
use std::sync::Mutex;

use tungstenite::protocol::{Role, WebSocket};
use tungstenite::Message;

use crate::handshake::derive_accept_key;
use crate::protocol::{parse_request, DataJoin, DatumMeta, ProtocolError, Request, Response, PONG};
use crate::session::{ServeSession, SessionDatum};

/// The largest request head the server will read, in bytes. A local dev server
/// still does not read an unbounded byte stream into memory on the word of an
/// unauthenticated client.
const MAX_HEAD_BYTES: usize = 16 * 1024;

/// The largest number of header lines read, for the same reason.
const MAX_HEADER_LINES: usize = 100;

/// Something worth telling the operator about. The CLI decides what to print —
/// library crates never do (STYLE E3).
#[derive(Debug)]
pub enum ServeEvent<'a> {
    /// A provider socket opened.
    Connected,
    /// A provider socket closed cleanly.
    Disconnected,
    /// A static asset request was answered.
    Served {
        /// The request target, query string stripped.
        target: &'a str,
        /// The HTTP status sent.
        status: u16,
    },
    /// A connection ended badly. Never fatal to the server.
    Failed {
        /// Which stage failed, as a fixed phrase.
        context: &'static str,
        /// The underlying detail, already rendered.
        detail: String,
    },
}

/// One embedded file.
#[derive(Clone, PartialEq, Eq, Debug)]
struct Asset {
    path: String,
    content_type: &'static str,
    body: Vec<u8>,
}

/// The files served over HTTP — mt-075's frontend, and until then the stub
/// page the CLI builds.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct StaticAssets {
    assets: Vec<Asset>,
}

impl StaticAssets {
    /// Registers one file at an absolute request path (`/`, `/app.js`, …).
    pub fn add(&mut self, path: impl Into<String>, content_type: &'static str, body: Vec<u8>) {
        self.assets.push(Asset {
            path: path.into(),
            content_type,
            body,
        });
    }

    /// The asset for a request target, or `None` for a 404. Linear search over
    /// a handful of entries — a map would be a `HashMap` in an output path
    /// (STYLE C1) for no measurable gain.
    fn get(&self, path: &str) -> Option<&Asset> {
        self.assets.iter().find(|asset| asset.path == path)
    }
}

/// Everything a connection needs: the assets, the shared session, and where to
/// report to.
///
/// The reporter is a trait object rather than a generic parameter because it is
/// called a handful of times per connection and nothing here is hot.
pub struct Provider<'a, S> {
    assets: &'a StaticAssets,
    session: &'a Mutex<S>,
    report: &'a (dyn Fn(&ServeEvent<'_>) + Sync),
}

impl<S> std::fmt::Debug for Provider<'_, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Provider")
            .field("assets", &self.assets)
            .finish_non_exhaustive()
    }
}

impl<'a, S: ServeSession + Send> Provider<'a, S> {
    /// Binds a provider to its assets, session, and reporter.
    pub fn new(
        assets: &'a StaticAssets,
        session: &'a Mutex<S>,
        report: &'a (dyn Fn(&ServeEvent<'_>) + Sync),
    ) -> Self {
        Provider {
            assets,
            session,
            report,
        }
    }

    /// Serves until the process is stopped: accept, hand each connection to its
    /// own thread, repeat.
    ///
    /// Never returns under normal operation — `mettle serve` runs until Ctrl-C
    /// (there is no in-band shutdown verb in the protocol, and inventing one
    /// would be a second way to kill a server that Ctrl-C already kills).
    /// Tests drive [`handle`](Provider::handle) directly instead.
    pub fn accept_loop(&self, listener: &TcpListener) {
        std::thread::scope(|scope| {
            for incoming in listener.incoming() {
                match incoming {
                    Ok(stream) => {
                        scope.spawn(move || self.handle(stream));
                    }
                    // One refused connection is not a reason to stop serving
                    // the ones that follow.
                    Err(e) => self.emit(&ServeEvent::Failed {
                        context: "accepting a connection",
                        detail: e.to_string(),
                    }),
                }
            }
        });
    }

    /// Serves exactly one connection to completion, then closes it.
    pub fn handle(&self, stream: TcpStream) {
        if let Err(e) = self.route(stream) {
            self.emit(&ServeEvent::Failed {
                context: "serving a connection",
                detail: e.to_string(),
            });
        }
    }

    fn emit(&self, event: &ServeEvent<'_>) {
        (self.report)(event);
    }

    /// Reads the request head and dispatches: WebSocket upgrade, or asset.
    fn route(&self, stream: TcpStream) -> io::Result<()> {
        let mut reader = BufReader::new(stream);
        let Some(head) = read_head(&mut reader)? else {
            // A connection opened and closed without sending a request (a
            // browser pre-connect, a port scan). Nothing to answer.
            return Ok(());
        };
        if head.is_websocket_upgrade() {
            return self.upgrade(reader, &head);
        }
        let mut stream = reader.into_inner();
        self.serve_asset(&mut stream, &head)
    }

    /// Answers a plain GET from the embedded assets.
    fn serve_asset(&self, stream: &mut TcpStream, head: &RequestHead) -> io::Result<()> {
        let target = head.path();
        let (status, reason, content_type, body): (u16, &str, &str, &[u8]) = if head.method != "GET"
        {
            (405, "Method Not Allowed", "text/plain; charset=utf-8", b"")
        } else if let Some(asset) = self.assets.get(target) {
            (200, "OK", asset.content_type, &asset.body)
        } else {
            (
                404,
                "Not Found",
                "text/plain; charset=utf-8",
                b"not found\n" as &[u8],
            )
        };
        self.emit(&ServeEvent::Served { target, status });
        // `Connection: close` throughout: without keep-alive there is no
        // pipelining to get wrong, and a browser opening one connection per
        // asset costs nothing on loopback.
        write!(
            stream,
            "HTTP/1.1 {status} {reason}\r\n\
             Content-Type: {content_type}\r\n\
             Content-Length: {}\r\n\
             Cache-Control: no-store\r\n\
             Connection: close\r\n\
             \r\n",
            body.len()
        )?;
        stream.write_all(body)?;
        stream.flush()
    }

    /// Completes the WebSocket handshake and runs the protocol loop.
    fn upgrade(&self, reader: BufReader<TcpStream>, head: &RequestHead) -> io::Result<()> {
        let Some(key) = head.header("sec-websocket-key") else {
            let mut stream = reader.into_inner();
            return write_bad_request(&mut stream, "missing Sec-WebSocket-Key");
        };
        let accept = derive_accept_key(key);
        // Anything the client sent after its handshake (a browser may pipeline
        // its first frame immediately) is already in the buffer; hand it to
        // tungstenite rather than dropping it.
        let pending = reader.buffer().to_vec();
        let mut stream = reader.into_inner();
        write!(
            stream,
            "HTTP/1.1 101 Switching Protocols\r\n\
             Upgrade: websocket\r\n\
             Connection: Upgrade\r\n\
             Sec-WebSocket-Accept: {accept}\r\n\
             \r\n"
        )?;
        stream.flush()?;

        let socket = WebSocket::from_partially_read(stream, pending, Role::Server, None);
        self.emit(&ServeEvent::Connected);
        let outcome = self.talk(socket);
        match outcome {
            Ok(()) => self.emit(&ServeEvent::Disconnected),
            Err(e) => self.emit(&ServeEvent::Failed {
                context: "on the provider socket",
                detail: e.to_string(),
            }),
        }
        Ok(())
    }

    /// The protocol loop: one text frame in, one text frame out, until close.
    fn talk(&self, mut socket: WebSocket<TcpStream>) -> Result<(), tungstenite::Error> {
        let mut connection = ConnectionState::default();
        loop {
            let message = match socket.read() {
                Ok(message) => message,
                // Both mean the peer is gone; neither is a failure to report.
                Err(tungstenite::Error::ConnectionClosed | tungstenite::Error::AlreadyClosed) => {
                    return Ok(())
                }
                Err(e) => return Err(e),
            };
            let reply = match message {
                Message::Text(text) => self.answer(&mut connection, text.as_str()),
                // The protocol is text-only (`JSON.parse`/`JSON.stringify`, no
                // binary framing — §2.2). Saying so beats ignoring the frame.
                Message::Binary(_) => Response::error(
                    "malformed-message",
                    "this provider speaks text frames only; binary frames carry no protocol.",
                )
                .to_frame(),
                // tungstenite answers Ping itself and Pong needs no answer;
                // Frame is never produced by `read`.
                Message::Ping(_) | Message::Pong(_) | Message::Frame(_) => continue,
                Message::Close(_) => return Ok(()),
            };
            socket.send(Message::text(reply))?;
        }
    }

    /// Turns one received text frame into the text frame that answers it.
    ///
    /// Total by construction: every branch — including every malformed one —
    /// produces a frame, so a client always learns what happened.
    fn answer(&self, connection: &mut ConnectionState, frame: &str) -> String {
        let request = match parse_request(frame) {
            Ok(request) => request,
            Err(e) => return protocol_error_frame(&e),
        };
        // One lock per request, released before the next read: a poisoned lock
        // means another connection panicked mid-session, which is a mettle bug
        // and not something to paper over — but it must not take the server
        // down either, so it is reported as a protocol error.
        let Ok(mut session) = self.session.lock() else {
            return Response::error(
                "session-unavailable",
                "the serve session failed and can no longer answer; restart `mettle serve`.",
            )
            .to_frame();
        };
        match request {
            Request::Ping => PONG.to_owned(),
            Request::Meta => Response::meta(session.meta()).to_frame(),
            Request::Data => Response::data(connection.join(&session.datum())).to_frame(),
            Request::Eval(eval) => {
                let result = session.eval(&eval.datum_id, &eval.expression);
                Response::eval(eval.id, result).to_frame()
            }
            Request::Click(click) => match session.click(&click.on_click, click.state) {
                Ok(()) => Response::data(connection.join(&session.datum())).to_frame(),
                Err(refused) => Response::error(refused.code, refused.message).to_frame(),
            },
        }
    }
}

/// What one provider socket remembers between requests: which datum it has
/// already shown, so an advance can retire the old one instead of leaving two
/// live evaluator panes on screen.
#[derive(Default, Debug)]
struct ConnectionState {
    shown: Option<String>,
}

impl ConnectionState {
    fn join(&mut self, datum: &SessionDatum) -> DataJoin {
        let mut update = Vec::new();
        if let Some(previous) = self.shown.replace(datum.id.clone()) {
            if previous != datum.id {
                // Forge's own convention (`forgeserver.rkt`): the superseded
                // datum stays in the client's history with its actions and its
                // evaluator switched off, rather than being `exit`ed outright.
                update.push(DatumMeta {
                    id: previous,
                    generator_name: datum.generator_name.clone(),
                    buttons: Vec::new(),
                    evaluator: false,
                });
            }
        }
        DataJoin {
            enter: vec![datum.to_datum()],
            update,
            exit: Vec::new(),
        }
    }
}

fn protocol_error_frame(error: &ProtocolError) -> String {
    Response::error(error.code(), error.to_string()).to_frame()
}

/// A parsed HTTP request head. Only what routing needs — this is not an HTTP
/// implementation.
#[derive(Clone, PartialEq, Eq, Debug)]
struct RequestHead {
    method: String,
    target: String,
    /// `(lowercased name, value)`, in arrival order.
    headers: Vec<(String, String)>,
}

impl RequestHead {
    /// The request target with any query string or fragment removed — the
    /// upstream SPA convention puts the provider port in the query
    /// (`/?1234`), so a target is not a path until it is stripped.
    fn path(&self) -> &str {
        let end = self.target.find(['?', '#']).unwrap_or(self.target.len());
        &self.target[..end]
    }

    fn header(&self, name: &str) -> Option<&str> {
        self.headers
            .iter()
            .find(|(header, _)| header == name)
            .map(|(_, value)| value.as_str())
    }

    /// Whether this is a WebSocket upgrade. `Connection` is a comma-separated
    /// list and browsers send `keep-alive, Upgrade`, so it is searched rather
    /// than compared.
    fn is_websocket_upgrade(&self) -> bool {
        let upgrade_to_websocket = self
            .header("upgrade")
            .is_some_and(|value| value.eq_ignore_ascii_case("websocket"));
        let connection_upgrade = self.header("connection").is_some_and(|value| {
            value
                .split(',')
                .any(|token| token.trim().eq_ignore_ascii_case("upgrade"))
        });
        upgrade_to_websocket && connection_upgrade
    }
}

/// Reads the request line and headers, stopping at the blank line.
///
/// `Ok(None)` means the peer closed before sending anything — a routine event
/// (browser pre-connects, health probes), not an error.
fn read_head(reader: &mut BufReader<TcpStream>) -> io::Result<Option<RequestHead>> {
    let mut budget = MAX_HEAD_BYTES;
    let mut line = String::new();
    if read_line_within(reader, &mut line, &mut budget)? == 0 {
        return Ok(None);
    }
    let mut parts = line.trim_end().split(' ');
    let (Some(method), Some(target)) = (parts.next(), parts.next()) else {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "malformed HTTP request line",
        ));
    };
    let (method, target) = (method.to_owned(), target.to_owned());

    let mut headers = Vec::new();
    loop {
        if read_line_within(reader, &mut line, &mut budget)? == 0 {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "HTTP request head ended before its blank line",
            ));
        }
        let trimmed = line.trim_end_matches(['\r', '\n']);
        if trimmed.is_empty() {
            break;
        }
        if headers.len() == MAX_HEADER_LINES {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "HTTP request head has too many headers",
            ));
        }
        if let Some((name, value)) = trimmed.split_once(':') {
            headers.push((name.trim().to_ascii_lowercase(), value.trim().to_owned()));
        }
    }
    Ok(Some(RequestHead {
        method,
        target,
        headers,
    }))
}

/// One header line, refusing to read past what is left of [`MAX_HEAD_BYTES`].
/// A head that outgrows the budget stops producing lines and the caller's
/// blank-line loop ends in the `UnexpectedEof` above — bounded either way.
fn read_line_within(
    reader: &mut BufReader<TcpStream>,
    line: &mut String,
    budget: &mut usize,
) -> io::Result<usize> {
    line.clear();
    let limit = u64::try_from(*budget).unwrap_or(u64::MAX);
    let read = reader.by_ref().take(limit).read_line(line)?;
    *budget = budget.saturating_sub(read);
    Ok(read)
}

fn write_bad_request(stream: &mut TcpStream, reason: &str) -> io::Result<()> {
    let body = format!("{reason}\n");
    write!(
        stream,
        "HTTP/1.1 400 Bad Request\r\n\
         Content-Type: text/plain; charset=utf-8\r\n\
         Content-Length: {}\r\n\
         Connection: close\r\n\
         \r\n{body}",
        body.len()
    )?;
    stream.flush()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn head(raw: &'static str) -> RequestHead {
        let listener = TcpListener::bind(("127.0.0.1", 0)).expect("bind");
        let addr = listener.local_addr().expect("addr");
        let writer = std::thread::spawn(move || {
            let mut client = TcpStream::connect(addr).expect("connect");
            client.write_all(raw.as_bytes()).expect("write");
            client.flush().expect("flush");
            // Hold the socket open until the reader is done with the head.
            std::thread::sleep(std::time::Duration::from_millis(50));
        });
        let (stream, _) = listener.accept().expect("accept");
        let parsed = read_head(&mut BufReader::new(stream))
            .expect("head reads")
            .expect("a request arrived");
        writer.join().expect("writer thread");
        parsed
    }

    #[test]
    fn a_plain_get_parses_into_method_target_and_headers() {
        let parsed = head("GET /app.js HTTP/1.1\r\nHost: localhost:1234\r\n\r\n");
        assert_eq!(parsed.method, "GET");
        assert_eq!(parsed.path(), "/app.js");
        assert_eq!(parsed.header("host"), Some("localhost:1234"));
        assert!(!parsed.is_websocket_upgrade());
    }

    #[test]
    fn the_upstream_query_string_convention_is_not_part_of_the_path() {
        // `http://localhost:4000?1234` — the stock SPA's provider-port handoff.
        let parsed = head("GET /?1234 HTTP/1.1\r\nHost: localhost\r\n\r\n");
        assert_eq!(parsed.path(), "/");
    }

    #[test]
    fn an_upgrade_is_recognized_through_a_multi_token_connection_header() {
        let parsed = head(
            "GET /ws HTTP/1.1\r\n\
             Host: localhost\r\n\
             Connection: keep-alive, Upgrade\r\n\
             Upgrade: WebSocket\r\n\
             Sec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\n\r\n",
        );
        assert!(parsed.is_websocket_upgrade());
        assert_eq!(
            parsed.header("sec-websocket-key"),
            Some("dGhlIHNhbXBsZSBub25jZQ==")
        );
        // The RFC 6455 example key/accept pair, so a broken handshake shows up
        // here rather than as a browser-side "connection failed". The
        // derivation itself is pinned against the standards' vectors in
        // `crate::handshake`.
        assert_eq!(
            derive_accept_key("dGhlIHNhbXBsZSBub25jZQ=="),
            "s3pPLMBiTxaQ9kYGzzhZRbK+xOo="
        );
    }

    #[test]
    fn an_upgrade_needs_both_headers() {
        let no_connection = head("GET /ws HTTP/1.1\r\nUpgrade: websocket\r\n\r\n");
        assert!(!no_connection.is_websocket_upgrade());
        let no_upgrade = head("GET /ws HTTP/1.1\r\nConnection: Upgrade\r\n\r\n");
        assert!(!no_upgrade.is_websocket_upgrade());
    }

    #[test]
    fn assets_are_looked_up_by_exact_path() {
        let mut assets = StaticAssets::default();
        assets.add("/", "text/html; charset=utf-8", b"<!doctype html>".to_vec());
        assert!(assets.get("/").is_some());
        assert!(assets.get("/missing").is_none());
    }
}
