//! Hand-rolled GET-only HTTP server for `conform watch` (mt-094).
//!
//! Serves exactly two routes on `127.0.0.1`: the embedded dashboard page at
//! `/`, and its live JSON feed at `/data`. `als-sterling::server` is the idiom
//! this borrows (bounded head read, `Connection: close`, one thread per
//! connection) but is deliberately not a dependency: `als-sterling` exists to
//! speak the Sterling WebSocket protocol, and pulling it in here would drag
//! `tungstenite` along for a server that has no WebSocket side at all (STYLE
//! P1/P2) — a plain "GET one of two things" responsibility is small enough to
//! hand-roll directly on `std::net`.

use std::io::{self, BufRead as _, BufReader, Read as _, Write as _};
use std::net::{TcpListener, TcpStream};
use std::path::PathBuf;

use super::data::assemble;

/// The largest request head the server will read, in bytes — a local dev
/// server still does not read an unbounded byte stream on the word of an
/// unauthenticated client.
const MAX_HEAD_BYTES: usize = 16 * 1024;

/// The largest number of header lines read, for the same reason.
const MAX_HEADER_LINES: usize = 100;

/// The embedded dashboard page — hand-written HTML with inline CSS/JS, no
/// build step, no external reference of any kind (see the offline test in
/// `crate::solve_gauge::watch::server::tests`).
const PAGE: &str = include_str!("../assets/watch.html");

/// Serves the mt-094 progress dashboard for one `solve-gauge
/// --progress-jsonl` run.
#[derive(Debug)]
pub struct WatchServer {
    jsonl_path: PathBuf,
    /// Always set (the bin resolves a default), so `/data` can always
    /// attempt a join — `sweep_baseline::read_prior` already degrades a
    /// missing/malformed file to "no historical times" on its own.
    baseline_path: PathBuf,
}

impl WatchServer {
    #[must_use]
    pub fn new(jsonl_path: PathBuf, baseline_path: PathBuf) -> Self {
        Self {
            jsonl_path,
            baseline_path,
        }
    }

    /// Serves until the process is stopped (Ctrl-C) — mirrors `mettle
    /// serve`; there is no in-band shutdown verb, and one connection per
    /// request costs nothing on loopback at a ~1s poll interval.
    pub fn accept_loop(&self, listener: &TcpListener) {
        std::thread::scope(|scope| {
            for incoming in listener.incoming().flatten() {
                scope.spawn(move || {
                    let _ = self.handle(incoming);
                });
            }
        });
    }

    fn handle(&self, stream: TcpStream) -> io::Result<()> {
        let mut reader = BufReader::new(stream);
        let Some(head) = read_head(&mut reader)? else {
            // A connection opened and closed without sending a request (a
            // browser pre-connect, a health probe). Nothing to answer.
            return Ok(());
        };
        let mut stream = reader.into_inner();
        if head.method != "GET" {
            return respond(&mut stream, 405, "Method Not Allowed", TEXT, b"");
        }
        match head.path() {
            "/" => respond(&mut stream, 200, "OK", HTML, PAGE.as_bytes()),
            "/data" => {
                let body = assemble(&self.jsonl_path, &self.baseline_path);
                respond(&mut stream, 200, "OK", JSON, body.as_bytes())
            }
            _ => respond(&mut stream, 404, "Not Found", TEXT, b"not found\n"),
        }
    }
}

const HTML: &str = "text/html; charset=utf-8";
const JSON: &str = "application/json";
const TEXT: &str = "text/plain; charset=utf-8";

/// A parsed HTTP request line — only what routing needs (method + path);
/// headers are read (to find the blank line that ends the head) but not kept.
#[derive(Debug, Clone, PartialEq, Eq)]
struct RequestHead {
    method: String,
    target: String,
}

impl RequestHead {
    /// The request target with any query string or fragment stripped.
    fn path(&self) -> &str {
        let end = self.target.find(['?', '#']).unwrap_or(self.target.len());
        &self.target[..end]
    }
}

/// Reads the request line and headers, stopping at the blank line.
///
/// `Ok(None)` means the peer closed before sending anything — a routine
/// event, not an error.
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
    let head = RequestHead {
        method: method.to_owned(),
        target: target.to_owned(),
    };

    let mut header_lines = 0usize;
    loop {
        if read_line_within(reader, &mut line, &mut budget)? == 0 {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "HTTP request head ended before its blank line",
            ));
        }
        if line.trim_end_matches(['\r', '\n']).is_empty() {
            break;
        }
        header_lines += 1;
        if header_lines == MAX_HEADER_LINES {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "HTTP request head has too many headers",
            ));
        }
    }
    Ok(Some(head))
}

/// One header line, refusing to read past what is left of [`MAX_HEAD_BYTES`].
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

fn respond(
    stream: &mut TcpStream,
    status: u16,
    reason: &str,
    content_type: &str,
    body: &[u8],
) -> io::Result<()> {
    // `Connection: close` throughout: without keep-alive there is no
    // pipelining to get wrong, and one connection per ~1s poll is free on
    // loopback.
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

#[cfg(test)]
#[allow(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "test fixtures assert on known-good values"
)]
mod tests {
    use super::*;

    /// SVG's XML namespace — an identifier `createElementNS` compares, never
    /// a resource anything fetches (same carve-out als-sterling's frontend
    /// offline test uses).
    const SVG_NAMESPACE: &str = "http://www.w3.org/2000/svg";

    #[test]
    fn the_embedded_page_references_nothing_off_this_origin() {
        let body = PAGE.replace(SVG_NAMESPACE, "");
        for forbidden in ["http://", "https://", "//cdn", "@import url("] {
            assert!(
                !body.contains(forbidden),
                "watch.html references {forbidden}"
            );
        }
    }

    #[test]
    fn the_embedded_page_is_a_well_formed_html_document() {
        assert!(PAGE.trim_start().starts_with("<!doctype html>"));
        assert!(PAGE.contains("<title>"));
        assert!(PAGE.contains("/data"), "the page must poll /data");
    }

    fn request(tag: &str, raw: &'static str) -> (u16, String, Vec<u8>) {
        let listener = TcpListener::bind(("127.0.0.1", 0)).expect("bind");
        let addr = listener.local_addr().expect("addr");
        let writer = std::thread::spawn(move || {
            let mut client = TcpStream::connect(addr).expect("connect");
            client.write_all(raw.as_bytes()).expect("write");
            client.flush().expect("flush");
            let mut resp = Vec::new();
            client.read_to_end(&mut resp).expect("read response");
            resp
        });
        let (stream, _) = listener.accept().expect("accept");
        // A unique dir per test so parallel `cargo test` threads never race
        // each other's create/remove of the same path.
        let dir = std::env::temp_dir().join(format!("als-watch-srv-{tag}-{}", std::process::id()));
        std::fs::remove_dir_all(&dir).ok();
        std::fs::create_dir_all(&dir).ok();
        let server = WatchServer::new(dir.join("progress.jsonl"), dir.join("baseline.json"));
        server.handle(stream).expect("handle");
        let resp = writer.join().expect("writer thread");
        let text = String::from_utf8_lossy(&resp).into_owned();
        let (head, body) = text.split_once("\r\n\r\n").expect("head/body split");
        let status: u16 = head
            .lines()
            .next()
            .and_then(|l| l.split_whitespace().nth(1))
            .and_then(|s| s.parse().ok())
            .expect("status line");
        std::fs::remove_dir_all(&dir).ok();
        (status, head.to_owned(), body.as_bytes().to_vec())
    }

    #[test]
    fn root_serves_the_dashboard_page() {
        let (status, head, body) = request("root", "GET / HTTP/1.1\r\nHost: localhost\r\n\r\n");
        assert_eq!(status, 200);
        assert!(head.contains("text/html"));
        assert!(String::from_utf8_lossy(&body).starts_with("<!doctype html>"));
    }

    #[test]
    fn data_serves_a_waiting_payload_before_any_run() {
        let (status, head, body) = request("data", "GET /data HTTP/1.1\r\nHost: localhost\r\n\r\n");
        assert_eq!(status, 200);
        assert!(head.contains("application/json"));
        let v: serde_json::Value = serde_json::from_slice(&body).unwrap();
        assert_eq!(v["waiting"], serde_json::json!(true));
    }

    #[test]
    fn an_unknown_path_is_404() {
        let (status, _, _) = request("notfound", "GET /nope HTTP/1.1\r\nHost: localhost\r\n\r\n");
        assert_eq!(status, 404);
    }

    #[test]
    fn a_non_get_method_is_405() {
        let (status, _, _) = request(
            "badmethod",
            "POST /data HTTP/1.1\r\nHost: localhost\r\n\r\n",
        );
        assert_eq!(status, 405);
    }
}
