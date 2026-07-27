//! The first-party frontend `mettle serve` ships (mt-075), embedded at compile
//! time.
//!
//! ADR-0016 Resolution 1: mettle writes its own browser frontend against the
//! pinned wire protocol rather than embedding anything from the Sterling
//! lineage. It is hand-written ES modules and one stylesheet — **no build
//! toolchain, no bundler, and no external reference of any kind**, so the page
//! renders identically with the machine offline, which is the only way a
//! single static binary can promise a visualizer at all.
//!
//! The files live in `crates/als-sterling/assets/` and are `include_str!`d
//! here: they are documents, not Rust modules, and keeping them as real files
//! is what lets them be edited (and diffed) as the JavaScript and CSS they
//! are. [`ASSETS`] is the whole served surface except the index, which is
//! [`index_html`] because it interpolates the model and command being served —
//! the two facts the page can state before the socket is even open.

/// The content type of every HTML response.
pub const HTML: &str = "text/html; charset=utf-8";

/// One embedded file, ready to register with [`crate::StaticAssets`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct FrontendAsset {
    /// The absolute request path it answers.
    pub path: &'static str,
    /// Its `Content-Type` header.
    pub content_type: &'static str,
    /// The file itself.
    pub body: &'static str,
}

/// The index's template, before the model and command are filled in.
const SHELL: &str = include_str!("../assets/index.html");

/// The `{{…}}` slot the served model path fills.
const MODEL_SLOT: &str = "{{model}}";

/// The `{{…}}` slot the served command fills.
const COMMAND_SLOT: &str = "{{command}}";

/// Every file the app loads after the index.
///
/// A flat table rather than a directory walk: the set is small, fixed, and
/// checked by the compiler, and a server that can only serve what is listed
/// here has no path-traversal surface to get wrong.
pub const ASSETS: &[FrontendAsset] = &[
    FrontendAsset {
        path: "/app.css",
        content_type: "text/css; charset=utf-8",
        body: include_str!("../assets/app.css"),
    },
    FrontendAsset {
        path: "/app.js",
        content_type: JAVASCRIPT,
        body: include_str!("../assets/app.js"),
    },
    FrontendAsset {
        path: "/protocol.js",
        content_type: JAVASCRIPT,
        body: include_str!("../assets/protocol.js"),
    },
    FrontendAsset {
        path: "/instance.js",
        content_type: JAVASCRIPT,
        body: include_str!("../assets/instance.js"),
    },
    FrontendAsset {
        path: "/tables.js",
        content_type: JAVASCRIPT,
        body: include_str!("../assets/tables.js"),
    },
];

/// The type a browser must see to run a file as an ES module.
const JAVASCRIPT: &str = "text/javascript; charset=utf-8";

/// The app shell, naming the model and command this server was started on.
///
/// Both are arbitrary user input reaching an HTML document, so both are
/// escaped — the page is served to its own author on loopback, and it is still
/// not a place to learn that lesson twice.
#[must_use]
pub fn index_html(model: &str, command: &str) -> String {
    debug_assert!(
        SHELL.contains(MODEL_SLOT) && SHELL.contains(COMMAND_SLOT),
        "the app shell lost one of its template slots"
    );
    SHELL
        .replace(MODEL_SLOT, &escape(model))
        .replace(COMMAND_SLOT, &escape(command))
}

/// Escapes text for an HTML text node or a double-quoted attribute.
fn escape(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for ch in text.chars() {
        match ch {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&#39;"),
            other => out.push(other),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_shell_names_what_it_serves_and_loads_the_app() {
        let html = index_html("models/river.als", "[0] run crossing for 8");
        assert!(html.starts_with("<!doctype html>"), "{html}");
        assert!(html.contains("models/river.als"), "{html}");
        assert!(html.contains("[0] run crossing for 8"), "{html}");
        assert!(
            html.contains(r#"<script type="module" src="/app.js">"#),
            "{html}"
        );
        assert!(
            !html.contains("{{"),
            "every template slot is filled: {html}"
        );
    }

    #[test]
    fn model_names_cannot_inject_markup() {
        let html = index_html("<script>alert(1)</script>", "run \"a & b\"");
        assert!(!html.contains("<script>alert"), "{html}");
        assert!(
            html.contains("&lt;script&gt;alert(1)&lt;/script&gt;"),
            "{html}"
        );
        assert!(html.contains("&quot;a &amp; b&quot;"), "{html}");
    }

    #[test]
    fn every_asset_the_shell_references_is_embedded() {
        let html = index_html("m.als", "run p");
        for asset in ASSETS {
            assert!(!asset.body.is_empty(), "{} is empty", asset.path);
        }
        // The two the page loads directly; the rest are imported by `app.js`,
        // which the module graph below covers.
        for path in ["/app.css", "/app.js"] {
            assert!(html.contains(path), "the shell must load {path}: {html}");
        }
        // A relative `import` that names a file the server does not serve is a
        // blank page in the browser and nothing at all in `cargo test`, which
        // is exactly the failure this closes: every module the graph mentions
        // has to be in the table above.
        for asset in ASSETS {
            for import in ["./instance.js", "./protocol.js", "./tables.js"] {
                let served = import.trim_start_matches('.');
                assert!(
                    !asset.body.contains(import) || ASSETS.iter().any(|a| a.path == served),
                    "{} imports {import}, which is not embedded",
                    asset.path
                );
            }
        }
    }

    #[test]
    fn the_frontend_references_nothing_off_this_origin() {
        // The whole point of an embedded frontend: a machine with no network
        // must render the same page. A CDN font or script would be invisible
        // in review and fatal offline.
        for asset in ASSETS {
            for forbidden in ["http://", "https://", "//cdn", "@import url("] {
                assert!(
                    !asset.body.contains(forbidden),
                    "{} references {forbidden}",
                    asset.path
                );
            }
        }
        assert!(
            !SHELL.contains("http://"),
            "the shell references an outside origin"
        );
        assert!(
            !SHELL.contains("https://"),
            "the shell references an outside origin"
        );
    }
}
