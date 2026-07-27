//! The placeholder page `mettle serve` shows until mt-075 lands.
//!
//! Deliberately not a design: mt-075 owns the first-party frontend (graph and
//! table views, trace stepper, evaluator pane, and a real visual pass). This
//! page exists so that the Rung-5 surface is *honest* today — a browser pointed
//! at `mettle serve` learns that the server is up, what it is serving, and that
//! the visualizer is not here yet, instead of a blank 404 that looks like a
//! bug. It also carries the provider socket's URL, which is the one fact a
//! `wscat`/DevTools-console user needs to drive the protocol by hand right now.

/// The stub page, naming the model and command being served.
#[must_use]
pub fn stub_index_html(model: &str, command: &str) -> String {
    let model = escape(model);
    let command = escape(command);
    format!(
        "<!doctype html>\n\
         <html lang=\"en\">\n\
         <head>\n\
         <meta charset=\"utf-8\">\n\
         <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n\
         <title>mettle serve — {model}</title>\n\
         <style>\n\
         :root {{ color-scheme: light dark; }}\n\
         body {{ font: 16px/1.6 ui-sans-serif, system-ui, sans-serif; margin: 0; \
         min-height: 100vh; display: grid; place-items: center; }}\n\
         main {{ max-width: 34rem; padding: 2rem; }}\n\
         h1 {{ font-size: 1.25rem; margin: 0 0 1rem; letter-spacing: -0.01em; }}\n\
         dl {{ display: grid; grid-template-columns: auto 1fr; gap: 0.25rem 1rem; margin: 0 0 1.5rem; }}\n\
         dt {{ opacity: 0.6; }}\n\
         dd {{ margin: 0; }}\n\
         code {{ font: 0.9em ui-monospace, monospace; }}\n\
         p {{ opacity: 0.75; }}\n\
         </style>\n\
         </head>\n\
         <body>\n\
         <main>\n\
         <h1>mettle serve is running</h1>\n\
         <dl>\n\
         <dt>model</dt><dd><code>{model}</code></dd>\n\
         <dt>command</dt><dd><code>{command}</code></dd>\n\
         <dt>provider</dt><dd><code id=\"ws\"></code></dd>\n\
         </dl>\n\
         <p>The instance is solved and the provider socket is answering the \
         Sterling protocol (<code>data</code>, <code>eval</code>, \
         <code>click</code>, <code>meta</code>). The visualizer itself — graph \
         and table views, the trace stepper, the evaluator pane — arrives in \
         mt-075 and will be served from this page.</p>\n\
         </main>\n\
         <script>\n\
         document.getElementById('ws').textContent =\n\
         \x20\x20(location.protocol === 'https:' ? 'wss://' : 'ws://') + location.host + '/ws';\n\
         </script>\n\
         </body>\n\
         </html>\n"
    )
}

/// Escapes text for an HTML text node or a double-quoted attribute. A model
/// path is arbitrary user input; it reaches this page and therefore gets
/// escaped, even though the page is served to its own author on loopback.
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
    fn the_stub_names_what_it_serves() {
        let html = stub_index_html("models/river.als", "[0] run crossing for 8");
        assert!(html.starts_with("<!doctype html>"), "{html}");
        assert!(html.contains("models/river.als"), "{html}");
        assert!(html.contains("[0] run crossing for 8"), "{html}");
        assert!(html.contains("mt-075"), "the page must say where the UI is");
    }

    #[test]
    fn model_names_cannot_inject_markup() {
        let html = stub_index_html("<script>alert(1)</script>", "run \"a & b\"");
        assert!(!html.contains("<script>alert"), "{html}");
        assert!(
            html.contains("&lt;script&gt;alert(1)&lt;/script&gt;"),
            "{html}"
        );
        assert!(html.contains("&quot;a &amp; b&quot;"), "{html}");
    }
}
