import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.parser.CompUtil;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;

/**
 * Batch resolve/typecheck verdict shim for the mt-020 differential gauge
 * (docs/reference/alloy4fun-resolve-pass.md). Emits the reference's binary
 * post-{@code resolveAll} verdict — ACCEPT (returns) vs REJECT (throws) — for
 * every {@code .als} file in a list, one JVM for the whole batch.
 *
 * <p>Unlike {@code ParseOnlyShim} (mt-013), which calls
 * {@link CompUtil#parseEverything_fromString} (it writes the code to a
 * <em>temp</em> file, so a relative {@code open ../sibling} resolves from the
 * temp directory and spuriously fails), this shim calls the real-path entry
 * {@link CompUtil#parseEverything_fromFile}{@code (rep, null, path)} — the same
 * 3-arg {@code resolveAll} pipeline (resolution-doc §0) but rooted at the file's
 * actual directory, so multi-file corpus models resolve their sibling {@code
 * open}s correctly. For self-contained single-file models (the 150,891
 * alloy4fun codes, which only {@code open util/*} — served from the jar's
 * embedded fallback) the two entries are verdict-equivalent; for the 167-file
 * corpus (real sibling opens) only this one is correct.
 *
 * <p>The mt-020 gauge is binary, so no syntax-vs-resolve classification is
 * needed (contrast {@code ParseOnlyShim}); the {@code message}/position fields
 * are emitted only to aid triage of disagreements.
 *
 * <p>Usage: {@code java -cp <shim>:<jar> ResolveGaugeShim <file-list>}, one
 * absolute {@code .als} path per line. Output: JSON Lines on stdout, one object
 * per input file, in list order:
 * <pre>
 *   {"file":"...","ok":true}
 *   {"file":"...","ok":false,"line":12,"col":8,"message":"..."}
 * </pre>
 * Never throws; a genuinely unexpected {@link Throwable} is reported distinctly.
 */
public final class ResolveGaugeShim {

    private ResolveGaugeShim() {}

    public static void main(String[] args) throws Exception {
        if (args.length != 1) {
            System.err.println("usage: ResolveGaugeShim <file-list>");
            System.exit(2);
            return;
        }
        PrintStream out = new PrintStream(System.out, false, "UTF-8");
        try (BufferedReader r = new BufferedReader(new FileReader(args[0], StandardCharsets.UTF_8))) {
            String path;
            while ((path = r.readLine()) != null) {
                path = path.trim();
                if (path.isEmpty()) {
                    continue;
                }
                out.println(runOne(path));
            }
        }
        out.flush();
    }

    private static String runOne(String path) {
        try {
            CompUtil.parseEverything_fromFile(A4Reporter.NOP, null, path);
            return "{\"file\":\"" + escape(path) + "\",\"ok\":true}";
        } catch (Err e) {
            Pos pos = e.pos != null ? e.pos : Pos.UNKNOWN;
            return "{\"file\":\"" + escape(path) + "\",\"ok\":false,"
                + "\"line\":" + pos.y + ",\"col\":" + pos.x + ","
                + "\"message\":\"" + escape(e.msg) + "\"}";
        } catch (Throwable t) {
            String m = t.getMessage();
            return "{\"file\":\"" + escape(path) + "\",\"ok\":false,"
                + "\"line\":0,\"col\":0,"
                + "\"message\":\"unclassified throwable: " + escape(m != null ? m : t.getClass().getName()) + "\"}";
        }
    }

    /** Hand-rolled JSON string escaping — no JSON-library dependency (matches the other shims). */
    private static String escape(String s) {
        if (s == null) {
            return "";
        }
        StringBuilder out = new StringBuilder(s.length() + 8);
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            switch (c) {
                case '"':  out.append("\\\""); break;
                case '\\': out.append("\\\\"); break;
                case '\n': out.append("\\n"); break;
                case '\r': out.append("\\r"); break;
                case '\t': out.append("\\t"); break;
                default:
                    if (c < 0x20) {
                        out.append(String.format("\\u%04x", (int) c));
                    } else {
                        out.append(c);
                    }
            }
        }
        return out.toString();
    }
}
