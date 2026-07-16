import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.parser.CompUtil;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;

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
 * <p>The mt-020 gauge itself is binary, so it never looked at *why* a file was
 * rejected. mt-024's `conform bench` needs exactly that: a per-stage
 * conformance report (parse vs. resolve) plus per-file timing, from one JVM
 * pass over the corpus. Two purely <b>additive</b> fields were added for that
 * ({@code phase} on reject lines, {@code nanos} always) -- every field mt-020
 * already reads (`file`, `ok`) is untouched, so the existing gauge is
 * unaffected.
 *
 * <p>{@code phase} classifies a reject the same way {@code ParseOnlyShim}
 * (mt-013) classifies SYNTAX vs. OTHER -- by inspecting the top frame of the
 * thrown {@link Err}'s stack trace -- just renamed to mettle's own
 * `ResolveError` phase vocabulary ({@code parse} vs. {@code resolve}) so a
 * `bench` disagreement line reads the same on both sides.
 *
 * <p>Usage: {@code java -cp <shim>:<jar> ResolveGaugeShim <file-list>}, one
 * absolute {@code .als} path per line. Output: JSON Lines on stdout, one object
 * per input file, in list order:
 * <pre>
 *   {"file":"...","ok":true,"nanos":123456,"warnings":[{"line":4,"col":7,"message":"..."}]}
 *   {"file":"...","ok":false,"phase":"parse","nanos":123456,"line":12,"col":8,"message":"..."}
 *   {"file":"...","ok":false,"phase":"resolve","nanos":123456,"line":1,"col":1,"message":"..."}
 * </pre>
 * The {@code warnings} array (mt-023) captures the reference's post-{@code
 * resolveAll} warning set for the warning-parity gauge; it appears only on
 * ACCEPT records (warnings are emitted only after success). It is additive:
 * every field mt-020/mt-024 read is untouched.
 * {@code nanos} is this file's own `parseEverything_fromFile` wall time,
 * excluding JVM startup (which happens once, before the first line) -- the
 * per-file half of `bench`'s batch-mode jar timing.
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
        long t0 = System.nanoTime();
        // mt-023: a capturing reporter (the ProbeShim precedent) records each
        // warning's (line, col, message). The reference emits warnings only
        // after resolveAll fully succeeds (resolution-doc §0/§5.2), so a
        // captured warning always coincides with an ACCEPT record. The
        // `warnings` field is purely additive: mt-020/mt-024 readers ignore it.
        final List<ErrorWarning> warns = new ArrayList<>();
        A4Reporter rep = new A4Reporter() {
            @Override public void warning(ErrorWarning w) { warns.add(w); }
        };
        try {
            CompUtil.parseEverything_fromFile(rep, null, path);
            long nanos = System.nanoTime() - t0;
            return "{\"file\":\"" + escape(path) + "\",\"ok\":true,\"nanos\":" + nanos
                + ",\"warnings\":" + warningsJson(warns) + "}";
        } catch (Err e) {
            long nanos = System.nanoTime() - t0;
            Pos pos = e.pos != null ? e.pos : Pos.UNKNOWN;
            return "{\"file\":\"" + escape(path) + "\",\"ok\":false,"
                + "\"phase\":\"" + classify(e) + "\","
                + "\"nanos\":" + nanos + ","
                + "\"line\":" + pos.y + ",\"col\":" + pos.x + ","
                + "\"message\":\"" + escape(e.msg) + "\"}";
        } catch (Throwable t) {
            long nanos = System.nanoTime() - t0;
            String m = t.getMessage();
            return "{\"file\":\"" + escape(path) + "\",\"ok\":false,"
                + "\"phase\":\"resolve\","
                + "\"nanos\":" + nanos + ","
                + "\"line\":0,\"col\":0,"
                + "\"message\":\"unclassified throwable: " + escape(m != null ? m : t.getClass().getName()) + "\"}";
        }
    }

    /**
     * "parse" iff the top stack frame is the lexer, the CUP parser, an inline
     * CUP grammar action, or one of the two inline {@code CompModule}
     * structural checks (module header, empty enum) -- a genuine syntax-phase
     * failure. Everything else is a later-phase module/name/type failure:
     * "resolve". Identical logic to {@code ParseOnlyShim#classify}
     * (mt-013, kept for its own SYNTAX/OTHER vocabulary); duplicated rather
     * than shared because the two shims are independent single-file
     * compilation units (no shared shim library exists, matching this
     * project's zero-dependency shim convention) -- if the two ever drift,
     * `bench`'s parse-stage numbers and the mt-020 gauge's category labels
     * would visibly disagree, which is itself a useful tripwire.
     */
    private static String classify(Err e) {
        StackTraceElement[] st = e.getStackTrace();
        if (st.length == 0) {
            return "resolve";
        }
        String cls = st[0].getClassName();
        String method = st[0].getMethodName();
        if (cls.equals("edu.mit.csail.sdg.parser.CompLexer")
            || cls.equals("edu.mit.csail.sdg.parser.CompParser")
            || cls.startsWith("edu.mit.csail.sdg.parser.CUP$CompParser$actions")) {
            return "parse";
        }
        if (cls.equals("edu.mit.csail.sdg.parser.CompModule")
            && (method.equals("addModelName") || method.equals("addEnum"))) {
            return "parse";
        }
        return "resolve";
    }

    /**
     * Serializes the captured warnings as a JSON array of
     * {@code {"line":Y,"col":X,"message":"..."}} objects, in collection order
     * (the reference's collection order is JVM-incidental — resolution-doc §8 —
     * so the mt-023 gauge compares warning SETS, never order). A warning with
     * an unknown pos serializes with line/col 0.
     */
    private static String warningsJson(List<ErrorWarning> warns) {
        StringBuilder sb = new StringBuilder();
        sb.append('[');
        for (int i = 0; i < warns.size(); i++) {
            ErrorWarning w = warns.get(i);
            Pos p = w.pos != null ? w.pos : Pos.UNKNOWN;
            if (i > 0) {
                sb.append(',');
            }
            sb.append("{\"line\":").append(p.y)
              .append(",\"col\":").append(p.x)
              .append(",\"message\":\"").append(escape(w.msg != null ? w.msg : "")).append("\"}");
        }
        sb.append(']');
        return sb.toString();
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
