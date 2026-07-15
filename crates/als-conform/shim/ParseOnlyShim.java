import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;

/**
 * Syntax-only differential-testing shim for mt-013 (Alloy4Fun error-quality
 * pass, docs/reference/alloy4fun-error-pass.md). Kept separate from
 * {@code OracleShim} (mt-006) because its job is unrelated: no solving, no
 * symmetry/overflow/solver options, batch-of-many-files-per-JVM instead of
 * one-file-per-JVM, and it needs a syntax-vs-semantics classifier that
 * {@code OracleShim} has no reason to carry.
 *
 * <p>The reference jar has no public "syntax only, no name resolution" entry
 * point: {@link CompUtil#parseEverything_fromFile} both parses <em>and</em>
 * resolves names/opens/types in one pass, so a plain try/catch around it
 * conflates real grammar/lex errors with later-phase semantic errors (a
 * missing {@code open} target, an unresolved name, a type mismatch) that
 * mettle's Rung-1 parser intentionally does not attempt (docs/reference/
 * alloy6-grammar.md sec 4: only the reference's inline grammar-action
 * checks are in scope; name/type resolution is Rung 2+). This shim
 * disambiguates by inspecting the top frame of the thrown {@link Err}'s
 * stack trace, verified empirically (see the report's classifier section):
 * <ul>
 *   <li>{@code CompLexer}/{@code CompParser} (the generated JFlex/CUP
 *       scanner and parser) and {@code CUP$CompParser$actions} (inline CUP
 *       grammar actions, where the reference's own parse-time semantic
 *       checks -- scope-on-univ, growing-int-scope, exactly-redundant,
 *       defined-disjoint, {@code $}-in-name, empty-enum's sibling checks,
 *       etc. -- live) are genuine syntax-phase failures: {@code SYNTAX}.
 *   <li>{@code CompModule#addModelName}/{@code #addEnum} are also inline,
 *       parse-time checks (module-header-not-first, empty-enum) mettle
 *       reproduces exactly: {@code SYNTAX}.
 *   <li>Everything else -- {@code CompModule#hint} (name resolution),
 *       {@code #resolveParams} (open argument-count), {@code #dup}
 *       (duplicate-declaration, a whole-module symbol table check),
 *       {@code CompUtil#parseEverything_fromFile} (open target file
 *       lookup), any {@code ErrorType} -- is a later-phase resolution/type
 *       error outside Rung 1's contract: {@code OTHER}. A file whose only
 *       failure is {@code OTHER} counts as "syntactically OK" for this
 *       comparison, matching mettle's own behavior (opens are inert
 *       paragraphs at parse time; no name/type resolution yet).
 * </ul>
 *
 * <p>Usage:
 * <pre>
 *   java -cp &lt;shim-classes&gt;:org.alloytools.alloy.dist.jar ParseOnlyShim &lt;file-list&gt;
 * </pre>
 * {@code file-list}: a text file with one absolute {@code .als} path per
 * line. One JVM processes every listed file (JVM startup dominates cost;
 * see the shim's module doc in {@code OracleShim.java}).
 *
 * <p>Output: JSON Lines on stdout, one object per input file, in the same
 * order as the list:
 * <pre>
 *   {"file":"...","ok":true}
 *   {"file":"...","ok":false,"category":"syntax","line":12,"col":8,"line2":12,"col2":12,"message":"..."}
 *   {"file":"...","ok":false,"category":"other","line":1,"col":1,"line2":1,"col2":1,"message":"..."}
 * </pre>
 * Never throws; a file this shim itself can't read is reported as its own
 * {@code category:"shim"} line rather than aborting the batch.
 */
public final class ParseOnlyShim {

    private ParseOnlyShim() {}

    public static void main(String[] args) throws Exception {
        if (args.length != 1) {
            System.err.println("usage: ParseOnlyShim <file-list>");
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
        String code;
        try {
            code = new String(Files.readAllBytes(Paths.get(path)), StandardCharsets.UTF_8);
        } catch (Exception e) {
            return obj(path, "false", "\"shim\"", 0, 0, 0, 0, "could not read file: " + messageOf(e));
        }
        try {
            CompModule m = CompUtil.parseEverything_fromString(A4Reporter.NOP, code);
            return "{\"file\":\"" + escape(path) + "\",\"ok\":true}";
        } catch (Err e) {
            String category = classify(e);
            Pos pos = e.pos != null ? e.pos : Pos.UNKNOWN;
            return obj(path, "false", "\"" + category + "\"", pos.y, pos.x, pos.y2, pos.x2, e.msg);
        } catch (Throwable t) {
            // Anything else (StackOverflowError on pathological input, etc.)
            // is a shim-classification miss, not a verdict -- surface it
            // distinctly rather than guessing.
            return obj(path, "false", "\"shim\"", 0, 0, 0, 0, "unclassified throwable: " + messageOf(t));
        }
    }

    /**
     * SYNTAX iff the top stack frame is the lexer, the CUP parser, an
     * inline CUP grammar action, or one of the two inline
     * {@code CompModule} structural checks (module header, empty enum).
     * Everything else is a later-phase resolution/type error: OTHER.
     */
    private static String classify(Err e) {
        StackTraceElement[] st = e.getStackTrace();
        if (st.length == 0) {
            return "other";
        }
        String cls = st[0].getClassName();
        String method = st[0].getMethodName();
        if (cls.equals("edu.mit.csail.sdg.parser.CompLexer")
            || cls.equals("edu.mit.csail.sdg.parser.CompParser")
            || cls.startsWith("edu.mit.csail.sdg.parser.CUP$CompParser$actions")) {
            return "syntax";
        }
        if (cls.equals("edu.mit.csail.sdg.parser.CompModule")
            && (method.equals("addModelName") || method.equals("addEnum"))) {
            return "syntax";
        }
        return "other";
    }

    private static String messageOf(Throwable t) {
        String m = t.getMessage();
        return m != null ? m : t.getClass().getName();
    }

    private static String obj(String path, String ok, String category, int line, int col, int line2, int col2, String message) {
        StringBuilder sb = new StringBuilder();
        sb.append("{\"file\":\"").append(escape(path)).append("\",");
        sb.append("\"ok\":").append(ok).append(',');
        sb.append("\"category\":").append(category).append(',');
        sb.append("\"line\":").append(line).append(',');
        sb.append("\"col\":").append(col).append(',');
        sb.append("\"line2\":").append(line2).append(',');
        sb.append("\"col2\":").append(col2).append(',');
        sb.append("\"message\":\"").append(escape(message)).append("\"}");
        return sb.toString();
    }

    /** Hand-rolled JSON string escaping -- deliberately no JSON library dependency (matches OracleShim). */
    private static String escape(String s) {
        if (s == null) {
            return "";
        }
        StringBuilder out = new StringBuilder(s.length() + 8);
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            switch (c) {
                case '"':
                    out.append("\\\"");
                    break;
                case '\\':
                    out.append("\\\\");
                    break;
                case '\n':
                    out.append("\\n");
                    break;
                case '\r':
                    out.append("\\r");
                    break;
                case '\t':
                    out.append("\\t");
                    break;
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
