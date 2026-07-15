import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;
import kodkod.engine.satlab.SATFactory;

import java.util.List;

/**
 * Minimal, dependency-free JVM shim that drives the reference Alloy jar
 * through the {@code A4Options} API -- never the {@code exec} CLI, whose
 * {@code -y}/{@code --ymmetry} flag is a confirmed no-op in 6.2.0 (see
 * docs/reference/alloy6-reference.md sec 3(c)). One JVM launch processes
 * every command in the given file, because JVM startup is the expensive
 * part.
 *
 * <p>Usage:
 * <pre>
 *   java -cp &lt;shim-classes&gt;:org.alloytools.alloy.dist.jar OracleShim \
 *        &lt;model.als&gt; &lt;symmetry:int&gt; &lt;noOverflow:true|false&gt; &lt;solver&gt; &lt;enumCap:int&gt;
 * </pre>
 * {@code enumCap}: {@code 0} = verdict only (no enumeration beyond the
 * first solve); {@code N > 0} = enumerate up to {@code N} instances;
 * {@code -1} = exhaustive enumeration (stop only at UNSAT).
 *
 * <p>Output: JSON Lines on stdout, one object per command, in ascending
 * command-index order:
 * <pre>
 *   {"index":0,"label":"show","check":false,"expects":-1,
 *    "verdict":"SAT","instance_count":null}
 * </pre>
 * A command whose translation/solve throws reports a structured error
 * instead of a verdict:
 * <pre>
 *   {"index":1,"label":"broken","check":true,"expects":-1,
 *    "error":{"kind":"command","message":"..."}}
 * </pre>
 * A file that fails to parse before any command runs prints exactly one
 * line and nothing else:
 * <pre>
 *   {"error":{"kind":"parse","message":"..."}}
 * </pre>
 * Exit code is {@code 0} whenever the shim produced structured output
 * (including per-command errors); {@code 2} for a file-level parse
 * failure or bad usage. There is never a raw stack trace on stdout --
 * the Rust side only ever needs to parse JSON lines.
 */
public final class OracleShim {

    private OracleShim() {}

    public static void main(String[] args) {
        if (args.length != 5) {
            System.out.println(jsonError("usage", "expected 5 args: <model.als> <symmetry> <noOverflow> <solver> <enumCap>, got " + args.length));
            System.exit(2);
            return;
        }

        String file = args[0];
        int symmetry;
        int enumCap;
        try {
            symmetry = Integer.parseInt(args[1]);
            enumCap = Integer.parseInt(args[4]);
        } catch (NumberFormatException e) {
            System.out.println(jsonError("usage", "symmetry and enumCap must be integers: " + e.getMessage()));
            System.exit(2);
            return;
        }
        boolean noOverflow = Boolean.parseBoolean(args[2]);
        String solverName = args[3];

        CompModule world;
        try {
            world = CompUtil.parseEverything_fromFile(A4Reporter.NOP, null, file);
        } catch (Throwable t) {
            System.out.println(jsonError("parse", messageOf(t)));
            System.exit(2);
            return;
        }

        java.util.Optional<SATFactory> solver = SATFactory.find(solverName);
        if (solver.isEmpty()) {
            // Never silently substitute another solver for a typo'd name --
            // a conformance verdict must come from the solver that was asked for.
            System.out.println(jsonError("usage", "unknown solver: " + solverName));
            System.exit(2);
            return;
        }

        A4Options opts = new A4Options();
        opts.symmetry = symmetry;
        opts.noOverflow = noOverflow;
        opts.solver = solver.get();

        List<Command> cmds = world.getAllCommands();
        for (int i = 0; i < cmds.size(); i++) {
            System.out.println(runOne(world, cmds.get(i), i, opts, enumCap));
        }
    }

    /** Runs one command and renders its one-line JSON result. Never throws. */
    private static String runOne(CompModule world, Command cmd, int index, A4Options opts, int enumCap) {
        StringBuilder sb = new StringBuilder();
        sb.append('{');
        sb.append("\"index\":").append(index).append(',');
        sb.append("\"label\":\"").append(escape(cmd.label)).append("\",");
        sb.append("\"check\":").append(cmd.check).append(',');
        sb.append("\"expects\":").append(cmd.expects).append(',');
        try {
            A4Solution sol = TranslateAlloyToKodkod.execute_command(A4Reporter.NOP, world.getAllReachableSigs(), cmd, opts);
            boolean sat = sol.satisfiable();
            Integer count = enumCap == 0 ? null : countInstances(sol, enumCap);
            sb.append("\"verdict\":\"").append(sat ? "SAT" : "UNSAT").append("\",");
            sb.append("\"instance_count\":").append(count == null ? "null" : count.toString());
        } catch (Throwable t) {
            sb.append("\"error\":{\"kind\":\"command\",\"message\":\"").append(escape(messageOf(t))).append("\"}");
        }
        sb.append('}');
        return sb.toString();
    }

    /** Enumerates satisfying assignments up to {@code cap} ({@code -1} = exhaustive). */
    private static int countInstances(A4Solution first, int cap) throws Exception {
        int count = 0;
        A4Solution cur = first;
        while (cur.satisfiable()) {
            count++;
            if (cap > 0 && count >= cap) {
                break;
            }
            cur = cur.next();
        }
        return count;
    }

    private static String messageOf(Throwable t) {
        String m = t.getMessage();
        return m != null ? m : t.getClass().getName();
    }

    private static String jsonError(String kind, String message) {
        return "{\"error\":{\"kind\":\"" + kind + "\",\"message\":\"" + escape(message) + "\"}}";
    }

    /** Hand-rolled JSON string escaping -- deliberately no JSON library dependency. */
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
