import org.smtlib.SMT;

import java.io.OutputStream;
import java.io.PrintStream;
import java.nio.file.Files;
import java.nio.file.Paths;

/**
 * Compares two ways of running the same SMT-LIB script N times against a solver:
 *   A) a fresh SolverProcess (new solver subprocess) per script, ending with (exit)
 *   B) one long-lived SolverProcess, scripts separated by (reset)
 *
 * Both approaches drive the real, unmodified org.smtlib.SMT class -- the same code
 * path the jSMTLIB CLI uses -- so the only thing that varies between A and B is
 * whether a fresh solver subprocess is started for each script or not. Both run
 * inside the same warm JVM, so JIT warmup affects each equally and isn't part of
 * what's being measured.
 *
 * Usage: java -cp jSMTLIB.jar:. TimingExperiment <solverName> <N> <scriptFile> [relax]
 */
public class TimingExperiment {

    public static void main(String[] args) throws Exception {
        if (args.length < 3) {
            System.err.println("Usage: TimingExperiment <solverName> <N> <scriptFile> [relax]");
            System.exit(2);
        }
        String solverName = args[0];
        int n = Integer.parseInt(args[1]);
        String script = new String(Files.readAllBytes(Paths.get(args[2])));
        boolean relax = args.length > 3 && Boolean.parseBoolean(args[3]);

        PrintStream sink = new PrintStream(OutputStream.nullOutputStream());

        // ---- Approach A: fresh solver subprocess per script. No explicit (exit) is
        // sent -- exec()'s own finally-block cleanup() already force-exits the solver
        // once the script's commands are exhausted, which is what actually tears down
        // the process either way; sending (exit) too would only add a second, redundant
        // teardown path and would make the last captured response "success" (from the
        // exit command) instead of the check-sat result this is meant to sanity-check. ----
        int errorsA = 0;
        String lastResponseA = null;
        long startA = System.nanoTime();
        for (int i = 0; i < n; i++) {
            SMT smt = newSmt(solverName, relax, sink);
            smt.smtConfig.text = script;
            int rc = smt.exec();
            if (rc != 0) errorsA++;
            if (smt.lastResponse != null) lastResponseA = smt.lastResponse.toString();
        }
        long elapsedA = System.nanoTime() - startA;

        // ---- Approach B: one solver subprocess, N scripts separated by (reset).
        // No (reset) after the final iteration, so the last captured response is the
        // final check-sat's, not a trailing reset's "success" -- same reasoning as
        // approach A skipping (exit). ----
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < n; i++) {
            sb.append(script);
            if (i < n - 1) sb.append("\n(reset)\n");
        }
        SMT smtB = newSmt(solverName, relax, sink);
        smtB.smtConfig.text = sb.toString();
        long startB = System.nanoTime();
        int rcB = smtB.exec();
        long elapsedB = System.nanoTime() - startB;
        String lastResponseB = smtB.lastResponse == null ? null : smtB.lastResponse.toString();

        double msA = elapsedA / 1e6;
        double msB = elapsedB / 1e6;
        System.out.printf(
            "solver=%-14s n=%-6d perProcess_total_ms=%10.1f perProcess_per_iter_ms=%8.3f errorsA=%d lastRespA=%s"
            + "  ||  reset_total_ms=%10.1f reset_per_iter_ms=%8.3f rcB=%d lastRespB=%s%n",
            solverName, n, msA, msA / n, errorsA, lastResponseA,
            msB, msB / n, rcB, lastResponseB);
    }

    private static SMT newSmt(String solverName, boolean relax, PrintStream sink) {
        SMT smt = new SMT();
        smt.props = smt.readProperties();
        smt.smtConfig.solvername = solverName;
        smt.smtConfig.relax = relax;
        smt.smtConfig.stdout = sink;
        smt.smtConfig.stderr = sink;
        smt.smtConfig.log.out = sink;
        smt.smtConfig.log.diag = sink;
        return smt;
    }
}
