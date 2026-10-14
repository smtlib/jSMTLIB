package org.smtlib.test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Assume;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.junit.runners.ParameterizedWithNames;
import org.smtlib.SMT;

/** Measures what --pipeline saves: a script of many declarations and assertions is run with and
 *  without it, for each solver in SMT_TEST_SOLVERS that pipelines. The output must be the same,
 *  and pipelining must take at most half the time (about a fifteenth was measured on macOS, so
 *  the bound leaves room for a loaded machine). The timings are printed. */
@RunWith(ParameterizedWithNames.class)
public class PipelinePerformanceTests {

    @Rule public Timeout timeout = new Timeout(3, TimeUnit.MINUTES);

    /** Declarations in the script, each followed by an assertion */
    private static final int DECLARATIONS = 1000;

    private final String solvername;

    public PipelinePerformanceTests(String solvername) {
        this.solvername = solvername;
    }

    @Parameters
    public static Collection<String[]> data() {
        List<String[]> list = new ArrayList<>();
        for (String s : LogicTests.solvers) list.add(new String[]{s});
        return list;
    }

    private static String script(int declarations) {
        StringBuilder sb = new StringBuilder("(set-logic QF_LIA)\n");
        for (int i = 0; i < declarations; i++) {
            sb.append("(declare-fun x").append(i).append(" () Int)\n");
            sb.append("(assert (> x").append(i).append(' ').append(i).append("))\n");
        }
        sb.append("(check-sat)\n");
        return sb.toString();
    }

    /** Output and elapsed nanoseconds of running the script through the command-line tool */
    private Object[] run(String text, boolean pipeline) {
        SMT smt = new SMT();
        smt.smtConfig.props = smt.smtConfig.readProperties();
        ByteArrayOutputStream outBuf = new ByteArrayOutputStream();
        ByteArrayOutputStream errBuf = new ByteArrayOutputStream();
        PrintStream out = new PrintStream(outBuf);
        PrintStream err = new PrintStream(errBuf);
        smt.smtConfig.log.setChannels(out, err);
        smt.smtConfig.stdout = out;
        smt.smtConfig.stderr = err;
        long start = System.nanoTime();
        smt.exec(new String[]{"--solver", solvername, pipeline ? "--pipeline" : "--no-pipeline", "--text", text});
        long elapsed = System.nanoTime() - start;
        smt.cleanup();
        out.flush();
        err.flush();
        return new Object[]{outBuf.toString() + errBuf.toString(), elapsed};
    }

    @Test
    public void pipeliningIsFaster() {
        // Solvers not run as a process, and z3-4.3, whose adapter does not pipeline
        Assume.assumeFalse(solvername.equals("test") || solvername.equals("simplify")
                || solvername.startsWith("z3-4.3") || solvername.startsWith("z3_4_3"));
        // Warm up both paths, so that neither timing includes class loading and compilation
        run(script(50), false);
        run(script(50), true);

        String text = script(DECLARATIONS);
        Object[] sync = run(text, false);
        Object[] pipelined = run(text, true);
        Assert.assertEquals("output with --pipeline", sync[0], pipelined[0]);
        Assert.assertTrue("unexpected output: " + sync[0], ((String)sync[0]).endsWith("sat\n"));
        long syncMillis = (Long)sync[1] / 1_000_000;
        long pipelinedMillis = (Long)pipelined[1] / 1_000_000;
        System.out.println("Pipelining " + (2 * DECLARATIONS + 2) + " commands with " + solvername + ": "
                + pipelinedMillis + " ms instead of " + syncMillis + " ms");
        Assert.assertTrue("pipelined " + pipelinedMillis + " ms vs. " + syncMillis + " ms unpipelined",
                2 * pipelinedMillis < syncMillis);
    }
}
