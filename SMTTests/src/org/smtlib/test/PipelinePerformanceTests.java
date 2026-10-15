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
import org.smtlib.ICommand;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.SMT;

/** Measures what --pipeline saves: a script of many declarations and assertions is run with and
 *  without it, through the command-line tool and through the library's IScript.execute, for each solver in SMT_TEST_SOLVERS that pipelines. The output must be the same,
 *  and pipelining must take at most half the time (about a fifteenth was measured on macOS, so
 *  the bound leaves room for a loaded machine). The timings are printed when the speedup is
 *  under REPORTED_SPEEDUP, or always if the environment variable SMT_TEST_VERBOSE_TIMING is set. */
@RunWith(ParameterizedWithNames.class)
public class PipelinePerformanceTests {

    @Rule public Timeout timeout = new Timeout(3, TimeUnit.MINUTES);

    /** Declarations in the script, each followed by an assertion */
    private static final int DECLARATIONS = 1000;

    /** Speedups below this are printed even without SMT_TEST_VERBOSE_TIMING */
    private static final int REPORTED_SPEEDUP = 40;

    private static final boolean VERBOSE_TIMING = System.getenv("SMT_TEST_VERBOSE_TIMING") != null;

    /** Prints a timing, if verbose or the speedup is small */
    static void reportTiming(String message, long pipelinedMillis, long syncMillis) {
        if (VERBOSE_TIMING || REPORTED_SPEEDUP * pipelinedMillis > syncMillis) {
            System.out.println(message + ": " + pipelinedMillis + " ms instead of " + syncMillis + " ms");
        }
    }

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
        // QF_UF, which every solver supports
        StringBuilder sb = new StringBuilder("(set-logic QF_UF)\n");
        for (int i = 0; i < declarations; i++) {
            sb.append("(declare-fun p").append(i).append(" () Bool)\n");
            sb.append("(assert (or p").append(i).append(" (not p").append(i / 2).append(")))\n");
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
        return new Object[]{(outBuf.toString() + errBuf.toString()).replace("\r\n", "\n"), elapsed};
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
        reportTiming("Pipelining " + (2 * DECLARATIONS + 2) + " commands with " + solvername,
                pipelinedMillis, syncMillis);
        Assert.assertTrue("pipelined " + pipelinedMillis + " ms vs. " + syncMillis + " ms unpipelined",
                2 * pipelinedMillis < syncMillis);
    }

    /** Response and elapsed nanoseconds of executing the script with a new solver, with or without
     *  SMT.Configuration.pipeline */
    private Object[] execute(String text, boolean pipeline) throws Exception {
        SMT smt = new SMT();
        SMT.Configuration config = smt.smtConfig;
        config.props = config.readProperties();
        config.pipeline = pipeline;
        ISolver solver = config.createSolver(solvername, smt.resolveExecutableForSolver(solvername));
        IResponse started = solver.start();
        Assert.assertFalse("start: " + started, started.isError());
        try {
            List<ICommand> commands = new ArrayList<>();
            org.smtlib.IParser parser = new org.smtlib.sexpr.Parser(config, config.smtFactory.createSource(text, null));
            ICommand cmd;
            while ((cmd = parser.parseCommand()) != null) commands.add(cmd);
            ICommand.IScript script = config.commandFactory.script(null, commands);
            long start = System.nanoTime();
            IResponse r = script.execute(solver);
            return new Object[]{r.toString(), System.nanoTime() - start};
        } finally {
            solver.exit();
        }
    }

    @Test
    public void scriptPipeliningIsFaster() throws Exception {
        Assume.assumeFalse(solvername.equals("test") || solvername.equals("simplify")
                || solvername.startsWith("z3-4.3") || solvername.startsWith("z3_4_3"));
        execute(script(50), false);
        execute(script(50), true);

        String text = script(DECLARATIONS);
        Object[] sync = execute(text, false);
        Object[] pipelined = execute(text, true);
        Assert.assertEquals("response with pipelining", sync[0], pipelined[0]);
        Assert.assertEquals("sat", sync[0]);
        long syncMillis = (Long)sync[1] / 1_000_000;
        long pipelinedMillis = (Long)pipelined[1] / 1_000_000;
        System.out.println("Executing a script of " + (2 * DECLARATIONS + 2) + " commands with " + solvername
                + ", pipelined: " + pipelinedMillis + " ms instead of " + syncMillis + " ms");
        Assert.assertTrue("pipelined " + pipelinedMillis + " ms vs. " + syncMillis + " ms unpipelined",
                2 * pipelinedMillis < syncMillis);
    }
}
