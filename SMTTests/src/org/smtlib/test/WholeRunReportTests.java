package org.smtlib.test;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.SequenceInputStream;
import java.lang.reflect.Method;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.concurrent.TimeUnit;
import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.SMT;
import org.smtlib.SolverProcess;

/**
 * The report a solver writes when its whole-run time limit ends it while idle is read as unread output once a
 * command finds the process gone. It is recognized whatever the solver wrote on its other stream, and text read
 * before a stream fails is kept. The limit is 60 seconds, so the solver (a StubSolver) has not run that long, and
 * only its report can show that the limit ended it. Not a .tst: the solver must have exited before the next
 * command is sent, which needs a pause between commands.
 */
public class WholeRunReportTests {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    /** Starts the named adapter on a StubSolver with the given replies, with a 60-second whole-run limit */
    private static ISolver startStub(SMT.Configuration config, String solverName, String replies) throws Exception {
        File stub = File.createTempFile("stub", ".stub");
        stub.deleteOnExit();
        Files.writeString(stub.toPath(), replies);
        config.timeoutTotal = 60;
        config.props = config.readProperties();
        String javaBin = System.getProperty("java.home") + File.separator + "bin" + File.separator + "java";
        String prefix = "org.smtlib.solver_" + solverName;
        for (String k: config.props.stringPropertyNames()) {
            if (k.startsWith(prefix + ".exec")) config.props.remove(k);
        }
        config.props.setProperty(prefix + ".exec", javaBin);
        config.props.setProperty(prefix + ".command", String.join(",", javaBin, "-cp",
                System.getProperty("java.class.path"), "org.smtlib.test.StubSolver", stub.getAbsolutePath()));
        ISolver solver = config.createSolver(solverName, null);
        IResponse r = solver.start();
        Assert.assertFalse("start: " + r, r.isError());
        return solver;
    }

    /** After set-logic (and a pause, so that set-logic is answered before the solver stops), the stub writes
     *  exitText's lines and exits; the next commands answer timeout if timedOut, else an error */
    private static void checkReport(String solverName, String exitText, boolean timedOut) throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        String replies = "<<success-for (set-option :print-success true)>>\nsuccess\n"
                + "<<sleep 300>>\n" + exitText + "<<exit 0>>\n";
        ISolver solver = startStub(config, solverName, replies);
        try {
            Assert.assertEquals("set-logic", config.responseFactory.success(), solver.set_logic("QF_UF", null));
            Thread.sleep(1500); // the stub exits meanwhile
            IResponse r = solver.check_sat();
            if (timedOut) {
                Assert.assertEquals("check-sat after the report", config.responseFactory.timeout(), r);
                Assert.assertEquals("a later check-sat", config.responseFactory.timeout(), solver.check_sat());
            } else {
                Assert.assertTrue("check-sat without a report: " + r, r.isError());
            }
        } finally {
            solver.exit();
        }
    }

    @Test
    public void z3ReportWithStderrText() throws Exception {
        checkReport("z3-4.14.1", "<<print timeout>>\n<<eprint some diagnostic>>\n", true);
    }

    @Test
    public void bitwuzlaReportWithStderrText() throws Exception {
        checkReport("bitwuzla", "<<print unknown>>\n<<eprint some diagnostic>>\n", true);
    }

    @Test
    public void cvc5ReportWithStdoutText() throws Exception {
        checkReport("cvc5-1.3.2", "<<print some output>>\n<<eprint cvc5 interrupted by timeout.>>\n", true);
    }

    /** Without a report, the solver's exit is not a timeout */
    @Test
    public void z3NoReport() throws Exception {
        checkReport("z3-4.14.1", "<<print some output>>\n<<eprint some diagnostic>>\n", false);
    }

    /** A stream that yields the given text and then fails */
    private static InputStream failingAfter(String text) {
        return new SequenceInputStream(new ByteArrayInputStream(text.getBytes(StandardCharsets.UTF_8)),
                new InputStream() {
                    @Override public int read() throws IOException {
                        throw new IOException("read failed");
                    }
                });
    }

    /** Calls the gobbler's package-private method of the given name, with a wait in milliseconds */
    private static String call(SolverProcess.StreamGobbler g, String name, long millis) throws Exception {
        Method m = SolverProcess.StreamGobbler.class.getDeclaredMethod(name, long.class);
        m.setAccessible(true);
        try {
            return (String)m.invoke(g, millis);
        } catch (java.lang.reflect.InvocationTargetException e) {
            throw (Exception)e.getCause();
        }
    }

    /** Text read before the stream fails is returned, whether or not it ends with the end marker */
    @Test
    public void drainKeepsTextBeforeFailure() throws Exception {
        for (String method: new String[] {"drainToEnd", "drain"}) {
            for (String text: new String[] {"timeout\n", "timeout"}) {
                SolverProcess.StreamGobbler g = new SolverProcess.StreamGobbler(failingAfter(text),
                        s -> s.toString().endsWith("\n"), StandardCharsets.UTF_8);
                g.start();
                g.join(5000);
                Assert.assertEquals(method + " of " + text.trim(), text, call(g, method, 1000));
            }
        }
    }
}
