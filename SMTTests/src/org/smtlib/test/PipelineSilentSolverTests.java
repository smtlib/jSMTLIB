package org.smtlib.test;

import java.io.File;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.TimeUnit;

import org.junit.After;
import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.junit.rules.Timeout;
import org.smtlib.AbstractSolver;
import org.smtlib.ICommand;
import org.smtlib.IParser;
import org.smtlib.IResponse;
import org.smtlib.ISource;
import org.smtlib.SMT;
import org.smtlib.solvers.Solver_smt;

/** Pipelining with a solver that writes nothing for a successful command (#149): responses are
 *  matched by shape, and an echo sent before waiting marks the end of the pending responses.
 *  Uses StubSolver, whose replies include one for the priming command and one for the echo. */
public class PipelineSilentSolverTests {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);
    @Rule public TemporaryFolder folder = new TemporaryFolder();

    private SMT.Configuration config;
    private AbstractSolver solver;

    @After
    public void stop() {
        if (solver != null) solver.forceExit();
    }

    /** Starts a silent solver whose replies are the given lines */
    private void start(String... replies) throws Exception {
        File stub = folder.newFile("replies");
        Files.write(stub.toPath(), Arrays.asList(replies));
        config = new SMT().smtConfig;
        String javaBin = System.getProperty("java.home") + File.separator + "bin" + File.separator + "java";
        solver = new Solver_smt(config, new String[]{javaBin, "-cp", System.getProperty("java.class.path"),
                "org.smtlib.test.StubSolver", stub.getPath()}) {
            @Override protected boolean solverPrintsSuccess() { return false; }
        };
        Assert.assertFalse(solver.start().isError());
    }

    /** Sends each command pipelined, waits for the responses, and returns them */
    private List<IResponse> run(String text) throws Exception {
        ISource source = config.smtFactory.createSource(text, null);
        IParser parser = new org.smtlib.sexpr.Parser(config, source);
        List<IResponse> responses = new ArrayList<>();
        ICommand cmd;
        while ((cmd = parser.parseCommand()) != null) responses.add(solver.sendPipelined(cmd));
        solver.readPipelined(true);
        List<IResponse> result = new ArrayList<>();
        for (IResponse r: responses) result.add(r instanceof AbstractSolver.Pending p ? p.response() : r);
        return result;
    }

    private String print(List<IResponse> responses) {
        StringBuilder sb = new StringBuilder();
        for (IResponse r: responses) sb.append(config.defaultPrinter.toString(r)).append('\n');
        return sb.toString();
    }

    private static final String SCRIPT = "(set-logic QF_UF)(declare-fun p () Bool)(assert p)(check-sat)(assert (not p))";

    @Test
    public void successfulCommandsAreSilent() throws Exception {
        start("success", "", "", "", "sat", "", "\"jsmtlib-sync-1\"");
        Assert.assertEquals("success\nsuccess\nsuccess\nsat\nsuccess\n", print(run(SCRIPT)));
        Assert.assertFalse(solver.outOfStep());
    }

    /** An error is matched to the oldest command without a response: which command it belongs to
     *  cannot be known, but the error is reported */
    @Test
    public void anErrorIsReported() throws Exception {
        start("success", "", "", "(error \"bad\")", "sat", "", "\"jsmtlib-sync-1\"");
        List<IResponse> responses = run(SCRIPT);
        long errors = responses.stream().filter(IResponse::isError).count();
        Assert.assertEquals(print(responses), 1, errors);
        Assert.assertEquals("sat", config.defaultPrinter.toString(responses.get(3)));
    }

    @Test
    public void outputAfterTheEchoIsOutOfStep() throws Exception {
        start("success", "", "", "", "sat", "", "\"jsmtlib-sync-1\" success");
        run(SCRIPT);
        solver.readPipelined(true);
        Assert.assertTrue(solver.outOfStep());
    }

    @Test
    public void aSuccessIsOutOfStep() throws Exception {
        start("success", "success", "", "", "sat", "", "\"jsmtlib-sync-1\"");
        List<IResponse> responses = run(SCRIPT);
        Assert.assertTrue(print(responses), responses.get(0).isError());
        Assert.assertTrue(solver.outOfStep());
    }
}
