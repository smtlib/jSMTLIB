package org.smtlib.test;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.concurrent.TimeUnit;

import org.junit.After;
import org.junit.Assert;
import org.junit.Assume;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.junit.runners.ParameterizedWithNames;
import org.smtlib.AbstractSolver;
import org.smtlib.ICommand;
import org.smtlib.IParser;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.ISource;
import org.smtlib.SMT;

/** Tests of pipelining through the library API (AbstractSolver.sendPipelined/readPipelined), for
 *  each solver in SMT_TEST_SOLVERS whose adapter pipelines: responses are read later and matched
 *  to their commands in order, check-sat's answer becomes the check-sat status when read, and a
 *  request that waits for its response first reads the pending ones. */
@RunWith(ParameterizedWithNames.class)
public class PipelineApiTests {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    private final String solvername;
    private SMT.Configuration config;
    private AbstractSolver solver;

    public PipelineApiTests(String solvername) {
        this.solvername = solvername;
    }

    @Parameters
    public static Collection<String[]> data() {
        List<String[]> list = new ArrayList<>();
        for (String s : LogicTests.solvers) list.add(new String[]{s});
        return list;
    }

    @Before
    public void start() throws Exception {
        SMT smt = new SMT();
        config = smt.smtConfig;
        config.props = config.readProperties();
        ISolver s = config.createSolver(solvername, LogicTests.executable(smt, solvername));
        Assume.assumeTrue("not run as a process", s instanceof AbstractSolver);
        solver = (AbstractSolver)s;
        Assume.assumeTrue("does not pipeline", solver.pipelines(parse("(check-sat)").get(0)));
        IResponse r = solver.start();
        Assert.assertFalse("start: " + r, r.isError());
    }

    @After
    public void stop() {
        if (solver != null) solver.forceExit();
    }

    private List<ICommand> parse(String text) throws Exception {
        ISource source = config.smtFactory.createSource(text, null);
        IParser parser = new org.smtlib.sexpr.Parser(config, source);
        List<ICommand> commands = new ArrayList<>();
        ICommand cmd;
        while ((cmd = parser.parseCommand()) != null) commands.add(cmd);
        return commands;
    }

    /** Sends each command with sendPipelined, returning the responses */
    private List<IResponse> pipeline(String text) throws Exception {
        List<IResponse> responses = new ArrayList<>();
        for (ICommand c : parse(text)) {
            Assert.assertTrue("pipelines " + c, solver.pipelines(c));
            responses.add(solver.sendPipelined(c));
        }
        return responses;
    }

    /** The response read for a command sent with sendPipelined */
    private static IResponse read(IResponse r) {
        Assert.assertTrue("a pending response: " + r, r instanceof AbstractSolver.Pending);
        AbstractSolver.Pending p = (AbstractSolver.Pending)r;
        Assert.assertTrue("read", p.isReady());
        return p.response();
    }

    @Test
    public void responsesAreReadLater() throws Exception {
        List<IResponse> rs = pipeline("(set-logic QF_UF)(declare-fun x () Bool)(assert x)");
        solver.readPipelined(true);
        Assert.assertFalse(solver.hasPending());
        for (IResponse r : rs) Assert.assertEquals("success", read(r).toString());
    }

    @Test
    public void checkSatStatusIsSetWhenRead() throws Exception {
        List<IResponse> rs = pipeline("(set-logic QF_UF)(declare-fun x () Bool)(assert x)(check-sat)");
        IResponse checkSat = rs.get(3);
        solver.readPipelined(true);
        Assert.assertEquals("sat", read(checkSat).toString());
        Assert.assertEquals("sat", solver.checkSatStatus().toString());
    }

    @Test
    public void answersAreMatchedInOrder() throws Exception {
        StringBuilder text = new StringBuilder("(set-logic QF_UF)(declare-fun x () Bool)");
        List<String> expected = new ArrayList<>(List.of("success", "success"));
        for (int i = 0; i < 50; i++) {
            boolean sat = i % 3 != 0;
            text.append("(push 1)(assert ").append(sat ? "x" : "(and x (not x))").append(")(check-sat)(pop 1)");
            expected.addAll(List.of("success", "success", sat ? "sat" : "unsat", "success"));
        }
        List<IResponse> rs = pipeline(text.toString());
        solver.readPipelined(true);
        for (int i = 0; i < rs.size(); i++) Assert.assertEquals("response " + i, expected.get(i), read(rs.get(i)).toString());
    }

    @Test
    public void readingWithoutWaitingLeavesTheRest() throws Exception {
        List<IResponse> rs = pipeline("(set-logic QF_UF)(declare-fun x () Bool)");
        solver.readPipelined(false); // whatever has arrived, perhaps nothing
        solver.readPipelined(true);
        for (IResponse r : rs) Assert.assertEquals("success", read(r).toString());
    }

    @Test
    public void aWaitingRequestReadsThePendingResponsesFirst() throws Exception {
        List<IResponse> rs = pipeline("(set-logic QF_UF)(declare-fun x () Bool)(assert x)(check-sat)");
        // executed as usual, so it waits for its own response
        IResponse push = parse("(push 1)").get(0).execute(solver);
        Assert.assertEquals("success", push.toString());
        Assert.assertFalse(solver.hasPending());
        Assert.assertEquals("sat", read(rs.get(3)).toString());
    }

    @Test
    public void sendCommandsReadsThePendingResponsesFirst() throws Exception {
        List<IResponse> rs = pipeline("(set-logic QF_UF)(declare-fun x () Bool)");
        IResponse block = solver.sendCommands(parse("(declare-fun y () Bool)(assert (or x y))"));
        Assert.assertEquals("success", block.toString());
        for (IResponse r : rs) Assert.assertEquals("success", read(r).toString());
        Assert.assertEquals("sat", parse("(check-sat)").get(0).execute(solver).toString());
    }

    @Test
    public void anErrorIsMatchedToItsCommand() throws Exception {
        List<IResponse> rs = pipeline("(set-logic QF_UF)(declare-fun x () Bool)(assert (and x undeclared))(declare-fun y () Bool)(check-sat)");
        solver.readPipelined(true);
        Assert.assertEquals("success", read(rs.get(1)).toString());
        Assert.assertTrue("an error: " + read(rs.get(2)), read(rs.get(2)).isError());
        // z3 and smtinterpol go on after the error; cvc5, yices2 and bitwuzla stop, as for every later command
        IResponse after = read(rs.get(3));
        if (after.isError()) {
            Assert.assertTrue(after.toString(), after.toString().contains("Solver process has already exited"));
            Assert.assertTrue(read(rs.get(4)).toString().contains("Solver process has already exited"));
        } else {
            Assert.assertEquals("success", after.toString());
            Assert.assertEquals("sat", read(rs.get(4)).toString());
        }
    }
}
