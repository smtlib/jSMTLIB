package org.smtlib.test;

import java.io.File;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;
import org.junit.Assert;
import org.junit.Assume;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.ICommand;
import org.smtlib.IParser;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.ISource;
import org.smtlib.SMT;

/**
 * Tests of ISolver.sendCommands, which sends declarations, definitions and assertions to the solver as one block
 * (AbstractSolver) or one at a time (the ISolver default, here through Solver_test).
 *
 * After an error inside a block, z3 and smtinterpol go on with the rest of the block, while cvc5 and yices2 stop
 * reading input; either way the first error is returned, without waiting for an acknowledgment that never comes.
 * A test is skipped if its solver's executable is not in SMT_SOLVER_DIR.
 */
public class SendCommandsTests {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    /** The executable in SMT_SOLVER_DIR, or null if it is not there */
    private static String exe(String name) {
        String dir = System.getenv("SMT_SOLVER_DIR");
        if (dir == null) return null;
        String exe = new File(dir, name).getPath();
        // absolute, as createSolver would otherwise resolve a relative path against SMT_SOLVER_DIR a second time
        return new File(exe).isFile() || new File(exe + ".exe").isFile() ? new File(exe).getAbsolutePath() : null;
    }

    /** Starts the named solver (a name configured in jsmtlib.properties), whose executable is exeName */
    private static ISolver start(SMT.Configuration config, String solverName, String exeName) throws Exception {
        String exe = exe(exeName);
        Assume.assumeTrue(exeName + " executable not available", exe != null);
        config.props = config.readProperties(); // the adapter for the solver name comes from jsmtlib.properties
        ISolver solver = config.createSolver(solverName, exe);
        IResponse r = solver.start();
        Assert.assertFalse("start: " + r, r.isError());
        return solver;
    }

    private static List<ICommand> parse(SMT.Configuration config, String text) throws Exception {
        ISource source = config.smtFactory.createSource(text, null);
        IParser parser = new org.smtlib.sexpr.Parser(config, source);
        List<ICommand> commands = new ArrayList<>();
        ICommand cmd;
        while ((cmd = parser.parseCommand()) != null) commands.add(cmd);
        return commands;
    }

    /** Executes the commands one at a time, returning the response to the last one */
    private static IResponse run(SMT.Configuration config, ISolver solver, String text) throws Exception {
        IResponse response = null;
        for (ICommand c: parse(config, text)) response = c.execute(solver);
        return response;
    }

    static final String DECLS =
            "(declare-fun x () Int)\n"
            + "(declare-const y Int)\n"
            + "(declare-fun f (Int) Int)\n"
            + "(define-fun g ((i Int)) Int (+ i 1))\n"
            + "(declare-sort S 0)\n"
            + "(declare-fun s () S)\n"
            + "(assert (> x y))\n"
            + "(assert (= (g x) (+ x 1)))\n";

    /** A block is acknowledged once and has the same effect as its commands one at a time */
    private static void checkBlock(String solverName, String exeName) throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        ISolver solver = start(config, solverName, exeName);
        try {
            Assert.assertEquals("set-logic", config.responseFactory.success(), run(config, solver, "(set-logic ALL)\n"));
            Assert.assertEquals("block", config.responseFactory.success(), solver.sendCommands(parse(config, DECLS)));
            Assert.assertEquals("check-sat", config.responseFactory.sat(), run(config, solver, "(check-sat)\n"));
            // a block clears the check-sat status, as each of its commands would
            Assert.assertEquals("second block", config.responseFactory.success(),
                    solver.sendCommands(parse(config,
                            "(assert (forall ((i Int)) (! (> (f i) i) :pattern ((f i)))))\n(assert (= y (f x)))\n")));
            Assert.assertNull("check-sat status after a block", solver.checkSatStatus());
            Assert.assertEquals("check-sat", config.responseFactory.unsat(), run(config, solver, "(check-sat)\n"));
        } finally {
            solver.exit();
        }
    }

    /** The first error in a block is returned; if continues, the solver is still usable afterwards */
    private static void checkErrorInBlock(String solverName, String exeName, boolean continues) throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        ISolver solver = start(config, solverName, exeName);
        try {
            run(config, solver, "(set-logic ALL)\n");
            IResponse r = solver.sendCommands(parse(config,
                    "(declare-fun x () Int)\n(assert (> undeclared 0))\n(assert (+ x true))\n(declare-fun z () Int)\n"));
            Assert.assertTrue("expected an error: " + r, r.isError());
            String text = config.defaultPrinter.toString(r);
            Assert.assertTrue("the first error: " + text, text.contains("undeclared"));
            if (continues) {
                Assert.assertEquals("check-sat after the block", config.responseFactory.sat(),
                        run(config, solver, "(assert (> z x))\n(check-sat)\n"));
            }
        } finally {
            solver.exit();
        }
    }

    /** A block sent after the solver's whole-run limit ended it gets the timeout response */
    private static void checkAfterWholeRunLimit(String solverName, String exeName) throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        config.timeoutTotal = 1;
        ISolver solver = start(config, solverName, exeName);
        try {
            IResponse r = run(config, solver, WholeRunTimeoutTests.HARD_QUERY);
            Assert.assertEquals("check-sat at the whole-run limit", config.responseFactory.timeout(), r);
            r = solver.sendCommands(parse(config, "(declare-fun u () Int)\n(assert (> u 0))\n"));
            Assert.assertEquals("a block after the whole-run limit", config.responseFactory.timeout(), r);
        } finally {
            IResponse r = solver.exit();
            Assert.assertFalse("exit after the whole-run limit: " + r, r.isError());
        }
    }

    /** Only declarations, definitions and assertions are accepted; otherwise nothing is sent */
    private static void checkRejectsOtherCommands(ISolver solver, SMT.Configuration config) throws Exception {
        IResponse r = solver.sendCommands(parse(config, "(declare-fun v () Int)\n(check-sat)\n"));
        Assert.assertTrue("expected an error: " + r, r.isError());
        Assert.assertTrue(config.defaultPrinter.toString(r), config.defaultPrinter.toString(r).contains("check-sat"));
        // v was not declared, so it can be declared now
        Assert.assertEquals(config.responseFactory.success(), solver.sendCommands(parse(config, "(declare-fun v () Int)\n")));
        Assert.assertEquals(config.responseFactory.success(), solver.sendCommands(new ArrayList<>()));
    }

    @Test
    public void z3Block() throws Exception {
        checkBlock("z3-4.16.0", "z3-4.16.0");
    }

    @Test
    public void z3_4_3Block() throws Exception {
        checkBlock("z3-4.3", "z3-4.3.1");
    }

    @Test
    public void cvc5Block() throws Exception {
        checkBlock("cvc5-1.3.2", "cvc5-1.3.2");
    }

    @Test
    public void yices2Block() throws Exception {
        // yices2 has no quantifiers in ALL; its block leaves out the forall
        SMT.Configuration config = new SMT.Configuration();
        ISolver solver = start(config, "yices2-2.7.0", "yices2-2.7.0");
        try {
            run(config, solver, "(set-logic QF_UFLIA)\n");
            Assert.assertEquals("block", config.responseFactory.success(), solver.sendCommands(parse(config,
                    "(declare-fun x () Int)\n(declare-fun f (Int) Int)\n(assert (> (f x) x))\n(assert (= x (f x)))\n")));
            Assert.assertEquals("check-sat", config.responseFactory.unsat(), run(config, solver, "(check-sat)\n"));
        } finally {
            solver.exit();
        }
    }

    @Test
    public void smtinterpolBlock() throws Exception {
        checkBlock("smtinterpol-2.5", "smtinterpol-2.5.jar");
    }

    @Test
    public void z3ErrorInBlock() throws Exception {
        checkErrorInBlock("z3-4.16.0", "z3-4.16.0", true);
    }

    @Test
    public void cvc5ErrorInBlock() throws Exception {
        checkErrorInBlock("cvc5-1.3.2", "cvc5-1.3.2", false);
    }

    @Test
    public void yices2ErrorInBlock() throws Exception {
        checkErrorInBlock("yices2-2.7.0", "yices2-2.7.0", false);
    }

    @Test
    public void smtinterpolErrorInBlock() throws Exception {
        checkErrorInBlock("smtinterpol-2.5", "smtinterpol-2.5.jar", true);
    }

    @Test
    public void z3AfterWholeRunLimit() throws Exception {
        checkAfterWholeRunLimit("z3-4.16.0", "z3-4.16.0");
    }

    @Test
    public void cvc5AfterWholeRunLimit() throws Exception {
        checkAfterWholeRunLimit("cvc5-1.3.2", "cvc5-1.3.2");
    }

    @Test
    public void z3RejectsOtherCommands() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        ISolver solver = start(config, "z3-4.16.0", "z3-4.16.0");
        try {
            run(config, solver, "(set-logic ALL)\n");
            checkRejectsOtherCommands(solver, config);
        } finally {
            solver.exit();
        }
    }

    @Test // z3-4.3's adapter requires the logic to be set first, for a block as for each command
    public void z3_4_3RequiresLogic() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        ISolver solver = start(config, "z3-4.3", "z3-4.3.1");
        try {
            IResponse r = solver.sendCommands(parse(config, "(declare-fun x () Int)\n(assert (> x 0))\n"));
            Assert.assertTrue("expected an error: " + r, r.isError());
        } finally {
            solver.exit();
        }
    }

    @Test // the ISolver default, one command at a time
    public void defaultImplementation() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        ISolver solver = config.createSolver("test", null);
        Assert.assertFalse(solver.start().isError());
        try {
            run(config, solver, "(set-logic ALL)\n");
            Assert.assertEquals("block", config.responseFactory.success(), solver.sendCommands(parse(config, DECLS)));
            IResponse r = solver.sendCommands(parse(config, "(declare-fun w () Int)\n(assert (> undeclared 0))\n"));
            Assert.assertTrue("expected an error: " + r, r.isError());
            checkRejectsOtherCommands(solver, config);
        } finally {
            solver.exit();
        }
    }
}
