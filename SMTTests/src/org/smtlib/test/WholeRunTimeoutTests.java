package org.smtlib.test;

import java.io.File;
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
 * Covers the two kinds of solver time limit. A per-query limit (SMT.Configuration#timeout) makes check-sat answer
 * 'unknown' and leaves the solver usable. A whole-run limit (SMT.Configuration#timeoutTotal) ends the solver, which
 * each solver reports in its own way (z3 answers 'timeout' and exits; cvc5 reports the timeout on stderr and
 * aborts); jSMTLIB normalizes that to responseFactory.timeout(), for check-sat and for every later command.
 *
 * A whole-run limit runs on the wall clock, so it can also end the solver between commands; the next request of any
 * kind then gets the timeout response (checked with get-value, as after a 'sat' a client asks for model values).
 *
 * The query is hard nonlinear arithmetic: x^3 + y^3 = z^3 has no solution in positive integers, which neither solver
 * can show, so it always runs into whichever limit is set and the outcome does not depend on the machine's speed.
 * A test is skipped if its solver's executable is not in SMT_SOLVER_DIR.
 */
public class WholeRunTimeoutTests {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    static final String HARD_QUERY =
            "(set-logic ALL)\n"
            + "(declare-fun x () Int)\n"
            + "(declare-fun y () Int)\n"
            + "(declare-fun z () Int)\n"
            + "(assert (and (> x 0) (> y 0) (> z 0)))\n"
            + "(assert (= (+ (* x x x) (* y y y)) (* z z z)))\n"
            + "(check-sat)\n";

    /** The solver's executable in SMT_SOLVER_DIR, or null if it is not there */
    private static String exe(String name) {
        String dir = System.getenv("SMT_SOLVER_DIR");
        if (dir == null) return null;
        String exe = new File(dir, name).getPath();
        // absolute, as createSolver would otherwise resolve a relative path against SMT_SOLVER_DIR a second time
        return new File(exe).isFile() || new File(exe + ".exe").isFile() ? new File(exe).getAbsolutePath() : null;
    }

    /** Starts the named solver (a name configured in jsmtlib.properties, which is also its executable's name) */
    private static ISolver start(SMT.Configuration config, String solverName) throws Exception {
        String exe = exe(solverName);
        Assume.assumeTrue(solverName + " executable not available", exe != null);
        config.props = config.readProperties(); // the adapter for the solver name comes from jsmtlib.properties
        ISolver solver = config.createSolver(solverName, exe);
        IResponse r = solver.start();
        Assert.assertFalse("start: " + r, r.isError());
        return solver;
    }

    /** Executes the commands in text, returning the response to the last one */
    private static IResponse run(SMT.Configuration config, ISolver solver, String text) throws Exception {
        ISource source = config.smtFactory.createSource(text, null);
        IParser parser = new org.smtlib.sexpr.Parser(config, source);
        IResponse response = null;
        ICommand cmd;
        while ((cmd = parser.parseCommand()) != null) {
            response = cmd.execute(solver);
        }
        return response;
    }

    private static void checkWholeRunLimit(String solverName) throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        config.timeoutTotal = 1;
        ISolver solver = start(config, solverName);
        try {
            IResponse r = run(config, solver, HARD_QUERY);
            Assert.assertEquals("check-sat at the whole-run limit", config.responseFactory.timeout(), r);
            // The solver has ended: later commands get the same response, not an error about the exited process
            Assert.assertEquals("a later check-sat", config.responseFactory.timeout(), solver.check_sat());
        } finally {
            IResponse r = solver.exit();
            Assert.assertFalse("exit after the whole-run limit: " + r, r.isError());
        }
    }

    /** The whole-run limit runs on the wall clock, so it can end the solver while it is idle, e.g. while a client
     *  is processing a counterexample; the next request of any kind (here get-value) then gets the timeout response */
    private static void checkWholeRunLimitWhileIdle(String solverName) throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        config.timeoutTotal = 1;
        ISolver solver = start(config, solverName);
        try {
            IResponse r = run(config, solver, "(set-option :produce-models true)\n(set-logic ALL)\n"
                    + "(declare-fun x () Int)\n(assert (> x 3))\n(check-sat)\n");
            Assert.assertEquals("an easy check-sat", config.responseFactory.sat(), r);
            Thread.sleep(2000); // idle past the 1-second limit
            r = run(config, solver, "(get-value (x))\n");
            Assert.assertEquals("get-value after the whole-run limit", config.responseFactory.timeout(), r);
            Assert.assertEquals("a later check-sat", config.responseFactory.timeout(), solver.check_sat());
        } finally {
            IResponse r = solver.exit();
            Assert.assertFalse("exit after the whole-run limit: " + r, r.isError());
        }
    }

    private static void checkPerQueryLimit(String solverName) throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        config.timeout = 1;
        ISolver solver = start(config, solverName);
        try {
            IResponse r = run(config, solver, HARD_QUERY);
            Assert.assertEquals("check-sat at the per-query limit", config.responseFactory.unknown(), r);
            // The solver is still running: another query gets an answer of its own
            Assert.assertEquals("a later check-sat", config.responseFactory.unknown(), solver.check_sat());
        } finally {
            solver.exit();
        }
    }

    @Test
    public void z3WholeRunLimit() throws Exception {
        checkWholeRunLimit("z3-4.16.0");
    }

    @Test
    public void z3PerQueryLimit() throws Exception {
        checkPerQueryLimit("z3-4.16.0");
    }

    @Test
    public void z3WholeRunLimitWhileIdle() throws Exception {
        checkWholeRunLimitWhileIdle("z3-4.16.0");
    }

    @Test
    public void cvc5WholeRunLimitWhileIdle() throws Exception {
        checkWholeRunLimitWhileIdle("cvc5-1.3.2");
    }

    @Test
    public void cvc5WholeRunLimit() throws Exception {
        checkWholeRunLimit("cvc5-1.3.2");
    }

    @Test
    public void cvc5PerQueryLimit() throws Exception {
        checkPerQueryLimit("cvc5-1.3.2");
    }
}
