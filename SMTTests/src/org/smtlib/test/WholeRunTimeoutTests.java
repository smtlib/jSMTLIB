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
 * 'unknown', with reason 'timeout', and leaves the solver usable. A whole-run limit (SMT.Configuration#timeoutTotal) ends the solver, which
 * each solver reports in its own way (z3 answers 'timeout' and exits; cvc5 reports the timeout on stderr and
 * aborts); jSMTLIB normalizes that to responseFactory.timeout(), for check-sat and for every later command.
 *
 * A whole-run limit runs on the wall clock, so it can also end the solver between commands; the next request of any
 * kind then gets the timeout response (checked with get-value, as after a 'sat' a client asks for model values).
 *
 * The query is hard nonlinear arithmetic: x^3 + y^3 = z^3 has no solution in positive integers, which neither solver
 * can show, so it always runs into whichever limit is set and the outcome does not depend on the machine's speed.
 * z3-4.3 gives up on that query with 'unknown' at once, so its tests use the pigeonhole query of scripts/timeout.scr.
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

    /** 12 pigeons into 11 holes, as QF_UF clauses in one assert (see scripts/timeout.scr) */
    static String pigeonholeQuery() {
        StringBuilder sb = new StringBuilder("(set-logic QF_UF)\n");
        for (int i = 1; i <= 12; i++) {
            for (int j = 1; j <= 11; j++) sb.append("(declare-fun p_").append(i).append('_').append(j).append(" () Bool)\n");
        }
        sb.append("(assert (and");
        for (int i = 1; i <= 12; i++) {
            sb.append(" (or");
            for (int j = 1; j <= 11; j++) sb.append(" p_").append(i).append('_').append(j);
            sb.append(')');
        }
        for (int j = 1; j <= 11; j++) {
            for (int i1 = 1; i1 <= 12; i1++) {
                for (int i2 = i1 + 1; i2 <= 12; i2++) {
                    sb.append(" (or (not p_").append(i1).append('_').append(j).append(") (not p_").append(i2).append('_').append(j).append("))");
                }
            }
        }
        sb.append("))\n(check-sat)\n");
        return sb.toString();
    }

    /** The solver's executable in SMT_SOLVER_DIR, or null if it is not there */
    private static String exe(String name) {
        String dir = System.getenv("SMT_SOLVER_DIR");
        if (dir == null) return null;
        String exe = new File(dir, name).getPath();
        // absolute, as createSolver would otherwise resolve a relative path against SMT_SOLVER_DIR a second time
        return new File(exe).isFile() || new File(exe + ".exe").isFile() ? new File(exe).getAbsolutePath() : null;
    }

    /** Starts the named solver (a name configured in jsmtlib.properties) from the named executable */
    private static ISolver start(SMT.Configuration config, String solverName, String exeName) throws Exception {
        String exe = exe(exeName);
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
        checkWholeRunLimit(solverName, solverName, HARD_QUERY);
    }

    private static void checkWholeRunLimit(String solverName, String exeName, String query) throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        config.timeoutTotal = 1;
        ISolver solver = start(config, solverName, exeName);
        try {
            IResponse r = run(config, solver, query);
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
        checkWholeRunLimitWhileIdle(solverName, solverName, "(set-option :produce-models true)\n(set-logic ALL)\n"
                + "(declare-fun x () Int)\n(assert (> x 3))\n(check-sat)\n");
    }

    /** As above, with the given easy (sat) query, which declares x */
    private static void checkWholeRunLimitWhileIdle(String solverName, String exeName, String query) throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        config.timeoutTotal = 1;
        ISolver solver = start(config, solverName, exeName);
        try {
            IResponse r = run(config, solver, query);
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

    /** The per-query limit, in incremental mode (after a push), as OpenJML uses a solver; the reason for 'unknown' is
     *  'timeout' (z3 4.16.0 itself answers "canceled" there, which the adapter reports as "timeout") */
    private static void checkPerQueryLimit(String solverName) throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        config.timeout = 1;
        ISolver solver = start(config, solverName, solverName);
        try {
            IResponse r = run(config, solver, HARD_QUERY.replace("(assert (= (+", "(push 1)\n(assert (= (+"));
            Assert.assertEquals("check-sat at the per-query limit", config.responseFactory.unknown(), r);
            IResponse reason = solver.get_info(config.exprFactory.keyword(":reason-unknown"));
            Assert.assertTrue("reason for unknown: " + reason, reason.toString().contains("timeout"));
            // The solver is still running: another query gets an answer of its own
            Assert.assertEquals("a later check-sat", config.responseFactory.unknown(), solver.check_sat());
        } finally {
            solver.exit();
        }
    }

    @Test
    public void bitwuzlaWholeRunLimit() throws Exception {
        checkWholeRunLimit("bitwuzla", "bitwuzla-0.9.1", pigeonholeQuery());
    }

    @Test
    public void bitwuzlaWholeRunLimitWhileIdle() throws Exception {
        checkWholeRunLimitWhileIdle("bitwuzla", "bitwuzla-0.9.1", "(set-option :produce-models true)\n(set-logic QF_BV)\n"
                + "(declare-fun x () (_ BitVec 4))\n(assert (bvugt x #x3))\n(check-sat)\n");
    }

    /** bitwuzla answers unknown both at its per-query limit and when its whole-run limit ends it; with both limits
     *  set, an unknown at the per-query limit is not a timeout, and the solver keeps running */
    @Test
    public void bitwuzlaPerQueryLimitWithWholeRunLimit() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        config.timeout = 1;
        config.timeoutTotal = 30;
        ISolver solver = start(config, "bitwuzla", "bitwuzla-0.9.1");
        try {
            IResponse r = run(config, solver, pigeonholeQuery());
            Assert.assertEquals("check-sat at the per-query limit", config.responseFactory.unknown(), r);
            // bitwuzla keeps what it learned, so a second second may finish the proof: unknown or unsat
            IResponse later = solver.check_sat();
            Assert.assertTrue("a later check-sat: " + later, later.equals(config.responseFactory.unknown())
                    || later.equals(config.responseFactory.unsat()));
        } finally {
            IResponse r = solver.exit();
            Assert.assertFalse("exit: " + r, r.isError());
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

    /** Not on linux-arm64, whose z3-4.3.1 build answers sat for the (unsat) pigeonhole query (#101) */
    @Test
    public void z3_4_3WholeRunLimit() throws Exception {
        Assume.assumeFalse("z3-4.3.1's linux-arm64 build answers sat",
                System.getProperty("os.name").startsWith("Linux") && System.getProperty("os.arch").equals("aarch64"));
        checkWholeRunLimit("z3-4.3", "z3-4.3.1", pigeonholeQuery());
    }

    /** macOS only: z3-4.3.1's -T limit did not expire while it was idle on Linux (amd64 Docker container) */
    @Test
    public void z3_4_3WholeRunLimitWhileIdle() throws Exception {
        Assume.assumeTrue("z3-4.3 idle limit is checked on macOS only", System.getProperty("os.name").startsWith("Mac"));
        checkWholeRunLimitWhileIdle("z3-4.3", "z3-4.3.1", "(set-option :produce-models true)\n(set-logic ALL)\n"
                + "(declare-fun x () Int)\n(assert (> x 3))\n(check-sat)\n");
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
