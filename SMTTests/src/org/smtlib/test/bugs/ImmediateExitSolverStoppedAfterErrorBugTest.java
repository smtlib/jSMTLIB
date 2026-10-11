package org.smtlib.test.bugs;

import java.io.File;
import java.util.ArrayList;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Assume;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.IExpr;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.ISort;
import org.smtlib.SMT;

/**
 * Pins down (and confirms the fix for) immediate-exit solvers that do not actually exit.
 * cvc5's :error-behavior is immediate-exit, and jSMTLIB assumed its process would end after
 * an error; but run interactively (as Solver_cvc5 runs it) cvc5 does not always exit -- it
 * stays alive and ignores all further input. After a get-value error (a path that did not
 * go through sendCommand's settle-pause at all), the next get-value's :produce-models check
 * then reported the misleading "The get-value command is only valid if :produce-models has
 * been enabled", and a client's later exit() could wait forever for a reply.
 * <p>
 * Fixed by AbstractSolver.checkImmediateExit(), applied to every parsed response: after an
 * error from a selfReportsImmediateExit() solver, the process is given a moment to exit and
 * otherwise stopped (SolverProcess.stopIfRunning()), and requireOptionEnabled() now passes an
 * error from its get-option query through instead of reporting the option as off.
 */
public class ImmediateExitSolverStoppedAfterErrorBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    private static String cvc5Exe() {
        String dir = System.getenv("SMT_SOLVER_DIR");
        if (dir == null) return null;
        String exe = new File(dir, "cvc5-1.3.2").getPath();
        return new File(exe).isFile() || new File(exe + ".exe").isFile() ? exe : null;
    }

    @Test
    public void errorInGetValueStopsTheSolverAndLaterCommandsSayWhy() throws Exception {
        String exe = cvc5Exe();
        Assume.assumeTrue("cvc5-1.3.2 executable not available on this platform", exe != null);

        SMT.Configuration config = new SMT.Configuration();
        IExpr.IFactory f = config.exprFactory;
        ISolver solver = config.createSolver("cvc5-1.3.2", new File(exe).getAbsolutePath());
        Assert.assertFalse(solver.start().isError());
        try {
            Assert.assertFalse(solver.set_option(f.keyword(":produce-models"), f.symbol("true")).isError());
            Assert.assertFalse(solver.set_logic("ALL", null).isError());
            ISort intSort = config.sortFactory.createSortExpression(f.symbol("Int"), new ISort[0]);
            Assert.assertFalse(solver.declare_fun(config.commandFactory.declare_fun(f.symbol("x"), new ArrayList<>(), intSort)).isError());
            Assert.assertEquals("sat", config.defaultPrinter.toString(solver.check_sat()));

            // QQ is undeclared: cvc5 reports a parse error and stops processing input
            IResponse r = solver.get_value(f.fcn(f.symbol("f"), f.symbol("QQ")));
            Assert.assertTrue("expected an error: " + r, r.isError());

            // The next command must fail promptly, reporting that the solver is gone (as "has
            // already exited" or, depending on timing, "closed its input stream") -- not that
            // :produce-models is off
            r = solver.get_value(f.symbol("x"));
            String msg = config.defaultPrinter.toString(r);
            Assert.assertTrue("expected an error: " + msg, r.isError());
            Assert.assertTrue("expected the error to come from writing to the stopped solver: " + msg, msg.contains("Error writing to solver"));
            Assert.assertFalse("misleading :produce-models message: " + msg, msg.contains("only valid if"));
        } finally {
            solver.exit(); // must return (the Timeout rule guards against a hang)
        }
    }
}
