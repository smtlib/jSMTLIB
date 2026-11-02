package org.smtlib.test.bugs;

import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.ICommand;
import org.smtlib.IParser;
import org.smtlib.IResponse;
import org.smtlib.ISource;
import org.smtlib.SMT;
import org.smtlib.solvers.Solver_simplify;

/**
 * Pins down issue #55: {@code Solver_simplify.define_fun()} builds and sends
 * {@code (= cmd.symbol() cmd.expression())} to record the definition (via {@code
 * assertExpr()}), but never checks that call's return value -- {@code res} was already set to
 * {@code success()} a few lines earlier, so a failing {@code assertExpr()} (e.g. because the
 * definition itself is ill-typed) is silently discarded and {@code define_fun()} reports
 * success regardless.
 * <p>
 * Reproduced with a body Simplify cannot translate (a decimal literal), which fails the
 * internal recording step after jSMTLIB's own type check has passed.
 * <p>
 * Fixed by propagating a failure of the internal recording step.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/55">issue #55</a>.
 * <p>
 * Stays a JUnit test: no Simplify binary is available in any local or CI-configured solver
 * directory (it is excluded from the test-solver list entirely when missing, per
 * {@code LogicTests.solversFromEnv()}), so a {@code --solver simplify} script test can't be
 * authored and verified against the real command-line tool here.
 */
public class SolverSimplifyDefineFunIgnoresAssertResultBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    private IResponse doCommand(SMT.Configuration config, Solver_simplify solver, String text) throws Exception {
        ISource source = config.smtFactory.createSource(text, null);
        IParser p = new org.smtlib.sexpr.Parser(config, source);
        ICommand cmd = p.parseCommand();
        return cmd.execute(solver);
    }

    @Test
    public void defineFunReportsTheUnderlyingAssertFailure() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        Solver_simplify solver = new Solver_simplify(config, "simplify");

        doCommand(config, solver, "(set-logic QF_LRA)");
        IResponse r = doCommand(config, solver, "(define-fun g ((x Real)) Real 2.5)");

        Assert.assertTrue("a failing internal definition step must not be reported as success",
                r.isError());
    }

    /** Issue #95: a definition with parameters was recorded as (= f body), an ill-sorted
     *  assertion; it is now a quantified axiom, accepted even in a QF logic. */
    @Test
    public void defineFunWithParametersSucceeds() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        Solver_simplify solver = new Solver_simplify(config, "simplify");

        doCommand(config, solver, "(set-logic QF_UF)");
        doCommand(config, solver, "(declare-sort S 0)");
        IResponse r = doCommand(config, solver, "(define-fun f ((x S)) S x)");

        Assert.assertTrue("define-fun with parameters: " + r, r.isOK());
    }
}
