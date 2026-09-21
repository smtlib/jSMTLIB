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
 * Reproduced with a parameterized (arity &gt; 0) function: {@code define_fun()} always builds
 * the internal assertion as {@code (= <name> <body>)} (never applying the parameters), which
 * is only sound for an arity-0 definition -- for arity &gt; 0, {@code <name>} denotes the
 * function itself (an arrow-sorted symbol), so comparing it via {@code =} against the
 * (value-sorted) body is a genuine sort mismatch that {@code assertExpr()} correctly rejects.
 * That's exactly the kind of failure this bug swallows.
 * <p>
 * Fixed by capturing {@code assertExpr()}'s result and propagating it when it isn't OK.
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

        doCommand(config, solver, "(set-logic QF_UF)");
        doCommand(config, solver, "(declare-sort S 0)");

        // f : S -> S, defined as (define-fun f ((x S)) S x). The internal recording
        // assertion becomes (= f x) -- comparing the function symbol f itself (sort S->S)
        // against x (sort S) -- a sort mismatch assertExpr() must reject.
        IResponse r = doCommand(config, solver, "(define-fun f ((x S)) S x)");

        Assert.assertTrue("a failing internal assertExpr() must not be reported as success",
                r.isError());
    }
}
