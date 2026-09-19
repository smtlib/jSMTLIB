package org.smtlib.test.bugs;

import java.util.concurrent.TimeUnit;

import org.junit.Assert;
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
 * Pins down issue #37: {@code C_push}/{@code C_pop} store the command's numeral argument as
 * both the original {@code INumeral} (arbitrary-precision, via {@code BigInteger}) and a
 * narrowed {@code int} ({@code number = n.intValue()}). {@code BigInteger.intValue()} silently
 * truncates to the low-order 32 bits per the Java spec -- so {@code (push 99999999999999999999)}
 * (far beyond {@code Integer.MAX_VALUE}) doesn't error, it silently becomes some arbitrary,
 * possibly negative {@code int} that gets passed straight to {@code solver.push(int)}.
 * {@code SMTExpr.Numeral}'s own constructor already has a {@code // FIXME - test with too big
 * a number} marking this exact gap.
 * <p>
 * Fixed by having {@code C_push}/{@code C_pop}'s {@code execute()} reject a numeral whose
 * {@code BigInteger} value doesn't fit in a (non-negative) {@code int} with a clean error,
 * instead of silently proceeding with the wrapped-around value.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/37">issue #37</a>.
 */
public class PushPopNumeralOverflowBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    private ISolver newTestSolver(SMT smt) {
        smt.props = smt.readProperties();
        smt.smtConfig.solvername = "test";
        ISolver solver = smt.startSolver(smt.smtConfig, "test", null);
        if (solver == null) throw new RuntimeException("Failed to create the test solver");
        return solver;
    }

    private IResponse doCommand(SMT smt, ISolver solver, String text) throws Exception {
        ISource source = smt.smtConfig.smtFactory.createSource(text, null);
        IParser p = new org.smtlib.sexpr.Parser(smt.smtConfig, source);
        ICommand cmd = p.parseCommand();
        return cmd.execute(solver);
    }

    @Test
    public void pushWithNumeralBeyondIntRangeIsRejected() throws Exception {
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic QF_UF)");

        IResponse r = doCommand(smt, solver, "(push 99999999999999999999)");
        Assert.assertTrue("a push argument far beyond Integer.MAX_VALUE must be rejected, "
                + "not silently truncated", r.isError());
    }

    @Test
    public void popWithNumeralBeyondIntRangeIsRejected() throws Exception {
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic QF_UF)");
        doCommand(smt, solver, "(push 1)");

        IResponse r = doCommand(smt, solver, "(pop 99999999999999999999)");
        Assert.assertTrue("a pop argument far beyond Integer.MAX_VALUE must be rejected, "
                + "not silently truncated", r.isError());
    }

    @Test
    public void ordinaryPushAndPopStillWork() throws Exception {
        // Characterizes that the fix doesn't affect ordinary, in-range arguments.
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic QF_UF)");
        Assert.assertFalse(doCommand(smt, solver, "(push 2)").isError());
        Assert.assertFalse(doCommand(smt, solver, "(pop 2)").isError());
    }
}
