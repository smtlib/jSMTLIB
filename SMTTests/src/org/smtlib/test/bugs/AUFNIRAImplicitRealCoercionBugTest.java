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
 * Pins down the FIXME in {@code logic/AUFNIRA.java} ("needs to allow implicit casts").
 * {@code AUFNIRA.java} (and {@code AUFLIRA.java}, which shares the same extension and the
 * same underlying code path) is a no-op restriction class by design -- everything it would
 * plausibly restrict (UF, arbitrary sorts, nonlinear arithmetic, quantifiers) is explicitly
 * permitted per its own {@code :language}/{@code :notes}. The FIXME instead points at
 * {@code AUFNIRA.smt2}'s {@code :extensions} clause: "for every ... term t1 ... of sort Int
 * and t of sort Real, (op t1 t) is syntactic sugar for (op (to_real t1) t)", including
 * "(/ t1 t2) is syntactic sugar for (/ (to_real t1) (to_real t2))".
 * <p>
 * That coercion is implemented generically in {@code TypeChecker.visit(IFcnExpr)} (not in
 * {@code AUFNIRA.java} itself, which has no sort information to work with) -- but only when
 * the failed overload lookup already has at least one argument of sort Real to borrow a
 * concrete Real sort from. A term with ALL-Int arguments, like {@code (/ x x)}, never
 * triggers it: Reals_Ints declares only {@code (/ Real Real Real)}, no {@code (/ Int Int
 * Real)} overload, and since no argument is already Real-sorted, the coercion retry never
 * fires -- so a completely legitimate {@code (/ x x)} between two Int constants was rejected
 * as "Argument 1 of / has sort Int, expected Real", even though every Int argument here
 * should be implicitly widened to Real per the extension.
 * <p>
 * Mixed-sort cases like {@code (< x y)} (x: Int, y: Real) already worked, since one argument
 * was already Real-sorted for the retry to key off of -- confirming this is specifically an
 * all-Int-arguments gap, not a general absence of the coercion.
 * <p>
 * Fixed by triggering the coercion retry whenever any argument is Int-sorted (not only when
 * another argument is already Real-sorted), substituting a freshly constructed Real sort for
 * every Int-sorted argument.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/49">issue #49</a>.
 */
public class AUFNIRAImplicitRealCoercionBugTest {

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
    public void auflniraDivisionOfTwoIntsIsWidenedToReal() throws Exception {
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic AUFNIRA)");
        doCommand(smt, solver, "(declare-const x Int)");
        IResponse r = doCommand(smt, solver, "(assert (= (/ x x) 1.0))");
        Assert.assertFalse("expected (/ x x) to be widened to (/ (to_real x) (to_real x)): "
                + (r.isError() ? ((IResponse.IError) r).errorMsg() : ""), r.isError());
    }

    @Test
    public void aufliraDivisionOfTwoIntConstantsIsWidenedToReal() throws Exception {
        // AUFLIRA additionally requires linear arithmetic, so (unlike AUFNIRA) this needs a
        // division of two Int *constants* -- (/ x x) would legitimately fail AUFLIRA's own
        // linearity check (dividing by a free variable), independent of Int/Real widening.
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic AUFLIRA)");
        IResponse r = doCommand(smt, solver, "(assert (= (/ 4 2) 2.0))");
        Assert.assertFalse("expected (/ 4 2) to be widened to (/ (to_real 4) (to_real 2)): "
                + (r.isError() ? ((IResponse.IError) r).errorMsg() : ""), r.isError());
    }

    @Test
    public void mixedIntRealComparisonStillWorks() throws Exception {
        // Characterizes the already-working case, so a regression here would show up
        // alongside the all-Int fix.
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic AUFNIRA)");
        doCommand(smt, solver, "(declare-const x Int)");
        doCommand(smt, solver, "(declare-const y Real)");
        IResponse r = doCommand(smt, solver, "(assert (< x y))");
        Assert.assertFalse(r.isError());
    }

    @Test
    public void genuineSortMismatchIsStillRejected() throws Exception {
        // Characterizes that broadening the coercion doesn't start accepting everything --
        // an Int-vs-Bool mismatch has no widening rule and must still be rejected.
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic AUFNIRA)");
        doCommand(smt, solver, "(declare-const x Int)");
        doCommand(smt, solver, "(declare-const b Bool)");
        IResponse r = doCommand(smt, solver, "(assert (< x b))");
        Assert.assertTrue(r.isError());
    }
}
