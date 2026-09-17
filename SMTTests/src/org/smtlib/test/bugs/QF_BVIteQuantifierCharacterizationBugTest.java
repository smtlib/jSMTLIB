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
 * Pins down the (now resolved) FIXME at {@code logic/QF_BV.java:34-36}, which quoted
 * {@code QF_BV.smt2}'s own {@code :language} text -- "Formulas in ite terms must satisfy the
 * same restriction as well [quantifier-freedom], with the exception that they need not be
 * closed" -- and asked "what does this mean", without ever implementing anything for it.
 * <p>
 * Confirmed here that nothing extra was actually needed: {@code QF_BV.validExpression()}'s
 * {@code noQuantifiers()} call recurses into every subexpression via the ordinary
 * {@code IVisitor.TreeVisitor} traversal (since {@code QF_BV} never overrides
 * {@code visit(IFcnExpr)} the way {@code QF_IDL} did before issue #44's fix), so a quantifier
 * nested inside an {@code ite}'s condition argument is already rejected, same as one anywhere
 * else in the formula. This is a characterization test (no code change), confirming the FIXME
 * was stale, not an open gap.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/49">issue #49</a>.
 */
public class QF_BVIteQuantifierCharacterizationBugTest {

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
    public void quantifierNestedInsideIteConditionIsRejected() throws Exception {
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic QF_BV)");
        doCommand(smt, solver, "(declare-const b (_ BitVec 4))");
        IResponse r = doCommand(smt, solver, "(assert (= (ite (forall ((y Bool)) y) b b) b))");
        Assert.assertTrue(r.isError());
    }

    @Test
    public void iteWithoutAQuantifierIsAccepted() throws Exception {
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic QF_BV)");
        doCommand(smt, solver, "(declare-const b (_ BitVec 4))");
        doCommand(smt, solver, "(declare-const c Bool)");
        IResponse r = doCommand(smt, solver, "(assert (= (ite c b b) b))");
        Assert.assertFalse(r.isError());
    }
}
