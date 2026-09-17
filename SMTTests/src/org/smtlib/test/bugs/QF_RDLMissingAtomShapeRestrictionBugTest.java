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
 * Pins down the FIXME at {@code logic/QF_RDL.java:31} ("additional restrictions on
 * expressions"): {@code QF_RDL.validExpression()} only called {@code noQuantifiers()} --
 * unlike its integer-difference-logic sibling {@code QF_IDL}, it implemented no atom-shape
 * restriction at all, so any Real-sorted formula (nonlinear multiplication, arbitrary
 * comparisons, anything) was silently accepted.
 * <p>
 * Fixed by giving {@code QF_RDL} the same atom-shape restriction {@code QF_IDL} already has
 * (post issue #44's recursion fix) -- {@code (op x y)} and {@code (op (- x y) c)} for Real
 * symbols/decimals -- deliberately matching {@code QF_IDL}'s existing level of completeness
 * (the CORE subset of {@code QF_RDL.smt2}'s grammar) rather than the full spec grammar (which
 * additionally allows a bare Bool atom, {@code distinct}, n-ary repeated-sum differences, and
 * a {@code (/ c n)} abbreviation -- none of which any sibling class in this package attempts
 * either).
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/49">issue #49</a>.
 */
public class QF_RDLMissingAtomShapeRestrictionBugTest {

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

    private ISolver freshQfRdl(SMT smt) throws Exception {
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic QF_RDL)");
        doCommand(smt, solver, "(declare-const x Real)");
        doCommand(smt, solver, "(declare-const y Real)");
        return solver;
    }

    @Test
    public void acceptsSymbolComparison() throws Exception {
        SMT smt = new SMT();
        ISolver solver = freshQfRdl(smt);
        Assert.assertFalse(doCommand(smt, solver, "(assert (>= x y))").isError());
    }

    @Test
    public void acceptsSymbolVsDecimalConstant() throws Exception {
        // (<= x 5.0) -- a single-variable bound against a real constant. Diverges
        // deliberately from QF_IDL's own, separately-tested, stricter
        // symbol-vs-symbol-only quirk: tests/logics/ok_QF_RDL.tst already established this
        // exact shape as valid QF_RDL input before this restriction existed at all.
        SMT smt = new SMT();
        ISolver solver = freshQfRdl(smt);
        Assert.assertFalse(doCommand(smt, solver, "(assert (<= x 5.0))").isError());
    }

    @Test
    public void acceptsDifferenceVsPositiveDecimal() throws Exception {
        SMT smt = new SMT();
        ISolver solver = freshQfRdl(smt);
        Assert.assertFalse(doCommand(smt, solver, "(assert (>= (- x y) 3.0))").isError());
    }

    @Test
    public void acceptsDifferenceVsNegatedDecimal() throws Exception {
        SMT smt = new SMT();
        ISolver solver = freshQfRdl(smt);
        Assert.assertFalse(doCommand(smt, solver, "(assert (>= (- x y) (- 3.0)))").isError());
    }

    @Test
    public void rejectsDifferenceArgsThatAreNotBothSymbols() throws Exception {
        SMT smt = new SMT();
        ISolver solver = freshQfRdl(smt);
        Assert.assertTrue(doCommand(smt, solver, "(assert (>= (- x 1.0) y))").isError());
    }

    @Test
    public void rejectsInvalidAtomNestedInsideAnd() throws Exception {
        // Same invalid shape as above, but nested one level inside an "and" -- exercises the
        // and/or/not/implies recursion at the same time (written correctly from the start
        // this time, learning from issue #44's QF_IDL recursion bug).
        SMT smt = new SMT();
        ISolver solver = freshQfRdl(smt);
        IResponse r = doCommand(smt, solver, "(assert (and (>= x y) (>= (- x 1.0) y)))");
        Assert.assertTrue(r.isError());
    }

    @Test
    public void acceptsValidAtomsNestedInsideAnd() throws Exception {
        SMT smt = new SMT();
        ISolver solver = freshQfRdl(smt);
        IResponse r = doCommand(smt, solver, "(assert (and (>= (- x y) 3.0) (<= (- y x) 5.0)))");
        Assert.assertFalse(r.isError());
    }

    @Test
    public void rejectsNonlinearMultiplicationAsComparisonLhs() throws Exception {
        SMT smt = new SMT();
        ISolver solver = freshQfRdl(smt);
        Assert.assertTrue(doCommand(smt, solver, "(assert (>= (* x y) 0.0))").isError());
    }

    @Test
    public void rejectsQuantifiers() throws Exception {
        SMT smt = new SMT();
        ISolver solver = freshQfRdl(smt);
        Assert.assertTrue(doCommand(smt, solver, "(assert (forall ((a Real)) (>= a 0.0)))").isError());
    }

    @Test
    public void rejectsFunctionDeclarations() throws Exception {
        SMT smt = new SMT();
        ISolver solver = freshQfRdl(smt);
        Assert.assertTrue(doCommand(smt, solver, "(declare-fun f (Real) Real)").isError());
    }

    @Test
    public void rejectsNewSorts() throws Exception {
        SMT smt = new SMT();
        ISolver solver = freshQfRdl(smt);
        Assert.assertTrue(doCommand(smt, solver, "(declare-sort S 0)").isError());
    }
}
