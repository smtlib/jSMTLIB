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
 * Characterizes (and, once fixed, pins down as unchanged) the observable behavior of four
 * {@code logic/} classes whose inheritance structure doesn't reuse a sibling class the way the
 * real-arithmetic (LRA) family does, per the pattern flagged in the issue:
 * <ul>
 * <li>{@code QF_LIA} and {@code QF_UFLIA} each re-implemented the same linearity check inline
 * instead of extending {@code LIA} and calling {@code super.validExpression()}, the way
 * {@code QF_LRA}/{@code UFLRA}/{@code QF_UFLRA} all correctly {@code extends LRA} and reuse its
 * check.
 * <li>{@code QF_UFBV} manually rewrote empty {@code checkFcnDeclaration}/{@code
 * checkSortDeclaration} overrides that {@code extends QF_UF} gives for free, as {@code QF_ABV}
 * and {@code QF_AUFBV} already demonstrate.
 * <li>{@code QF_UFIDL extends QF_IDL} was vestigial: {@code QF_UFIDL} overrode all three hooks
 * itself, so nothing was actually inherited -- and per {@code QF_UFIDL.smt2}'s own {@code :note},
 * "the syntax of this logic is *not* an extension of QF_IDL's syntax", so the {@code extends
 * QF_IDL} relationship was actively misleading, not merely redundant.
 * </ul>
 * This test only characterizes externally observable behavior (quantifier rejection, linearity,
 * and function/sort-declaration permissions) through the ordinary command pipeline against the
 * mock "test" solver -- it doesn't care how each class arrives at that behavior. It was written,
 * and confirmed passing, against the pre-refactor (duplicated) code, then re-confirmed passing
 * after each class was restructured to reuse its sibling via inheritance -- proving the
 * refactor is behavior-preserving, not just less repetitive.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/47">issue #47</a>.
 */
public class LogicFamilyInheritanceBugTest {

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

    // ---- QF_LIA: quantifier-free, linear-only, no UF, no new sorts ----

    @Test
    public void qfLiaRejectsQuantifiers() throws Exception {
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic QF_LIA)");
        IResponse r = doCommand(smt, solver, "(assert (forall ((y Int)) (>= y 0)))");
        Assert.assertTrue(r.isError());
    }

    @Test
    public void qfLiaRejectsNonlinearMultiplication() throws Exception {
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic QF_LIA)");
        doCommand(smt, solver, "(declare-const x Int)");
        doCommand(smt, solver, "(declare-const y Int)");
        IResponse r = doCommand(smt, solver, "(assert (= (* x y) 0))");
        Assert.assertTrue(r.isError());
    }

    @Test
    public void qfLiaAcceptsLinearMultiplication() throws Exception {
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic QF_LIA)");
        doCommand(smt, solver, "(declare-const x Int)");
        IResponse r = doCommand(smt, solver, "(assert (= (* 3 x) 0))");
        Assert.assertFalse(r.isError());
    }

    @Test
    public void qfLiaRejectsFunctionDeclarations() throws Exception {
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic QF_LIA)");
        IResponse r = doCommand(smt, solver, "(declare-fun f (Int) Int)");
        Assert.assertTrue(r.isError());
    }

    @Test
    public void qfLiaRejectsNewSorts() throws Exception {
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic QF_LIA)");
        IResponse r = doCommand(smt, solver, "(declare-sort S 0)");
        Assert.assertTrue(r.isError());
    }

    // ---- QF_UFLIA: same linearity rules as QF_LIA, but UF and new sorts permitted ----

    @Test
    public void qfUfliaRejectsQuantifiers() throws Exception {
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic QF_UFLIA)");
        IResponse r = doCommand(smt, solver, "(assert (forall ((y Int)) (>= y 0)))");
        Assert.assertTrue(r.isError());
    }

    @Test
    public void qfUfliaRejectsNonlinearMultiplication() throws Exception {
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic QF_UFLIA)");
        doCommand(smt, solver, "(declare-const x Int)");
        doCommand(smt, solver, "(declare-const y Int)");
        IResponse r = doCommand(smt, solver, "(assert (= (* x y) 0))");
        Assert.assertTrue(r.isError());
    }

    @Test
    public void qfUfliaAcceptsFunctionAndSortDeclarations() throws Exception {
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic QF_UFLIA)");
        Assert.assertFalse(doCommand(smt, solver, "(declare-fun f (Int) Int)").isError());
        Assert.assertFalse(doCommand(smt, solver, "(declare-sort S 0)").isError());
    }

    // ---- QF_UFBV: quantifier-free, UF and new sorts permitted (mirrors QF_UF) ----

    @Test
    public void qfUfbvRejectsQuantifiers() throws Exception {
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic QF_UFBV)");
        IResponse r = doCommand(smt, solver, "(assert (forall ((y Bool)) y))");
        Assert.assertTrue(r.isError());
    }

    @Test
    public void qfUfbvAcceptsFunctionAndSortDeclarations() throws Exception {
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic QF_UFBV)");
        Assert.assertFalse(doCommand(smt, solver, "(declare-fun f (Bool) Bool)").isError());
        Assert.assertFalse(doCommand(smt, solver, "(declare-sort S 0)").isError());
    }

    // ---- QF_UFIDL: quantifier-free; per its own :note its syntax is *not* an extension of
    // QF_IDL's, so QF_IDL's atom-shape restriction must never leak through. ----

    @Test
    public void qfUfidlRejectsQuantifiers() throws Exception {
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic QF_UFIDL)");
        IResponse r = doCommand(smt, solver, "(assert (forall ((y Int)) (>= y 0)))");
        Assert.assertTrue(r.isError());
    }

    @Test
    public void qfUfidlAcceptsFunctionAndSortDeclarations() throws Exception {
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic QF_UFIDL)");
        Assert.assertFalse(doCommand(smt, solver, "(declare-fun f (Int) Int)").isError());
        Assert.assertFalse(doCommand(smt, solver, "(declare-sort S 0)").isError());
    }

    @Test
    public void qfUfidlDoesNotEnforceQfIdlAtomShape() throws Exception {
        // (= (+ x y) 3) is a shape QF_IDL's own atom-shape restriction (were it inherited)
        // would reject outright -- QF_IDL only recognizes "-" differences, not "+", as a
        // comparison operand. QF_UFIDL's own validExpression() deliberately does not enforce
        // QF_IDL's atom shape (its :note says its syntax is not an extension of QF_IDL's).
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic QF_UFIDL)");
        doCommand(smt, solver, "(declare-const x Int)");
        doCommand(smt, solver, "(declare-const y Int)");
        IResponse r = doCommand(smt, solver, "(assert (= (+ x y) 3))");
        Assert.assertFalse(r.isError());
    }
}
