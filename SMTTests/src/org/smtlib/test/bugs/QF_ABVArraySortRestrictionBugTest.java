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
 * Pins down the "FIXME - restricted Array sorts" at {@code logic/QF_ABV.java:30}.
 * {@code QF_ABV.smt2}'s own {@code :language} mandates "all array terms have sort of the form
 * (Array (_ BitVec i) (_ BitVec j)) for some i, j > 0" -- but {@code QF_ABV.java} implemented
 * no such restriction at all: {@code (declare-const arr (Array (_ BitVec 4) Bool))} (a
 * BitVec-to-Bool array, not BitVec-to-BitVec) was silently accepted, both as a direct
 * {@code declare-const} and as a {@code define-sort} alias.
 * <p>
 * Fixed with a new {@code Logic.checkArraySortIsBitVecToBitVec()} helper (parallel to the
 * existing {@code checkArraySort()}, but predicate-based rather than an enumerated allowed
 * set, since the BitVec widths i, j are unconstrained) called from both
 * {@code checkFcnDeclaration()} (the resultSort of a declared constant -- the common case)
 * and {@code checkSortDeclaration()} (a {@code define-sort} alias -- mirroring
 * {@code AUFLIRA}'s existing, narrower pattern, which only ever checked the latter).
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/49">issue #49</a>.
 */
public class QF_ABVArraySortRestrictionBugTest {

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

    private ISolver freshQfAbv(SMT smt) throws Exception {
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic QF_ABV)");
        return solver;
    }

    @Test
    public void acceptsBitVecToBitVecArrayDeclareConst() throws Exception {
        SMT smt = new SMT();
        ISolver solver = freshQfAbv(smt);
        IResponse r = doCommand(smt, solver, "(declare-const arr (Array (_ BitVec 4) (_ BitVec 8)))");
        Assert.assertFalse(r.isError());
    }

    @Test
    public void rejectsBitVecToBoolArrayDeclareConst() throws Exception {
        SMT smt = new SMT();
        ISolver solver = freshQfAbv(smt);
        IResponse r = doCommand(smt, solver, "(declare-const arr (Array (_ BitVec 4) Bool))");
        Assert.assertTrue("a BitVec-to-Bool array must be rejected under QF_ABV", r.isError());
    }

    @Test
    public void acceptsBitVecToBitVecArrayDefineSort() throws Exception {
        SMT smt = new SMT();
        ISolver solver = freshQfAbv(smt);
        IResponse r = doCommand(smt, solver, "(define-sort MyArr () (Array (_ BitVec 4) (_ BitVec 8)))");
        Assert.assertFalse(r.isError());
    }

    @Test
    public void rejectsBitVecToBoolArrayDefineSort() throws Exception {
        SMT smt = new SMT();
        ISolver solver = freshQfAbv(smt);
        IResponse r = doCommand(smt, solver, "(define-sort BadArr () (Array (_ BitVec 4) Bool))");
        Assert.assertTrue("a BitVec-to-Bool array alias must be rejected under QF_ABV", r.isError());
    }

    @Test
    public void quantifierNestedInsideIteConditionIsStillRejected() throws Exception {
        // Characterizes that the pre-existing FIXME about ite-term formulas is already
        // handled correctly by noQuantifiers()'s ordinary recursive traversal (QF_ABV/QF_UF
        // never override visit(IFcnExpr), so ite's condition argument is walked like any
        // other) -- confirming no behavior change was needed there, just the array-sort fix.
        SMT smt = new SMT();
        ISolver solver = freshQfAbv(smt);
        doCommand(smt, solver, "(declare-const b (_ BitVec 4))");
        IResponse r = doCommand(smt, solver, "(assert (= (ite (forall ((y Bool)) y) b b) b))");
        Assert.assertTrue(r.isError());
    }
}
