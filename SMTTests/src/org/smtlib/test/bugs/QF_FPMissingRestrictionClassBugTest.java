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
 * Pins down the gap in <a href="https://github.com/smtlib/jSMTLIB/issues/89">issue #89</a>:
 * {@code QF_FP.smt2} (a jSMTLIB-invented convenience logic -- see its own {@code :notes}; not
 * an official SMT-LIB logic) has no matching {@code org.smtlib.logic.QF_FP} restriction class.
 * Per #46, {@code sexpr/Parser}'s logic-class loader falls back to an unrestricted
 * {@code SMTExpr.Logic} whenever no matching class exists, so nothing QF_FP.smt2's own
 * {@code :language} text claims -- "Closed quantifier-free formulas ... with free constant
 * symbols" -- was actually enforced: a quantifier and a declared function both silently
 * succeeded under QF_FP.
 * <p>
 * Fixed by adding {@code QF_FP.java} with the same {@code noQuantifiers}/{@code
 * noFunctions}/{@code noSorts} restrictions every other quantifier-free, no-UF, no-new-sorts
 * logic in this package already has.
 */
public class QF_FPMissingRestrictionClassBugTest {

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

    private ISolver freshQfFp(SMT smt) throws Exception {
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic QF_FP)");
        return solver;
    }

    @Test
    public void rejectsQuantifiers() throws Exception {
        SMT smt = new SMT();
        ISolver solver = freshQfFp(smt);
        IResponse r = doCommand(smt, solver, "(assert (forall ((x Real)) (= x x)))");
        Assert.assertTrue(r.isError());
    }

    @Test
    public void rejectsFunctionDeclarations() throws Exception {
        SMT smt = new SMT();
        ISolver solver = freshQfFp(smt);
        IResponse r = doCommand(smt, solver, "(declare-fun f (Real) Real)");
        Assert.assertTrue(r.isError());
    }

    @Test
    public void rejectsNewSorts() throws Exception {
        SMT smt = new SMT();
        ISolver solver = freshQfFp(smt);
        IResponse r = doCommand(smt, solver, "(declare-sort S 0)");
        Assert.assertTrue(r.isError());
    }

    @Test
    public void acceptsFreeConstantsOfTheAllowedSorts() throws Exception {
        SMT smt = new SMT();
        ISolver solver = freshQfFp(smt);
        Assert.assertFalse(doCommand(smt, solver, "(declare-const r Real)").isError());
        Assert.assertFalse(doCommand(smt, solver, "(declare-const bv (_ BitVec 8))").isError());
        Assert.assertFalse(doCommand(smt, solver, "(declare-const f (_ FloatingPoint 8 24))").isError());
    }
}
