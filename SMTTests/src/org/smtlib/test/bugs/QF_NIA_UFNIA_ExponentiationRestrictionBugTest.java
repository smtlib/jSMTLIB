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
 * Resolves issue #48: confirms {@code QF_NIA}/{@code UFNIA} are correct, per the SMT-LIB spec
 * files bundled with this repo, to forbid the exponentiation operator {@code **}, and adds
 * {@code UFNIA}'s previously-missing {@code checkFcnDeclaration} override/comment (every
 * other UF-permitting sibling logic documents that inherited no-op explicitly; {@code UFNIA}
 * was the one exception).
 * <p>
 * The spec question the original issue flagged as unconfirmed is settled by the logic
 * definition files themselves, already present under {@code SMT/logics/}:
 * <ul>
 * <li>{@code QF_NIA.smt2}/{@code UFNIA.smt2}'s own {@code :language} text says, verbatim,
 * "...whose terms of sort Int have no occurrences of the function symbol **." -- an explicit,
 * unambiguous requirement, not an inferred one.
 * <li>{@code QF_EIA.smt2} exists specifically as the "QF_NIA, but ** permitted" variant --
 * {@code QF_EIA.java}'s own comment already says so: "Exponentiation (**) is permitted --
 * that is the sole difference from QF_NIA."
 * <li>The asymmetry with the NRA family isn't a gap either: {@code Reals.smt2}/{@code
 * Reals_Ints.smt2} don't declare {@code **} for sort Real at all (only {@code Ints.smt2}
 * does, added 2026-01-16 per its own update history) -- there is no real-valued
 * exponentiation operator for QF_NRA/UFNRA to restrict in the first place.
 * </ul>
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/48">issue #48</a>.
 */
public class QF_NIA_UFNIA_ExponentiationRestrictionBugTest {

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
    public void qfNiaRejectsExponentiation() throws Exception {
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic QF_NIA)");
        doCommand(smt, solver, "(declare-const x Int)");
        IResponse r = doCommand(smt, solver, "(assert (= (** x 2) 4))");
        Assert.assertTrue(r.isError());
    }

    @Test
    public void ufniaRejectsExponentiation() throws Exception {
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic UFNIA)");
        doCommand(smt, solver, "(declare-const x Int)");
        IResponse r = doCommand(smt, solver, "(assert (= (** x 2) 4))");
        Assert.assertTrue(r.isError());
    }

    @Test
    public void ufniaStillPermitsUninterpretedFunctions() throws Exception {
        // Characterizes that adding the explicit checkFcnDeclaration override (documenting
        // the previously-implicit permissive default) doesn't change behavior.
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic UFNIA)");
        IResponse r = doCommand(smt, solver, "(declare-fun f (Int) Int)");
        Assert.assertFalse(r.isError());
    }

    @Test
    public void qfEiaPermitsExponentiationAsTheDocumentedSoleDifferenceFromQfNia() throws Exception {
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic QF_EIA)");
        doCommand(smt, solver, "(declare-const x Int)");
        IResponse r = doCommand(smt, solver, "(assert (= (** x 2) 4))");
        Assert.assertFalse(r.isError());
    }
}
