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
 * Resolves issue #40. The original report worried that {@code TypeChecker.validate()} --
 * the universal, solver-agnostic pre-dispatch check {@code SMT.java} runs on every command --
 * never checks a {@code define-fun}/{@code define-fun-rec} body's sort against its declared
 * result sort, and that {@code C_define_fun.java}/{@code C_define_fun_rec.java} both carry a
 * stale FIXME about it.
 * <p>
 * The issue's own follow-up correction (already on the tracker) narrows this considerably:
 * {@code Solver_test.define_fun()} (and {@code Solver_simplify}'s) separately call {@code
 * TypeChecker.checkFcn()}, which *does* perform this exact check -- confirmed here again
 * directly. The real, narrower gap is that this check lives only in {@code checkFcn()}, not
 * in the universal {@code validate()} pass, so real solver adapters never run it locally and
 * depend entirely on the real solver's own type-checking.
 * <p>
 * That's a deliberate consequence of this project's established design (see #46/#53's
 * discussion): jSMTLIB's real-solver adapters intentionally don't duplicate semantic checks a
 * real solver already performs and reports itself -- forwarding the raw command and trusting
 * the real solver's own error is the norm, not a gap, for the adapters that talk to actual
 * processes. Moving this into {@code validate()} would both duplicate {@code checkFcn()}'s
 * check for {@code test}/{@code simplify} and add a new client-side check for every other
 * adapter that breaks that established pattern. Resolved by documenting this instead (see
 * the updated comments in {@code C_define_fun.java}/{@code C_define_fun_rec.java}) rather
 * than centralizing the check -- no behavior change.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/40">issue #40</a>.
 */
public class DefineFunResultSortCheckCharacterizationBugTest {

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
    public void defineFunResultSortMismatchIsRejectedByTheTestSolver() throws Exception {
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic QF_UF)");

        IResponse r = doCommand(smt, solver, "(define-fun f () Bool 5)");
        Assert.assertTrue(r.isError());
    }

    @Test
    public void defineFunRecResultSortMismatchIsRejectedByTheTestSolver() throws Exception {
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic QF_UF)");

        IResponse r = doCommand(smt, solver, "(define-fun-rec f () Bool 5)");
        Assert.assertTrue(r.isError());
    }

    @Test
    public void matchingResultSortIsAccepted() throws Exception {
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic QF_UF)");

        // QF_UF only loads Core (Bool); use Bool, not Int, as the matching sort.
        IResponse r = doCommand(smt, solver, "(define-fun f () Bool true)");
        Assert.assertFalse(r.isError());
    }
}
