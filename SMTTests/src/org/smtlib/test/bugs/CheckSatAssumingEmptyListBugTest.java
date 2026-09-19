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
 * Pins down issue #38: {@code C_check_sat_assuming.parse()} shared {@code IParser}'s default
 * {@code parseListTerms()}, which hard-codes {@code allowEmpty = false} -- correct for
 * {@code get-value}'s {@code ( <term>+ )} grammar, but wrong for {@code check-sat-assuming},
 * whose own grammar is {@code ( <prop_literal>* )}, zero or more (equivalent to a plain
 * {@code check-sat} when empty). {@code (check-sat-assuming ())} -- syntactically legal --
 * was rejected with "Expected a parenthesized list of at least one term."
 * <p>
 * Fixed by giving {@code C_check_sat_assuming.parse()} its own {@code parseList} call with
 * {@code allowEmpty = true}.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/38">issue #38</a>.
 */
public class CheckSatAssumingEmptyListBugTest {

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
    public void emptyAssumptionListIsAccepted() throws Exception {
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic QF_UF)");
        doCommand(smt, solver, "(assert true)");

        IResponse r = doCommand(smt, solver, "(check-sat-assuming ())");
        Assert.assertFalse("expected (check-sat-assuming ()) to be accepted, equivalent to "
                + "a plain check-sat: " + (r.isError() ? ((IResponse.IError) r).errorMsg() : ""),
                r.isError());
    }

    @Test
    public void nonEmptyAssumptionListStillWorks() throws Exception {
        SMT smt = new SMT();
        ISolver solver = newTestSolver(smt);
        doCommand(smt, solver, "(set-logic QF_UF)");
        doCommand(smt, solver, "(declare-const b Bool)");
        doCommand(smt, solver, "(assert true)");

        IResponse r = doCommand(smt, solver, "(check-sat-assuming (b))");
        Assert.assertFalse(r.isError());
    }
}
