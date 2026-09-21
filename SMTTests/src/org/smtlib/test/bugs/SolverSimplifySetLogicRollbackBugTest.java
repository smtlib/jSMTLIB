package org.smtlib.test.bugs;

import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.IResponse;
import org.smtlib.SMT;
import org.smtlib.solvers.Solver_simplify;

/**
 * Pins down {@code Solver_simplify.set_logic()} (Solver_simplify.java:358-372): it called
 * {@code super.set_logic(...)} -- fully committing the new logic to the symbol table and
 * {@code logicSet} field -- *before* checking whether the logic name contains "BV" and should be
 * rejected (Simplify doesn't support bit-vectors). On rejection there was no rollback: the
 * command reported failure, but the solver was left thinking a logic had already been set, as if
 * the rejected logic had actually taken effect.
 * <p>
 * Observable symptom: after a rejected {@code (set-logic QF_BV)}, a subsequent, otherwise
 * perfectly valid {@code (set-logic QF_UF)} incorrectly failed with "Logic is already set"
 * (the same guard {@code Solver_test.set_logic()} uses for a genuine double set-logic) --
 * instead of succeeding, since no logic had actually been validly set yet.
 * <p>
 * Fixed by checking the BV-name rejection before calling {@code super.set_logic(...)}, so a
 * rejected logic never partially commits.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/54">issue #54</a>.
 * <p>
 * Stays a JUnit test: no Simplify binary is available in any local or CI-configured solver
 * directory (it is excluded from the test-solver list entirely when missing, per
 * {@code LogicTests.solversFromEnv()}), so a {@code --solver simplify} script test can't be
 * authored and verified against the real command-line tool here.
 */
public class SolverSimplifySetLogicRollbackBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    @Test
    public void rejectedBvLogicDoesNotBlockASubsequentValidSetLogic() {
        SMT.Configuration config = new SMT.Configuration();
        Solver_simplify solver = new Solver_simplify(config, "simplify");

        IResponse rejected = solver.set_logic("QF_BV", null);
        Assert.assertTrue("QF_BV must be rejected -- simplify doesn't support bit-vectors",
                rejected.isError());

        IResponse afterRejection = solver.set_logic("QF_UF", null);
        Assert.assertFalse(
                "a rejected set-logic must not leave the solver thinking a logic is already set: "
                + (afterRejection.isError() ? ((IResponse.IError) afterRejection).errorMsg() : ""),
                afterRejection.isError());
    }
}
