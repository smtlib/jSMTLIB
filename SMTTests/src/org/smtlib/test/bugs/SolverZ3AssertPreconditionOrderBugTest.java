package org.smtlib.test.bugs;

import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.IResponse;
import org.smtlib.SMT;
import org.smtlib.solvers.Solver_z3_4_3;

/**
 * Pins down Solver_z3_4_3.assertExpr()'s precondition-check order (Solver_z3_4_3.java:266-272):
 * {@code pushesDepth <= 0} was checked before {@code !logicSet}. {@code pushesDepth} starts at 0
 * and is only incremented by {@code set_logic()}, so an {@code assert} issued before any
 * {@code set-logic} reported "All assertion sets have been popped from the stack" instead of
 * "The logic must be set before an assert command is issued".
 * <p>
 * Confirmed against the repo's own golden files: {@code SMTTests/tests/assert/err_assertWithNoLogic.tst.out}
 * (the correct/bare expectation) says "The logic must be set before an assert command is issued";
 * the real z3-captured golden for the same adapter, {@code err_assertWithNoLogic.tst.out.z3-4.3},
 * said "All assertion sets have been popped from the stack" instead -- already flagged
 * non-conforming under the project's own {@code .bad} convention
 * ({@code err_assertWithNoLogic.tst.out.z3.bad}).
 * <p>
 * Reproduced directly against a freshly constructed Solver_z3_4_3 -- no live z3 process needed,
 * since both preconditions return before the solver process is touched.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/50">issue #50</a>.
 */
public class SolverZ3AssertPreconditionOrderBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    @Test
    public void assertBeforeSetLogicReportsMissingLogicNotEmptyStack() {
        SMT.Configuration config = new SMT.Configuration();
        Solver_z3_4_3 solver = new Solver_z3_4_3(config, "z3");

        // Neither set_logic() nor push()/pop() has been called: pushesDepth == 0 and
        // logicSet == false. assertExpr() must report the missing logic, not "stack popped"
        // -- the sexpr argument is never dereferenced before the precondition checks return.
        IResponse response = solver.assertExpr(null);

        Assert.assertTrue("expected an error response", response.isError());
        Assert.assertEquals("The logic must be set before an assert command is issued",
                ((IResponse.IError) response).errorMsg());
    }
}
