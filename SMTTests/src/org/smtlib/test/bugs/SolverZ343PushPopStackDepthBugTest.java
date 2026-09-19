package org.smtlib.test.bugs;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.IResponse;
import org.smtlib.SMT;
import org.smtlib.SolverProcess;
import org.smtlib.solvers.Solver_z3_4_3;

/**
 * Pins down issue #53: {@code Solver_z3_4_3}'s {@code pushesDepth} bookkeeping conflated two
 * different things -- the real number of open {@code (push N)} frames, and the always-present
 * base assertion frame that {@code set_logic()} establishes. {@code set_logic()} used to do
 * {@code pushesDepth++} on success with no corresponding {@code (push ...)} ever sent to the
 * real solver, so after {@code set-logic} alone (zero real pushes), {@code pushesDepth} was 1,
 * not 0. It also meant {@code reset()} left a stale {@code pushesDepth} behind (never reset to
 * 0), so a subsequent {@code set_logic()} built on top of leftover depth from before the reset.
 * <p>
 * A first attempt at fixing {@code pop()} added a client-side bound check
 * ({@code number > pushesDepth} -> error) to reject an over-large pop before ever reaching the
 * solver. That turned out to be the wrong layer to fix it at: confirmed against a real
 * z3-4.3.1 binary, z3-4.3 already validates a pop count against its own real stack depth and
 * reports a precise, line/column-annotated native error -- better diagnostics than anything
 * this adapter could produce -- so the fix instead removes the client-side check entirely and
 * defers to the solver (per the project's adapter-minimalism principle: defer to native
 * behavior when the solver is compliant, only intercept where it genuinely isn't). What
 * remains necessary is correctness of the local {@code pushesDepth} bookkeeping itself: it
 * must only be decremented once the solver actually confirms the pop succeeded, not
 * unconditionally before even asking -- otherwise a rejected pop would desync it from the
 * solver's real stack depth, corrupting later operations that depend on it (namely
 * {@code set_logic()}'s relax-mode re-entry, which does {@code pop(pushesDepth)} to clear the
 * stack before establishing a new logic).
 * <p>
 * Separately, {@code reset_assertions()} was briefly changed to simulate the command (which
 * z3-4.3 predates) by popping back to the base frame -- also reverted. z3-4.3, sent the
 * literal, unrecognized "(reset-assertions)" text, gracefully replies with the literal token
 * "unsupported" on its own (confirmed against the real binary) rather than erroring, which is
 * already the correct, honest answer for a solver that can't do this -- a pop-based simulation
 * would only partially honor the contract (it can't clear non-global declarations, which
 * reset-assertions is also supposed to clear, since this adapter doesn't track declarations
 * locally) while silently claiming success, which is worse.
 * <p>
 * Reproduced with a fake {@code SolverProcess} that records every command sent and returns
 * canned responses, without ever spawning a real z3 process.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/53">issue #53</a>.
 */
public class SolverZ343PushPopStackDepthBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    /** A SolverProcess that never touches a real process: sendAndListen() records every
     *  command sent (joined args) and returns the next canned response in order. */
    static class RecordingFakeSolverProcess extends SolverProcess {
        private final Queue<String> responses;
        final List<String> sent = new LinkedList<>();

        RecordingFakeSolverProcess(List<String> canned) {
            super(new String[]{"dummy"}, "\n", null);
            responses = new LinkedList<>(canned);
        }

        @Override
        public String sendAndListen(String... args) throws IOException {
            StringBuilder sb = new StringBuilder();
            for (String a : args) sb.append(a);
            sent.add(sb.toString());
            if (responses.isEmpty()) throw new IOException("test ran out of canned responses");
            return responses.poll();
        }
    }

    static class TestableSolver extends Solver_z3_4_3 {
        RecordingFakeSolverProcess fake;

        TestableSolver(SMT.Configuration config, List<String> cannedResponses) {
            super(config, "z3");
            fake = new RecordingFakeSolverProcess(cannedResponses);
            this.solverProcess = fake;
        }
    }

    @Test
    public void popIsForwardedToTheSolverEvenWhenLocalDepthLooksExceeded() {
        List<String> canned = new LinkedList<>();
        canned.add("success\n"); // (set-logic ...)
        // Zero real pushes have happened, so a naive client-side check would reject pop(1)
        // before ever reaching the solver. Canned response simulates z3-4.3's own real
        // rejection message for this exact scenario.
        canned.add("(error \"line 3 column 6: invalid pop command, argument is greater than the current stack depth\")\n");
        TestableSolver solver = new TestableSolver(new SMT.Configuration(), canned);
        solver.set_logic("QF_UF", null);

        IResponse r = solver.pop(1);

        Assert.assertTrue("the solver's own rejection must be forwarded, not replaced", r.isError());
        Assert.assertTrue("pop(1) must actually be sent to the solver rather than rejected locally",
                solver.fake.sent.get(solver.fake.sent.size() - 1).contains("pop"));
    }

    @Test
    public void pushesDepthIsNotDecrementedWhenTheSolverRejectsThePop() {
        List<String> canned = new LinkedList<>();
        canned.add("success\n"); // (set-logic ...)
        canned.add("success\n"); // (push 2)
        canned.add("(error \"too large\")\n"); // (pop 5) -- rejected by the (simulated) solver
        canned.add("success\n"); // (pop 2) -- set_logic()'s relax re-entry cleanup
        canned.add("success\n"); // (set-logic ...) -- sent again after the cleanup pop

        SMT.Configuration config = new SMT.Configuration();
        config.relax = true;
        TestableSolver solver = new TestableSolver(config, canned);
        solver.set_logic("QF_UF", null);
        solver.push(2);

        IResponse rejected = solver.pop(5);
        Assert.assertTrue(rejected.isError());

        // If the earlier rejected pop(5) had wrongly decremented pushesDepth anyway (2 - 5 =
        // -3), this relax-mode re-entry's internal pop(pushesDepth) would either throw
        // (pop() rejects a negative count) or send the wrong amount. A correct
        // implementation sends exactly 2 -- the real, unaffected depth.
        IResponse r = solver.set_logic("QF_UF", null);

        Assert.assertFalse("pushesDepth must not have gone negative from the rejected pop", r.isError());
        String lastPop = null;
        for (String s : solver.fake.sent) if (s.contains("pop")) lastPop = s;
        Assert.assertNotNull(lastPop);
        Assert.assertTrue("expected the cleanup pop to send the real depth (2), got: " + lastPop,
                lastPop.contains("2"));
    }

    @Test
    public void resetAssertionsForwardsTheLiteralCommandUnmodified() {
        List<String> canned = new LinkedList<>();
        canned.add("unsupported\n"); // (reset-assertions) -- z3-4.3's own real, graceful reply
        TestableSolver solver = new TestableSolver(new SMT.Configuration(), canned);

        IResponse r = solver.reset_assertions();

        Assert.assertFalse(r.isError());
        String lastSent = solver.fake.sent.get(solver.fake.sent.size() - 1);
        Assert.assertTrue("expected the literal reset-assertions command to be forwarded, got: " + lastSent,
                lastSent.contains("reset-assertions"));
    }

    @Test
    public void resetClearsPushesDepthSoALaterCleanupPopUsesTheRealDepth() {
        List<String> canned = new LinkedList<>();
        canned.add("success\n"); // (set-logic ...)
        canned.add("success\n"); // (push 2)
        canned.add("success\n"); // (reset)
        canned.add("success\n"); // (set-logic ...) again, fresh (logicSet was cleared)
        canned.add("success\n"); // (push 1)
        canned.add("success\n"); // (pop 1) -- relax re-entry cleanup on the third set_logic
        canned.add("success\n"); // (set-logic ...) -- sent again after that cleanup pop

        SMT.Configuration config = new SMT.Configuration();
        config.relax = true;
        TestableSolver solver = new TestableSolver(config, canned);
        solver.set_logic("QF_UF", null);
        solver.push(2);
        solver.reset();
        solver.set_logic("QF_UF", null);
        solver.push(1);

        // If reset() had left the old depth (2) lying around, this third set_logic's cleanup
        // pop would wrongly try to pop 1+2=3, not the real depth of 1.
        IResponse r = solver.set_logic("QF_UF", null);

        Assert.assertFalse(r.isError());
        String lastPop = null;
        for (String s : solver.fake.sent) if (s.contains("pop")) lastPop = s;
        Assert.assertNotNull(lastPop);
        Assert.assertTrue("expected the cleanup pop to reflect only the post-reset push (1), got: " + lastPop,
                lastPop.contains("1") && !lastPop.contains("3"));
    }

    @Test
    public void assertingImmediatelyAfterSetLogicWithNoPushSucceeds() {
        List<String> canned = new LinkedList<>();
        canned.add("success\n"); // (set-logic ...)
        canned.add("success\n"); // (assert ...)
        TestableSolver solver = new TestableSolver(new SMT.Configuration(), canned);
        solver.set_logic("QF_UF", null);

        IResponse r = solver.assertExpr(new SMT.Configuration().exprFactory.symbol("true"));

        Assert.assertFalse("asserting right after set-logic, with no push yet, must succeed",
                r.isError());
    }
}
