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
import org.smtlib.solvers.Solver_z3_4_3_2;

/**
 * Pins down issue #52: {@code Solver_z3_4_3_2.push()}'s echo-marker drain loop
 * (Solver_z3_4_3_2.java:38-44) works around a real z3-4.3.2 bug (push can print more than
 * one success message) by sending {@code (push N)} followed by {@code (echo "<<DONE>>")},
 * then looping {@code listen()} until the {@code <<DONE>>} marker appears -- but the loop
 * reassigns its local variable each iteration rather than accumulating it, and unconditionally
 * returns success once the marker shows up, regardless of what was actually drained. A genuine
 * {@code (error ...)} response to the push -- the process stays alive and still processes the
 * following echo normally, so the marker does arrive -- is silently discarded, and push()
 * reports success anyway.
 * <p>
 * (The issue's "infinite loop" framing is only partly live: {@code SolverProcess.listen()}
 * already throws {@code NoResponseException} on a forced EOF with no output on either stream,
 * which push()'s existing {@code catch (Exception e)} already turns into a clean error --
 * confirmed by reading {@code SolverProcess.listen()} directly. The genuinely unaddressed gap
 * is the discarded error text, which this test and fix target.)
 * <p>
 * Fixed by accumulating everything drained before the marker and checking it for an
 * {@code (error} before falling back to success -- so the original duplicate-success
 * workaround still works (characterized here too), but a real error is no longer swallowed.
 * <p>
 * Reproduced with a fake {@code SolverProcess} that returns canned responses without ever
 * spawning a real z3 process.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/52">issue #52</a>.
 * <p>
 * Stays a JUnit test: it needs a fake {@code SolverProcess} handing back exact canned
 * responses (including a real z3-4.3.2 duplicate-success quirk) -- not reproducible against a
 * real solver process, whose exact response text/timing can't be scripted this precisely.
 */
public class SolverZ3432PushDiscardsErrorBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    /** A SolverProcess that never touches a real process: sendNoListen() is a no-op, and
     *  listen() returns canned responses in order. */
    static class FakeSolverProcess extends SolverProcess {
        private final Queue<String> responses;

        FakeSolverProcess(List<String> canned) {
            super(new String[]{"dummy"}, "\n", null);
            responses = new LinkedList<>(canned);
        }

        @Override
        public void sendNoListen(String... args) {
            // discard -- nothing to send to
        }

        @Override
        public String listen() throws IOException {
            if (responses.isEmpty()) throw new IOException("test ran out of canned responses");
            return responses.poll();
        }
    }

    static class TestableSolver extends Solver_z3_4_3_2 {
        TestableSolver(SMT.Configuration config, List<String> cannedResponses) {
            super(config, "z3");
            this.solverProcess = new FakeSolverProcess(cannedResponses);
            this.logicSet = true;
        }
    }

    @Test
    public void pushReportsAGenuineErrorInsteadOfDiscardingIt() {
        List<String> canned = new LinkedList<>();
        canned.add("(error \"stack is empty\")\n");
        canned.add("<<DONE>>\n");
        TestableSolver solver = new TestableSolver(new SMT.Configuration(), canned);

        IResponse r = solver.push(1);
        Assert.assertTrue("a genuine push error must not be reported as success", r.isError());
    }

    @Test
    public void pushStillSucceedsOnTheOriginalDuplicateSuccessQuirk() {
        // The actual z3-4.3.2 bug this workaround exists for: push can print success twice.
        // Must still be treated as success, not misdiagnosed as an error.
        List<String> canned = new LinkedList<>();
        canned.add("success\n");
        canned.add("success\n");
        canned.add("<<DONE>>\n");
        TestableSolver solver = new TestableSolver(new SMT.Configuration(), canned);

        IResponse r = solver.push(1);
        Assert.assertFalse(r.isError());
    }

    @Test
    public void pushSucceedsWhenMarkerArrivesInTheFirstListenCall() {
        List<String> canned = new LinkedList<>();
        canned.add("success\n<<DONE>>\n");
        TestableSolver solver = new TestableSolver(new SMT.Configuration(), canned);

        IResponse r = solver.push(1);
        Assert.assertFalse(r.isError());
    }
}
