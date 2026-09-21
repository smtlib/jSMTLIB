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
 * Pins down issue #56 (the z3-4.3 half): {@code Solver_z3_4_3.check_sat()} detects
 * sat/unsat/error purely by substring-matching the raw response text
 * ({@code s.contains("unsat")}, {@code s.contains("sat")}), self-flagged with
 * {@code // FIXME - detect errors} in its own source. A genuine solver error (or any other
 * response text) that doesn't happen to contain "sat" is silently downgraded to
 * {@code unknown} rather than surfaced as an error -- even though this same class already has
 * a real, quirk-aware s-expression response parser ({@link Solver_z3_4_3#parseResponse}, used
 * by every other command) that correctly recognizes {@code (error ...)} responses.
 * <p>
 * Fixed by routing {@code check_sat()} through the same {@code sendCommand()} pipeline
 * (translate -> send -> {@code parseResponse()}) that every other command in this class
 * already uses, instead of hand-rolled substring matching.
 * <p>
 * Reproduced with a fake {@code SolverProcess} that returns a canned response without ever
 * spawning a real z3 process.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/56">issue #56</a>.
 * <p>
 * Stays a JUnit test: it needs a fake {@code SolverProcess} handing back a canned error
 * response that happens not to contain "sat" -- not reliably reproducible against a real
 * solver process, whose actual error wording can't be scripted this precisely.
 */
public class SolverZ343CheckSatSubstringMatchingBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    /** A SolverProcess that never touches a real process: sendAndListen() returns the next
     *  canned response in order, and it always reports itself as running. */
    static class FakeSolverProcess extends SolverProcess {
        private final Queue<String> responses;

        FakeSolverProcess(List<String> canned) {
            super(new String[]{"dummy"}, "\n", null);
            responses = new LinkedList<>(canned);
        }

        @Override
        public String sendAndListen(String... args) throws IOException {
            if (responses.isEmpty()) throw new IOException("test ran out of canned responses");
            return responses.poll();
        }

        @Override
        public boolean isRunning(boolean expectStopped) {
            return true;
        }
    }

    static class TestableSolver extends Solver_z3_4_3 {
        TestableSolver(SMT.Configuration config, String cannedResponse) {
            super(config, "z3");
            List<String> canned = new LinkedList<>();
            canned.add(cannedResponse);
            this.solverProcess = new FakeSolverProcess(canned);
            this.logicSet = true;
        }
    }

    @Test
    public void checkSatReportsAGenuineErrorInsteadOfDowngradingToUnknown() {
        // A real z3 error response that happens not to contain the substring "sat" anywhere.
        TestableSolver solver = new TestableSolver(new SMT.Configuration(), "(error \"line 1 column 5: unknown constant x\")\n");

        IResponse r = solver.check_sat();
        Assert.assertTrue("a genuine check-sat error must not be downgraded to unknown", r.isError());
    }

    @Test
    public void checkSatStillReportsSat() {
        SMT.Configuration config = new SMT.Configuration();
        TestableSolver solver = new TestableSolver(config, "sat\n");
        IResponse r = solver.check_sat();
        Assert.assertEquals(config.responseFactory.sat(), r);
    }

    @Test
    public void checkSatStillReportsUnsat() {
        SMT.Configuration config = new SMT.Configuration();
        TestableSolver solver = new TestableSolver(config, "unsat\n");
        IResponse r = solver.check_sat();
        Assert.assertEquals(config.responseFactory.unsat(), r);
    }
}
