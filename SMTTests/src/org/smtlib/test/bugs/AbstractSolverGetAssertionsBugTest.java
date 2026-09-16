package org.smtlib.test.bugs;

import java.io.IOException;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.AbstractSolver;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IResponse;
import org.smtlib.SMT;
import org.smtlib.SolverProcess;
import org.smtlib.Utils;

/**
 * Pins down AbstractSolver.java:459-474 (get_assertions()): the multi-read loop calls
 * solverProcess.sendAndListen(cmdText, "\n") on EVERY iteration -- re-sending the same
 * get-assertions command rather than just continuing to listen -- whenever its own
 * quote-unaware paren-balance heuristic comes up short after one response and has to read
 * again.
 * <p>
 * Uses a fake SolverProcess (never started -- no real process is spawned; sendNoListen()/
 * sendAndListen()/listen() are simply overridden) to observe exactly which method the loop
 * calls on each iteration, and a minimal AbstractSolver subclass whose get_option() is
 * short-circuited to always report the option enabled, so the test isolates the
 * get_assertions() loop itself from the rest of the option/handshake machinery.
 * <p>
 * Asserts the correct behavior: exactly one send, and every read (including the first)
 * goes through listen() rather than re-sending the command. This currently FAILS against
 * today's code (a second send instead of a listen), documenting the bug.
 * <p>
 * The fix landed as {@code sendNoListen(cmdText, "\n")} once followed by a loop that always
 * calls {@code listen()} (rather than the equally-valid alternative this test originally
 * verified: {@code sendAndListen} on the first iteration, {@code listen()} thereafter) --
 * the assertions below accept either shape, since both satisfy "send once, then only
 * listen".
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/25">issue #25</a>.
 */
public class AbstractSolverGetAssertionsBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    /** Never started -- start() is never called, so no OS process is actually spawned;
     *  sendNoListen()/sendAndListen()/listen() are overridden to hand back canned,
     *  pre-scripted chunks (sendNoListen() returns nothing -- its whole point is not to
     *  read a response -- so it does not consume a chunk). */
    static class FakeSolverProcess extends SolverProcess {
        int sendCalls = 0;
        int listenCalls = 0;
        private final String[] chunks;
        private int idx = 0;

        FakeSolverProcess(String... chunks) {
            super(new String[] { "true" }, "\n", null);
            this.chunks = chunks;
        }

        @Override
        public void sendNoListen(String... args) throws IOException {
            sendCalls++;
        }

        @Override
        public String sendAndListen(String... args) throws IOException {
            sendCalls++;
            return chunks[idx++];
        }

        @Override
        public String listen() throws IOException {
            listenCalls++;
            return chunks[idx++];
        }
    }

    static class TestSolver extends AbstractSolver {
        TestSolver(SMT.Configuration config, SolverProcess fakeProcess) {
            this.smtConfig = config;
            this.solverProcess = fakeProcess;
        }

        /** Short-circuits the produce-assertions/interactive-mode check so the test can
         *  focus purely on get_assertions()'s own read loop. */
        @Override
        public IResponse get_option(IKeyword option) {
            return Utils.TRUE;
        }
    }

    @Test
    public void multiReadLoopListensRatherThanResending() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        // First chunk is an unbalanced "(" (parens == 1), forcing a second read iteration;
        // the second chunk closes it, so the assembled response "()" parses as an empty
        // (but syntactically valid) assertion list. Every chunk here is consumed by
        // listen() under the fix's actual shape (sendNoListen() reads nothing itself).
        FakeSolverProcess fake = new FakeSolverProcess("(", ")");
        TestSolver solver = new TestSolver(config, fake);

        IResponse response = solver.get_assertions();

        Assert.assertFalse("get_assertions() should not itself report an error",
                response instanceof IResponse.IError);
        Assert.assertEquals("exactly one command should ever be sent", 1, fake.sendCalls);
        Assert.assertEquals("every response chunk should be read via listen()", 2, fake.listenCalls);
    }
}
