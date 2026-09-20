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
 * Pins down AbstractSolver.java's {@code get_assertions()}: its multi-read loop counts
 * every {@code (}/{@code )} character in the raw response text to decide whether the
 * s-expression is complete, without excluding characters inside string literals --
 * unlike {@link SolverProcess#endsWith(StringBuilder, String)}'s own end-marker
 * recognizer, which explicitly tracks in-string state for exactly this reason (a
 * parenthesis inside a solver's own string-valued response, e.g. a string-sort term
 * value, must not count toward the balance).
 * <p>
 * A response chunk containing a string literal with an unequal number of {@code (}/{@code
 * )} characters inside it (e.g. {@code "a)b)c)d"}, three stray {@code )} and no {@code (})
 * throws the naive count off: two real, unclosed opening parens plus three
 * inside-a-string closing parens nets to -1, which the old code reads as "already
 * balanced" and stops reading after just one chunk -- even though the string literal (and
 * the response) isn't actually finished yet.
 * <p>
 * Uses the same fake-process harness as {@link AbstractSolverGetAssertionsBugTest}, but a
 * response deliberately split so the string literal's closing quote arrives in a second
 * chunk, forcing a real string-aware implementation to keep reading past the first one.
 * <p>
 * Asserts the correct behavior: both chunks get consumed (the loop keeps reading until the
 * string literal -- and so the real parens -- actually close), and the assembled response
 * parses cleanly as a one-element assertion list.
 */
public class AbstractSolverGetAssertionsStringLiteralBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

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

        @Override
        public IResponse get_option(IKeyword option) {
            return Utils.TRUE;
        }
    }

    @Test
    public void parensInsideStringLiteralDoNotDesyncTheBalanceCount() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        // Assembled across both chunks: ((= s "a)b)c)d"))  -- a one-element assertion
        // list containing (= s "a)b)c)d"), a perfectly legal SMT-LIB term (a string
        // literal's contents are literal until its closing quote). The opening quote and
        // the three ')' inside it arrive in chunk 1, before it's closed; the closing
        // quote and the two real closing parens arrive in chunk 2.
        FakeSolverProcess fake = new FakeSolverProcess("((= s \"a)b)c)d", "\"))");
        TestSolver solver = new TestSolver(config, fake);

        IResponse response = solver.get_assertions();

        Assert.assertFalse("get_assertions() should not report an error: " + response,
                response instanceof IResponse.IError);
        Assert.assertEquals("both chunks must be read -- the string literal (and so the "
                + "real parens) aren't done after chunk 1", 2, fake.listenCalls);
    }
}
