package org.smtlib.test.bugs;

import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.impl.Response;

/**
 * Pins down impl/SMTExpr.java:278's {@code Symbol.isOK()}:
 *
 * <pre>public boolean isOK() { return value.equals(Response.OK) || value.equals(Response.EMPTY); }</pre>
 *
 * {@code value} is a {@code String}. {@code Response.OK} is the string {@code "success"} --
 * that half is fine. But {@code Response.EMPTY} (impl/Response.java:28) is not a String, it's
 * an {@code SMTExpr.Symbol} *instance*: {@code new SMTExpr.Symbol("")}. So
 * {@code value.equals(Response.EMPTY)} compares a String against a Symbol object --
 * {@code String.equals(Object)} always returns false for a non-String argument, regardless of
 * {@code value}'s actual content, so that half of the {@code ||} can never be true.
 * <p>
 * Under {@code :print-success false}, {@code AbstractSolver} returns {@code Response.EMPTY}
 * itself as the correct "success, suppressed" response for many commands. Any caller gating
 * on {@code .isOK()} (e.g. {@code Solver_simplify.java:106}) incorrectly treats that
 * legitimate response as a failure and short-circuits.
 * <p>
 * Asserts the correct behavior ({@code Response.EMPTY.isOK()} is true). This currently FAILS
 * against today's code, documenting the bug.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/57">issue #57</a>.
 */
public class SymbolIsOKBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    @Test
    public void emptyResponseIsConsideredOK() throws Exception {
        Assert.assertTrue("Response.EMPTY represents a suppressed but successful response",
                Response.EMPTY.isOK());
    }
}
