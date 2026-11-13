package org.smtlib.test;

import java.io.IOException;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.SolverProcess;

/**
 * A SolverProcess that fails to start reports a ProverException that keeps the failure as its
 * cause (#205 item 7). A JUnit test: the cause is visible only through the API.
 */
public class SolverProcessStartFailureTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    private static Throwable startFailure(String[] cmd) {
        try {
            new SolverProcess(cmd, "\n", null).start(false);
        } catch (SolverProcess.ProverException e) {
            return e.getCause();
        }
        Assert.fail("start() did not throw");
        return null;
    }

    @Test
    public void missingExecutableKeepsIOException() {
        Throwable cause = startFailure(new String[]{"no-such-solver-executable-205"});
        Assert.assertTrue(String.valueOf(cause), cause instanceof IOException);
    }

    @Test
    public void emptyCommandKeepsRuntimeException() {
        Throwable cause = startFailure(new String[0]);
        Assert.assertTrue(String.valueOf(cause), cause instanceof RuntimeException);
    }
}
