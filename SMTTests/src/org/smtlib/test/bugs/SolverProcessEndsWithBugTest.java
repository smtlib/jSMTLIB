package org.smtlib.test.bugs;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.SolverProcess;

/**
 * Pins down SolverProcess.java:195-200's endsWith(StringBuilder, String): sb.charAt(sblen-i)
 * goes negative when the accumulated buffer is shorter than a multi-character end marker
 * (e.g. Solver_simplify's ">\t" arriving across two small reads), throwing
 * StringIndexOutOfBoundsException. Since the only catch around the gobbler thread's read
 * loop is for IOException, this exception kills the daemon gobbler thread silently, and the
 * next listen() call then blocks on queue.take() forever -- a hang with no diagnostic.
 * <p>
 * endsWith() is a package-private instance method (called from a lambda passed to
 * StreamGobbler's constructor), so it is invoked here via reflection rather than directly;
 * the SolverProcess is never started() (no process is actually spawned), since endsWith()
 * only touches its own StringBuilder/String arguments.
 * <p>
 * This test asserts the correct behavior once endsWith() is fixed to treat a buffer shorter
 * than the end marker as simply "not yet ended" rather than indexing off the front of it. It
 * currently FAILS against today's code (StringIndexOutOfBoundsException instead),
 * documenting the bug.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/24">issue #24</a>.
 * <p>
 * Stays a JUnit test: reproducing this requires a private method invoked via reflection with
 * a hand-crafted, shorter-than-the-marker buffer -- the real trigger (a multi-character end
 * marker arriving split across two small OS-level reads) is a timing-dependent chunk split not
 * controllable from any script test.
 */
public class SolverProcessEndsWithBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    @Test
    public void shortBufferWithMultiCharMarkerIsNotYetEnded() throws Exception {
        SolverProcess sp = new SolverProcess(new String[] { "true" }, ">\t", null);
        Method endsWith = SolverProcess.class.getDeclaredMethod("endsWith", StringBuilder.class, String.class);
        endsWith.setAccessible(true);

        // The buffer (one char) is shorter than the two-character end marker ">\t".
        StringBuilder sb = new StringBuilder(">");
        try {
            boolean result = (Boolean) endsWith.invoke(sp, sb, ">\t");
            Assert.assertFalse("A buffer shorter than the end marker cannot have ended yet", result);
        } catch (InvocationTargetException e) {
            throw (Exception) e.getCause();
        }
    }
}
