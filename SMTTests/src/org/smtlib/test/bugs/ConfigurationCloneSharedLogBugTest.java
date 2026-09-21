package org.smtlib.test.bugs;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.SMT;

/**
 * Pins down SMT.Configuration.clone(): {@code super.clone()} shallow-copies every field,
 * including {@code log}, and the explicit per-field fixups afterward (giving the clone its
 * own commands/reservedWords/reservedWordsNotCommands/utils) never gave it its own {@code
 * Log} -- the adjacent {@code // FIXME - ok to have a reference copy of Log ?} documents
 * this as a known open question, not an intentional design choice. A clone and its original
 * shared the exact same Log instance, so redirecting one's output channel (e.g. via
 * {@code :regular-output-channel}, or directly through {@code Log.setChannels}) silently
 * redirected the other's too -- contradicting SMT's own class-level design goal that
 * "Separate instances of SMT objects can be run independently and in parallel."
 * <p>
 * Same underlying kind of bug as the already-fixed issue #23 (Configuration.clone()'s Utils
 * field), just for Log instead.
 * <p>
 * Stays a JUnit test: the bug only manifests when two {@code Configuration} instances exist
 * side by side in one process and one's channel redirection is checked against the other's --
 * every CLI invocation is its own separate process with exactly one {@code Configuration}, so
 * there is no script-observable way to construct this scenario.
 */
public class ConfigurationCloneSharedLogBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    @Test
    public void cloneAndOriginalEachKeepTheirOwnLog() throws Exception {
        SMT.Configuration original = new SMT.Configuration();
        SMT.Configuration clone = original.clone();

        // Fixed: the clone gets its own independent Log instance.
        Assert.assertNotSame(original.log, clone.log);

        PrintStream originalOut = original.log.getOut();
        PrintStream originalDiag = original.log.getDiag();

        // Redirect the CLONE's channels only.
        ByteArrayOutputStream buf = new ByteArrayOutputStream();
        PrintStream redirected = new PrintStream(buf);
        clone.log.setChannels(redirected, redirected);

        // The original's own channels must be untouched by the clone's redirection --
        // exactly what a shared Log instance would get wrong.
        Assert.assertSame(originalOut, original.log.getOut());
        Assert.assertSame(originalDiag, original.log.getDiag());

        // And the clone's redirection did actually take effect on the clone itself.
        Assert.assertSame(redirected, clone.log.getOut());
    }
}
