package org.smtlib.test.bugs;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.SMT;

/**
 * Pins down issue #32: {@code Log.out}/{@code Log.diag} used to be public fields
 * reassigned directly from half a dozen places ({@code AbstractSolver.set_option()},
 * its own duplicate in {@code Solver_test}, {@code CharSequenceSocket}, {@code SMT}'s
 * startup {@code --out}/{@code --diag} handling, {@code Solver_bitwuzla}'s
 * save/restore, and test code that deliberately aliases the two). Switching
 * {@code :regular-output-channel}/{@code :diagnostic-output-channel} to a file more
 * than once in the same session leaked the previously-opened {@code FileOutputStream}:
 * nothing closed it before the field was overwritten, since no single call site could
 * safely tell whether the stream it was about to replace was still needed elsewhere
 * (in particular, by the other channel, which test code and {@code Solver_bitwuzla}
 * both deliberately point at the same stream on purpose).
 * <p>
 * Fixed by making both fields private, routing every change through
 * {@code Log.setChannels(PrintStream, PrintStream)} (which never opens or closes
 * anything -- callers retain ownership of whatever they hand in) and the two new
 * {@code Log.setRegularOutputChannel(String)}/{@code setDiagnosticOutputChannel(String)}
 * convenience methods (the only places that ever call {@code new FileOutputStream},
 * and therefore the only places that can safely close a stream on the next switch,
 * since ownership is no longer ambiguous once there is exactly one opener).
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/32">issue #32</a>.
 * <p>
 * Stays a JUnit test: whether a previously-opened file stream got closed is a resource-
 * lifecycle property (probed here via {@code PrintStream.checkError()} after a redirect), not
 * anything printed to stdout/stderr that a script test could compare against a golden file.
 */
public class LogChannelOwnershipBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    private File tempFile() throws IOException {
        File f = File.createTempFile("jsmtlib-log32-", ".txt");
        f.deleteOnExit();
        return f;
    }

    /** After println'ing past a close, a PrintStream's error flag is set -- the
     *  standard way to observe "this stream is closed" without depending on any
     *  particular exception type from the underlying FileOutputStream. */
    private boolean isClosed(PrintStream p) {
        p.println("probe");
        return p.checkError();
    }

    @Test
    public void switchingRegularOutputChannelToAnotherFileClosesThePrevious() throws IOException {
        SMT.Configuration config = new SMT.Configuration();
        config.log.setRegularOutputChannel(tempFile().getAbsolutePath());
        PrintStream first = config.log.getOut();

        config.log.setRegularOutputChannel(tempFile().getAbsolutePath());

        Assert.assertTrue("previous file stream should be closed after switching to a new file",
            isClosed(first));
    }

    @Test
    public void switchingDiagnosticOutputChannelToAnotherFileClosesThePrevious() throws IOException {
        SMT.Configuration config = new SMT.Configuration();
        config.log.setDiagnosticOutputChannel(tempFile().getAbsolutePath());
        PrintStream first = config.log.getDiag();

        config.log.setDiagnosticOutputChannel(tempFile().getAbsolutePath());

        Assert.assertTrue("previous file stream should be closed after switching to a new file",
            isClosed(first));
    }

    @Test
    public void aFileStreamStillUsedByTheOtherChannelIsNotClosed() throws IOException {
        SMT.Configuration config = new SMT.Configuration();
        String path = tempFile().getAbsolutePath();
        config.log.setRegularOutputChannel(path);
        config.log.setDiagnosticOutputChannel(path); // deliberately the same file as :regular-output-channel

        // Switch only the regular-output channel elsewhere; the diagnostic channel
        // still needs the shared file stream, so it must survive.
        config.log.setRegularOutputChannel(tempFile().getAbsolutePath());

        Assert.assertFalse("stream still referenced by the other channel must not be closed",
            isClosed(config.log.getDiag()));
    }

    @Test
    public void switchingToStdoutOrStderrNeverClosesThem() throws IOException {
        SMT.Configuration config = new SMT.Configuration();
        config.log.setRegularOutputChannel(tempFile().getAbsolutePath());

        config.log.setRegularOutputChannel("stdout");
        config.log.setDiagnosticOutputChannel("stderr");

        // Not much to assert directly against System.out/System.err without corrupting
        // other tests' output, but this must not throw, and a second switch away and
        // back must still work -- which it wouldn't if stdout/stderr had been closed.
        config.log.setRegularOutputChannel("stderr");
        config.log.setDiagnosticOutputChannel("stdout");
    }

    @Test
    public void setChannelsNeverClosesACallerSuppliedStream() {
        SMT.Configuration config = new SMT.Configuration();
        java.io.ByteArrayOutputStream buf = new java.io.ByteArrayOutputStream();
        PrintStream caller = new PrintStream(buf);

        config.log.setChannels(caller, config.log.getDiag());
        // Replace it again with something else entirely -- setChannels must never close
        // a stream it didn't open itself, regardless of how many times it's replaced.
        config.log.setChannels(config.log.getOut(), config.log.getDiag());
        config.log.setChannels(new PrintStream(new java.io.ByteArrayOutputStream()), config.log.getDiag());

        Assert.assertFalse("setChannels must never close a caller-supplied stream",
            isClosed(caller));
    }
}
