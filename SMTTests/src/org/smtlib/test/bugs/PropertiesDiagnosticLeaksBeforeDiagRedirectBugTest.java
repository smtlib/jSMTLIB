package org.smtlib.test.bugs;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.PrintStream;
import java.nio.file.Files;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.SMT;

/**
 * Pins down SMT.java's parseCommandLine(): {@code readProperties()} (and the verbose
 * "#reading properties ..." diagnostics it emits via {@code smtConfig.log.logDiag}) runs
 * BEFORE the {@code --diag}/{@code --out} redirects requested on the same command line are
 * actually applied to {@code smtConfig.log} -- those are only wired up later, right before
 * the solver-name defaulting. A user who explicitly asks for diagnostics to go to a file via
 * {@code --diag <file> --verbose 1} still gets the properties-loading diagnostic on whatever
 * channel was in effect before parsing started (e.g. the real System.out/System.err in a
 * genuine CLI run), not the file they asked for.
 * <p>
 * Reproduced here by NOT pre-redirecting smtConfig.log before exec() runs (unlike
 * SMTCommandLineTests' own @Before, which points log at its captured buffer from the very
 * start, before parseCommandLine ever runs -- that setup can't distinguish "reached the
 * requested file" from "reached the pre-existing default", since both happen to be the same
 * buffer there). Here the pre-exec channel is a separate, distinctly-recognizable buffer, so
 * a message landing in it (instead of the --diag file) is unambiguous proof of the leak.
 * <p>
 * Asserts the correct behavior: with {@code --diag <file> --verbose 1}, the
 * "#reading properties" diagnostic ends up in the file, not on whatever channel was current
 * before parsing began.
 */
public class PropertiesDiagnosticLeaksBeforeDiagRedirectBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    @Test
    public void propertiesDiagnosticGoesToRequestedDiagFile() throws Exception {
        SMT smt = new SMT();
        ByteArrayOutputStream preExecBuf = new ByteArrayOutputStream();
        PrintStream preExecPs = new PrintStream(preExecBuf);
        // Distinct from the --diag file: whatever channel smtConfig.log happens to be
        // pointed at when exec() is first called, before parseCommandLine has processed
        // any arguments at all -- exactly the situation a real CLI invocation is in
        // (System.out/System.err) before --diag gets a chance to redirect anything.
        smt.smtConfig.log.setChannels(preExecPs, preExecPs);

        File diagFile = File.createTempFile("smtdiag", ".txt");
        diagFile.deleteOnExit();
        try {
            smt.exec(new String[] { "--diag", diagFile.getAbsolutePath(), "--verbose", "1",
                    "--solver", "test", "--text", "(exit)" });
            preExecPs.flush();

            String diagFileContent = new String(Files.readAllBytes(diagFile.toPath()));
            Assert.assertFalse("The properties-loading diagnostic must not leak to the "
                    + "pre-exec channel once --diag has been given: " + preExecBuf.toString(),
                    preExecBuf.toString().contains("reading properties"));
            Assert.assertTrue("The properties-loading diagnostic should end up in the "
                    + "requested --diag file instead", diagFileContent.contains("reading properties"));
        } finally {
            smt.cleanup();
        }
    }
}
