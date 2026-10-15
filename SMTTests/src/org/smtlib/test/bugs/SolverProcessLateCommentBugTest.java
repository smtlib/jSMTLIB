package org.smtlib.test.bugs;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.util.concurrent.TimeUnit;

import org.junit.After;
import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.SolverProcess;

/** Regression test for #99: z3 writes diagnostic comment lines after some responses, and when
 *  they arrived late they were taken as the response to a later command -- a comment line
 *  split across two reads of standard error lost its ';' (seen as a response of "0"), and a
 *  block of comment lines read on its own from standard output became the next response.
 *  Uses LateCommentProcess, which writes such comments late on purpose. */
public class SolverProcessLateCommentBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    private SolverProcess sp;

    @After
    public void tearDown() {
        if (sp != null) sp.exit();
    }

    private void start(String mode) throws Exception {
        String javaBin = System.getProperty("java.home") + File.separator + "bin" + File.separator + "java";
        sp = new SolverProcess(new String[]{javaBin, "-cp", System.getProperty("java.class.path"),
                "org.smtlib.test.LateCommentProcess", mode}, "\n", null, StandardCharsets.UTF_8);
        sp.start(false);
    }

    /** Sends a command after the late text from earlier commands has arrived */
    private String sendLater(String command) throws Exception {
        Thread.sleep(org.smtlib.test.LateCommentProcess.DELAY_MILLIS + 200);
        return sp.sendAndListen(command + "\n");
    }

    @Test
    public void commentSplitOnStandardError() throws Exception {
        start("--stderr-split");
        Assert.assertEquals("unsupported", sp.sendAndListen("ask\n"));
        Assert.assertEquals("success", sendLater("next"));
        Assert.assertEquals("success", sendLater("next"));
    }

    @Test
    public void commentsLateOnStandardOutput() throws Exception {
        start("--stdout-late");
        Assert.assertEquals("unsupported", sp.sendAndListen("ask\n"));
        Assert.assertEquals("success", sendLater("next"));
        Assert.assertEquals("success", sendLater("next"));
    }
}
