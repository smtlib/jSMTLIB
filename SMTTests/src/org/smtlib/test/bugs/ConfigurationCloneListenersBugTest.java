package org.smtlib.test.bugs;

import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.IResponse;
import org.smtlib.Log;
import org.smtlib.SMT;

/**
 * Issue #221: messages logged through a clone of a Configuration (as Utils.findLogic/findTheory make for
 * each logic and theory) must reach the original's listeners, while the clone keeps its own Log and
 * channels (ConfigurationCloneSharedLogBugTest).
 * <p>
 * Stays a JUnit test: listeners exist only in the API; on the command line both paths print to the same
 * streams, so no script can observe the difference.
 */
public class ConfigurationCloneListenersBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    /** Records diagnostic and error messages */
    static class Recorder implements Log.IListener {
        final List<String> messages = new ArrayList<>();
        @Override public void logOut(String msg) {}
        @Override public void logOutNoln(String msg) {}
        @Override public void logOut(IResponse result) {}
        @Override public void logError(String msg) { messages.add(msg); }
        @Override public void logError(IResponse.IError result) { messages.add(result.errorMsg()); }
        @Override public void logDiag(String msg) { messages.add(msg); }
        @Override public void indent(String chars) {}
    }

    @Test
    public void cloneReachesTheOriginalsListeners() throws Exception {
        SMT.Configuration original = new SMT.Configuration();
        Recorder recorder = new Recorder();
        original.log.addListener(recorder);
        SMT.Configuration clone = original.clone();
        clone.log.logDiag("from the clone");
        Assert.assertEquals(List.of("from the clone"), recorder.messages);
    }

    @Test
    public void cloneWritesToItsOwnChannels() throws Exception {
        SMT.Configuration original = new SMT.Configuration();
        ByteArrayOutputStream originalBuf = new ByteArrayOutputStream();
        PrintStream originalStream = new PrintStream(originalBuf, true);
        original.log.setChannels(originalStream, originalStream);
        SMT.Configuration clone = original.clone();
        ByteArrayOutputStream cloneBuf = new ByteArrayOutputStream();
        PrintStream cloneStream = new PrintStream(cloneBuf, true);
        clone.log.setChannels(cloneStream, cloneStream);
        clone.log.logDiag("from the clone");
        Assert.assertEquals("", originalBuf.toString());
        Assert.assertEquals("from the clone" + System.lineSeparator(), cloneBuf.toString());
    }

    @Test
    public void cloneOfALogWithoutTheStandardListenerPrintsNothing() throws Exception {
        SMT.Configuration original = new SMT.Configuration();
        PrintStream sink = new PrintStream(OutputStream.nullOutputStream());
        original.log.setChannels(sink, sink);
        original.log.clearListeners();
        Recorder recorder = new Recorder();
        original.log.addListener(recorder);
        SMT.Configuration clone = original.clone();
        ByteArrayOutputStream cloneBuf = new ByteArrayOutputStream();
        PrintStream cloneStream = new PrintStream(cloneBuf, true);
        clone.log.setChannels(cloneStream, cloneStream);
        clone.log.logDiag("from the clone");
        Assert.assertEquals("", cloneBuf.toString());
        Assert.assertEquals(List.of("from the clone"), recorder.messages);
    }

    /** End to end: QF_RDL's --relax warning is logged through the logic's cloned configuration */
    @Test
    public void logicWarningReachesTheListeners() throws Exception {
        SMT smt = new SMT();
        PrintStream sink = new PrintStream(OutputStream.nullOutputStream());
        smt.smtConfig.stdout = sink;
        smt.smtConfig.stderr = sink;
        smt.smtConfig.log.setChannels(sink, sink);
        smt.smtConfig.log.clearListeners();
        Recorder recorder = new Recorder();
        smt.smtConfig.log.addListener(recorder);
        smt.exec(new String[] { "--solver", "test", "--relax", "--text",
                "(set-logic QF_RDL)(declare-fun x () Real)(assert (< (- x x) 1.5))" });
        Assert.assertEquals(List.of("WARNING: A QF_RDL constant should be a numeral or a negated numeral,"
                + " not a decimal: (< (- x x) 1.5)"), recorder.messages);
    }
}
