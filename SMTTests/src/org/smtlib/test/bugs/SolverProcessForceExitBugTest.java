package org.smtlib.test.bugs;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;

import org.junit.After;
import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.SolverProcess;

/** Regression test for #156: exit() (reached through forceExit()) from another thread nulled
 *  the stream fields that the thread blocked in listen() reads once it wakes on EOF, so that
 *  thread could fail with a NullPointerException. It should instead see an IOException (a
 *  NoResponseException, or the read failing on the stream exit() closed) or the partial text.
 *  Uses EchoProcess with an end marker it never writes, so listen() blocks until the process
 *  is killed. */
public class SolverProcessForceExitBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    private SolverProcess sp;

    @After
    public void tearDown() {
        if (sp != null) sp.exit();
    }

    private void start() throws Exception {
        String javaBin = System.getProperty("java.home") + File.separator + "bin" + File.separator + "java";
        sp = new SolverProcess(new String[]{javaBin, "-cp", System.getProperty("java.class.path"),
                "org.smtlib.test.EchoProcess"}, "<never>", null, StandardCharsets.UTF_8);
        sp.start(false);
    }

    /** The state the woken thread sees when exit() has finished first: deterministic */
    @Test
    public void listenAfterExit() throws Exception {
        start();
        sp.exit();
        try {
            sp.listen();
            Assert.fail("expected an IOException");
        } catch (IOException e) {
            // expected
        }
    }

    /** The reported scenario: one thread blocked in listen(), another calls exit() */
    @Test
    public void exitFromAnotherThread() throws Exception {
        start();
        AtomicReference<Throwable> thrown = new AtomicReference<>();
        Thread listener = new Thread(() -> {
            try {
                sp.sendAndListen("x\n");
            } catch (IOException e) {
                // acceptable outcome
            } catch (Throwable t) {
                thrown.set(t);
            }
        });
        listener.start();
        while (listener.getState() != Thread.State.WAITING && listener.isAlive()) Thread.sleep(10);
        sp.exit();
        listener.join(10000);
        Assert.assertFalse("listener still blocked", listener.isAlive());
        Assert.assertNull(String.valueOf(thrown.get()), thrown.get());
    }
}
