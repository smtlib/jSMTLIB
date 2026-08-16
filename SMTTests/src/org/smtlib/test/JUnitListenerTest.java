package org.smtlib.test;

import org.junit.Assert;
import org.junit.Test;
import org.smtlib.IResponse;
import org.smtlib.SMT;
import org.smtlib.Utils;
import org.smtlib.impl.Response;

/** Tests for JUnitListener's error-capturing behavior, in particular the fix that makes
 *  {@code logError(String)} -- previously a silent no-op -- also populate {@code msgs},
 *  matching {@code logError(IResponse.IError)}. */
public class JUnitListenerTest {

    @Test
    public void logErrorString_isCaptured() {
        JUnitListener listener = new JUnitListener();
        listener.logError("a plain string error");
        Assert.assertEquals(1, listener.msgs.size());
        Assert.assertTrue(listener.msgs.get(0) instanceof IResponse.IError);
        Assert.assertEquals("a plain string error", ((IResponse.IError) listener.msgs.get(0)).errorMsg());
    }

    @Test
    public void logErrorIResponse_stillCaptured() {
        JUnitListener listener = new JUnitListener();
        IResponse.IError err = new Response.Error("an IError");
        listener.logError(err);
        Assert.assertEquals(1, listener.msgs.size());
        Assert.assertSame(err, listener.msgs.get(0));
    }

    @Test
    public void bothOverloads_accumulateInOrder() {
        JUnitListener listener = new JUnitListener();
        listener.logError("first");
        listener.logError(new Response.Error("second"));
        Assert.assertEquals(2, listener.msgs.size());
        Assert.assertEquals("first", ((IResponse.IError) listener.msgs.get(0)).errorMsg());
        Assert.assertEquals("second", ((IResponse.IError) listener.msgs.get(1)).errorMsg());
    }

    @Test
    public void logOutAndLogDiag_remainNoOps() {
        JUnitListener listener = new JUnitListener();
        listener.logOut("out message");
        listener.logOut(Response.SUCCESS);
        listener.logDiag("diag message");
        listener.indent("prompt");
        Assert.assertTrue(listener.msgs.isEmpty());
    }

    /** End-to-end regression test for the actual gap that motivated this fix: Utils.unescape
     *  reports malformed string literals via the plain-String logError overload, not
     *  IResponse.IError -- so before the fix, this error was invisible both to a JUnitListener
     *  and to the console (clearListeners() removes the printing listener). Confirms it is now
     *  captured through the same wiring the other JUnitListener-based test classes use. */
    @Test
    public void malformedStringLiteral_isCapturedThroughRealCodePath() {
        SMT.Configuration config = new SMT.Configuration();
        JUnitListener listener = new JUnitListener();
        config.log.clearListeners();
        config.log.addListener(listener);
        Utils u = new Utils(config);

        u.unescape("\"abc"); // missing closing quote -- reports via logError(String)

        Assert.assertFalse("expected the malformed-literal error to be captured", listener.msgs.isEmpty());
        Assert.assertTrue(listener.msgs.get(0) instanceof IResponse.IError);
    }
}
