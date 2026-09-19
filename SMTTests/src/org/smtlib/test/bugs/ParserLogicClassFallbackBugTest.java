package org.smtlib.test.bugs;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.ILogic;
import org.smtlib.IParser;
import org.smtlib.IResponse;
import org.smtlib.ISource;
import org.smtlib.Log;
import org.smtlib.SMT;

/**
 * Pins down sexpr/Parser.parseLogic()'s logic-class loader (Parser.java:845-870): it silently
 * fell back to a bare, unrestricted {@code SMTExpr.Logic} whenever there was no Java class
 * matching {@code org.smtlib.logic.<name>} -- e.g. {@code (set-logic QF_UFNIA)}, since
 * {@code QF_UFNIA.java} doesn't exist even though {@code UFNIA.java} does -- disabling ALL
 * syntactic checking (noQuantifiers, sort/function-declaration restrictions, everything) for
 * that logic name with no visible indication anything was wrong.
 * <p>
 * Fixed by logging a diagnostic (verbose-gated, matching the convention already used elsewhere
 * in this class, e.g. {@code "#Completed input"}) when the fallback happens, so a missing or
 * mistyped restriction class is visible instead of silent.
 * <p>
 * Reproduced directly against {@code IParser.parseLogic()} with a made-up logic name that can
 * never have a dedicated {@code org.smtlib.logic} class, exercising exactly the
 * {@code ClassNotFoundException} fallback path.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/46">issue #46</a>.
 */
public class ParserLogicClassFallbackBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    static class RecordingListener implements Log.IListener {
        final List<String> diagStrings = new ArrayList<>();
        @Override public void logOut(String msg) {}
        @Override public void logOutNoln(String msg) {}
        @Override public void logOut(IResponse r) {}
        @Override public void logError(String msg) {}
        @Override public void logError(IResponse.IError r) {}
        @Override public void logDiag(String msg) { diagStrings.add(msg); }
        @Override public void indent(String chars) {}
    }

    @Test
    public void fallbackToUnrestrictedLogicIsLogged() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        config.verbose = 1;
        RecordingListener listener = new RecordingListener();
        config.log.clearListeners();
        config.log.addListener(listener);

        ISource source = config.smtFactory.createSource("(logic QF_MADE_UP_LOGIC)", null);
        IParser p = new org.smtlib.sexpr.Parser(config, source);
        ILogic logic = p.parseLogic();

        // The fallback still succeeds (an unrestricted logic is a legitimate outcome for
        // genuinely unimplemented restriction classes) -- but it must no longer be silent.
        Assert.assertNotNull(logic);
        Assert.assertFalse("expected the fallback to a class-less, unrestricted logic to be "
                + "logged as a diagnostic", listener.diagStrings.isEmpty());
    }
}
