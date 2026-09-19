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
 * Pins down issue #33: {@code Log.logOut(String)} and {@code Log.logOutNoln(String)}
 * (Log.java) were byte-for-byte identical -- both forwarded to {@code listener.logOut(message)},
 * and {@code StandardListener.logOut(String)} only ever did {@code out.print(msg)}, so neither
 * method ever added a line termination despite {@code logOut(String)}'s name (and its sibling
 * overloads {@code logOut(IResponse)}/{@code logError(String)}/{@code logDiag(String)}, all of
 * which DO add one) implying it would.
 * <p>
 * This wasn't just a naming inconsistency: {@code ext/C_what.java}'s {@code :what} command logs
 * one line per symbol-table entry via repeated {@code logOut(String)} calls with no embedded
 * newline, expecting each to land on its own line -- so every {@code :what} query with more
 * than one result actually ran all its entries together on a single unbroken line.
 * <p>
 * Fixed by having {@code logOut(String)} add a line termination (matching its sibling
 * overloads' existing convention), while {@code logOutNoln(String)} keeps the original
 * no-newline behavior via a new, distinct {@code IListener.logOutNoln(String)} method (rather
 * than the two continuing to share one {@code IListener.logOut(String)} method under the hood).
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/33">issue #33</a>.
 */
public class LogOutNewlineBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    @Test
    public void logOutAddsALineTermination() {
        SMT.Configuration config = new SMT.Configuration();
        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        config.log.setChannels(new PrintStream(baos), config.log.getDiag());

        config.log.logOut("hello");

        Assert.assertEquals("hello" + System.lineSeparator(), baos.toString());
    }

    @Test
    public void logOutNolnAddsNoLineTermination() {
        SMT.Configuration config = new SMT.Configuration();
        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        config.log.setChannels(new PrintStream(baos), config.log.getDiag());

        config.log.logOutNoln("hello");

        Assert.assertEquals("hello", baos.toString());
    }
}
