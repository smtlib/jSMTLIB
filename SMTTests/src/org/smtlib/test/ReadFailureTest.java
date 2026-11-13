package org.smtlib.test;

import java.io.IOException;
import java.io.Reader;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.CharSequenceReader;
import org.smtlib.ICommand;
import org.smtlib.IParser;
import org.smtlib.SMT;

/**
 * A failure while reading input reaches the caller as an IOException, distinct from a
 * ParserException for bad input, both from IParser.parseCommand() and from the ILexer methods.
 * A JUnit test: a failing read needs a custom input stream.
 */
public class ReadFailureTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    /** Supplies its text, then fails every later read */
    private static class FailingReader extends Reader {
        private final String text;
        private boolean sent = false;
        FailingReader(String text) { this.text = text; }
        @Override public int read(char[] buf, int off, int len) throws IOException {
            if (sent) throw new IOException("read failed");
            int n = Math.min(len, text.length());
            text.getChars(0, n, buf, off);
            sent = true;
            return n;
        }
        @Override public boolean ready() { return false; }
        @Override public void close() {}
    }

    private static IParser parser(String text) {
        SMT.Configuration config = new SMT.Configuration();
        config.log.clearListeners();
        config.log.addListener(new JUnitListener());
        return config.smtFactory.createParser(config,
                config.smtFactory.createSource(new CharSequenceReader(new FailingReader(text)), null));
    }

    @Test
    public void parseCommandThrowsIOException() throws Exception {
        IParser p = parser("(set-logic QF_UF)\n(assert ");
        ICommand first = p.parseCommand();
        Assert.assertNotNull(first);
        try {
            p.parseCommand();
            Assert.fail("expected an IOException");
        } catch (IOException e) {
            Assert.assertEquals("read failed", e.getMessage());
        }
    }

    @Test
    public void getTokenThrowsIOException() throws Exception {
        IParser p = parser("(assert ");
        try {
            for (int i = 0; i < 10; i++) p.getToken();
            Assert.fail("expected an IOException");
        } catch (IOException e) {
            Assert.assertEquals("read failed", e.getMessage());
        }
    }
}
