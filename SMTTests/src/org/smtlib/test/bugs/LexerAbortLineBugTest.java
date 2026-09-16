package org.smtlib.test.bugs;

import java.util.concurrent.TimeUnit;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.ISource;
import org.smtlib.SMT;
import org.smtlib.sexpr.Lexer;

/**
 * Pins down sexpr/Lexer.java:41-46's {@code abortLine()}:
 *
 * <pre>public void abortLine() {
 *     int i = matcher.regionStart();
 *     char c;
 *     while ((c=csr.charAt(i))!= '\r' && c != '\n') ++i; // FIXME  - what about end of input?
 *     matcher.region(i,csr.length());
 * }</pre>
 *
 * Scans forward for {@code \r}/{@code \n} with no end-of-input check -- flagged by the
 * author's own FIXME on the same line. A final line with no trailing newline walks {@code i}
 * past the end of the buffer, and {@code csr.charAt(i)} throws.
 * <p>
 * {@code abortLine()} is called from {@code SMT.java}'s interactive-mode error recovery
 * (after a parse error, to skip to the next line and keep going) -- reachable any time the
 * last line of interactive input has a parse error and no trailing newline.
 * <p>
 * Asserts the correct behavior: {@code abortLine()} should treat end-of-input as an implicit
 * line boundary rather than throwing. This currently FAILS against today's code
 * (StringIndexOutOfBoundsException/IndexOutOfBoundsException instead), documenting the bug.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/72">issue #72</a>.
 */
public class LexerAbortLineBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    @Test
    public void abortLineAtEndOfInputWithNoTrailingNewlineDoesNotThrow() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        // No trailing '\r'/'\n' anywhere in this input.
        ISource source = config.smtFactory.createSource("(foo", null);
        Lexer lexer = new Lexer(config, source);

        lexer.abortLine();
    }
}
