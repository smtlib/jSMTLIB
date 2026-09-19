package org.smtlib.test.bugs;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.IParser.ParserException;
import org.smtlib.ISource;
import org.smtlib.SMT;
import org.smtlib.sexpr.Parser;

/**
 * Pins down two small issues in sexpr/Parser.java:
 * <ol>
 * <li>A stray-token recovery path at command-parse level (around lines 155-162) silently
 * skips an unbounded number of tokens with zero logging, by its own comment ("skip silently
 * to the next LP without logging, matching old null-return behavior"). Fixed to log a
 * diagnostic (count of skipped tokens) when {@code smtConfig.verbose != 0}, matching this
 * file's existing diagnostic-logging convention elsewhere (e.g. "#Completed input").
 * <li>Two user-facing error messages (lines 349, 379) misspell "identifier" as "identifer":
 * {@code parseQualifiedIdentifier()}'s "Invalid beginning of an identifer: expected either
 * 'as' or '_' here", and {@code parseIdentifier()}'s "Invalid beginning of an identifer:
 * expected a '_' here".
 * </ol>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/83">issue #83</a>.
 */
public class ParserStrayTokenAndTypoBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    @Test
    public void strayTokenRecoveryLogsADiagnostic() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        config.verbose = 1;
        ByteArrayOutputStream diagBuf = new ByteArrayOutputStream();
        config.log.setChannels(config.log.getOut(), new PrintStream(diagBuf));

        // "foo" is a stray token at command level (not a '('), so parseLP() fails and the
        // recovery path skips forward to the next '(' -- here, the start of "(exit)".
        ISource source = config.smtFactory.createSource("foo (exit)", null);
        Parser p = new Parser(config, source);

        Object result = p.parseCommand();

        Assert.assertNull("the stray token should still result in a null command (unchanged behavior)", result);
        Assert.assertTrue("expected a diagnostic mentioning the skipped stray token(s): [" + diagBuf + "]",
                diagBuf.toString().toLowerCase().contains("skip"));
    }

    @Test
    public void parseIdentifierErrorMessageSpelledCorrectly() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        // "(bar X)" -- a parenthesized identifier form whose head is neither "_" (the only
        // valid parameterized-identifier head parseIdentifier() accepts here).
        ISource source = config.smtFactory.createSource("(bar X)", null);
        Parser p = new Parser(config, source);

        try {
            p.parseIdentifier();
            Assert.fail("expected a ParserException");
        } catch (ParserException e) {
            Assert.assertTrue("message should say \"identifier\", not \"identifer\": " + e.getMessage(),
                    e.getMessage().contains("identifier"));
        }
    }

    @Test
    public void parseQualifiedIdentifierErrorMessageSpelledCorrectly() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        // "(bar X)" -- neither "as" nor "_" as the head, so parseQualifiedIdentifier()'s own
        // else-branch error fires.
        ISource source = config.smtFactory.createSource("(bar X)", null);
        Parser p = new Parser(config, source);

        try {
            p.parseQualifiedIdentifier();
            Assert.fail("expected a ParserException");
        } catch (ParserException e) {
            Assert.assertTrue("message should say \"identifier\", not \"identifer\": " + e.getMessage(),
                    e.getMessage().contains("identifier"));
        }
    }
}
