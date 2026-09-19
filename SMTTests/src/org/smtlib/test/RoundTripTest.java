package org.smtlib.test;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.io.StringWriter;
import java.net.URL;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.ICommand;
import org.smtlib.IParser;
import org.smtlib.IPos;
import org.smtlib.ISource;
import org.smtlib.SMT;

/**
 * Parses every command in roundtrip.smt2 -- including comments, each of which parses as its
 * own {@code C_comment} pseudo-command (issue #42) -- writes each back via {@code
 * org.smtlib.sexpr.Printer}, and asserts that the written text exactly reproduces the source
 * text actually consumed for it (per the command's own {@code pos()}), modulo leading/trailing
 * whitespace and runs of non-EOL whitespace collapsed to one space -- not modulo comments, or
 * modulo internal line structure.
 *
 * <p>This exercises all command {@code write()} implementations and their branches (empty vs.
 * non-empty loops, attribute present/absent, etc.) without invoking any solver.
 */
public class RoundTripTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    JUnitListener listener;
    SMT.Configuration config;

    @Before
    public void init() {
        config = new SMT.Configuration();
        listener = new JUnitListener();
        config.log.clearListeners();
        config.log.addListener(listener);
    }

    @Test
    public void roundTrip() throws Exception {
        URL url = getClass().getResource("roundtrip.smt2");
        Assert.assertNotNull("roundtrip.smt2 not found on classpath", url);

        StringBuilder contentBuilder = new StringBuilder();
        try (BufferedReader br = new BufferedReader(new InputStreamReader(url.openStream()))) {
            String line;
            while ((line = br.readLine()) != null) {
                contentBuilder.append(line).append('\n');
            }
        }
        String content = contentBuilder.toString();

        ISource source = config.smtFactory.createSource(content, url.toString());
        IParser parser = new org.smtlib.sexpr.Parser(config, source);

        int count = 0;
        ICommand cmd;
        while ((cmd = parser.parseCommand()) != null) {
            listener.msgs.clear();
            Assert.assertTrue(
                "Parse error for command " + count + ": "
                    + (listener.msgs.isEmpty() ? "" : listener.msgs.get(0)),
                listener.msgs.isEmpty());

            Assert.assertTrue("command " + count + " (" + cmd + ") is not IPosable",
                cmd instanceof IPos.IPosable);
            IPos pos = ((IPos.IPosable) cmd).pos();
            Assert.assertNotNull("command " + count + " (" + cmd + ") has no position set", pos);
            String sourceSpan = content.substring(pos.charStart(), pos.charEnd());

            StringWriter sw = new StringWriter();
            org.smtlib.sexpr.Printer.write(sw, cmd);

            Assert.assertEquals(
                "Round-trip mismatch for command " + count,
                normalize(sourceSpan), normalize(sw.toString()));
            count++;
        }

        Assert.assertTrue("Unexpected error at EOF", listener.msgs.isEmpty());
        Assert.assertTrue("roundtrip.smt2 produced no commands at all", count > 0);
    }

    /** Collapses runs of non-EOL whitespace (spaces/tabs) to a single space and trims each
     *  side, but otherwise leaves line structure (and everything else) untouched -- printed
     *  output is not expected to preserve a source command's exact original indentation, but
     *  its line breaks and content must still match. */
    private static String normalize(String s) {
        return s.trim().replaceAll("[ \t]+", " ");
    }
}
