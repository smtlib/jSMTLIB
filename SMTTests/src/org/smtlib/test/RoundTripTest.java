package org.smtlib.test;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.io.StringWriter;
import java.net.URL;
import java.util.ArrayList;
import java.util.List;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.smtlib.ICommand;
import org.smtlib.IParser;
import org.smtlib.ISource;
import org.smtlib.SMT;

/**
 * Parses every command in roundtrip.smt2, writes each back via
 * {@code org.smtlib.sexpr.Printer}, and asserts that the written text
 * exactly reproduces the input line.
 *
 * <p>This exercises all command {@code write()} implementations and their
 * branches (empty vs. non-empty loops, attribute present/absent, etc.)
 * without invoking any solver.
 */
public class RoundTripTest {

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

        // Collect expected strings (non-comment, non-blank lines) and build
        // the full file content for the parser.
        List<String> expected = new ArrayList<>();
        StringBuilder content = new StringBuilder();
        try (BufferedReader br = new BufferedReader(
                new InputStreamReader(url.openStream()))) {
            String line;
            while ((line = br.readLine()) != null) {
                content.append(line).append('\n');
                String trimmed = line.trim();
                if (!trimmed.isEmpty() && !trimmed.startsWith(";")) {
                    expected.add(trimmed);
                }
            }
        }

        // Parse the entire file as a sequence of commands.
        ISource source = config.smtFactory.createSource(content.toString(), url.toString());
        IParser parser = new org.smtlib.sexpr.Parser(config, source);

        for (int i = 0; i < expected.size(); i++) {
            listener.msgs.clear();
            ICommand cmd = parser.parseCommand();
            Assert.assertNotNull(
                "parseCommand() returned null for command " + i + ": " + expected.get(i),
                cmd);
            Assert.assertTrue(
                "Parse error for command " + i + " (" + expected.get(i) + "): "
                    + (listener.msgs.isEmpty() ? "" : listener.msgs.get(0)),
                listener.msgs.isEmpty());
            StringWriter sw = new StringWriter();
            org.smtlib.sexpr.Printer.write(sw, cmd);
            Assert.assertEquals(
                "Round-trip mismatch for command " + i,
                expected.get(i), sw.toString());
        }

        // Confirm no extra commands remain in the file.
        listener.msgs.clear();
        ICommand extra = parser.parseCommand();
        Assert.assertNull(
            "Extra command in file after " + expected.size() + " expected commands",
            extra);
        Assert.assertTrue("Unexpected error at EOF", listener.msgs.isEmpty());
    }
}
