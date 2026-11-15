package org.smtlib.test;

import java.io.OutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;
import org.smtlib.SMT;

/**
 * The public table of command-line options (#223): every option is accepted by processCommandLine with a
 * value of its kind, and valueIn reads that value back from the configuration. Stays a JUnit test: the
 * table is API, not observable from a script.
 */
public class OptionTableTests {

    /** A sample value for each kind of option, and what valueIn should return for it */
    private static String sample(SMT.Option o) {
        return switch (o.kind()) {
            case FLAG -> null;
            case INTEGER -> "3";
            case NUMBER -> "2.5";
            case STRING -> "some text";
            case PATH -> "/no/such/path";
            case SOLVER -> "z3-4.16.0";
            case SMTLIB_OPTION -> ":produce-models true";
            case CHANNEL -> "stderr";
        };
    }

    private static Object expected(SMT.Option o, String sample) {
        return switch (o.kind()) {
            case FLAG -> Boolean.TRUE;
            case INTEGER -> 3;
            case NUMBER -> 2.5;
            case SMTLIB_OPTION -> List.of(sample);
            default -> sample;
        };
    }

    /** A new SMT whose output is discarded */
    private static SMT quiet() {
        SMT smt = new SMT();
        PrintStream sink = new PrintStream(OutputStream.nullOutputStream());
        smt.smtConfig.stdout = sink;
        smt.smtConfig.stderr = sink;
        smt.smtConfig.log.setChannels(sink, sink);
        return smt;
    }

    @Test
    public void everyOptionIsAcceptedAndReadBack() {
        for (SMT.Option o : SMT.options()) {
            SMT smt = quiet();
            List<String> args = new ArrayList<>();
            if (o.name().equals("--exec")) args.addAll(List.of("--solver", "z3-4.16.0"));   // --exec needs a solver
            args.add(o.name());
            String sample = sample(o);
            if (sample != null) args.add(sample);
            int r = smt.processCommandLine(args.toArray(String[]::new), smt.smtConfig);
            if (o.name().equals("--help") || o.name().equals("--version")) {
                Assert.assertEquals(o.name() + " is an action", -1, r);
                Assert.assertNull(o.name(), o.valueIn(smt.smtConfig));
                continue;
            }
            Assert.assertEquals(o.name() + " accepted", 0, r);
            Assert.assertEquals(o.name() + " read back", expected(o, sample), o.valueIn(smt.smtConfig));
        }
    }

    @Test
    public void shortNamesAreAliases() {
        for (SMT.Option o : SMT.options()) {
            if (o.shortName() == null) continue;
            SMT smt = quiet();
            List<String> args = new ArrayList<>();
            if (o.name().equals("--exec")) args.addAll(List.of("--solver", "z3-4.16.0"));   // --exec needs a solver
            args.add(o.shortName());
            String sample = sample(o);
            if (sample != null) args.add(sample);
            int r = smt.processCommandLine(args.toArray(String[]::new), smt.smtConfig);
            if (o.name().equals("--help")) {
                Assert.assertEquals(-1, r);
                continue;
            }
            Assert.assertEquals(o.shortName() + " accepted", 0, r);
            Assert.assertEquals(o.shortName() + " read back", expected(o, sample), o.valueIn(smt.smtConfig));
        }
    }

    @Test
    public void flagsAreOffByDefault() {
        SMT smt = quiet();
        Assert.assertEquals(0, smt.processCommandLine(new String[0], smt.smtConfig));
        for (SMT.Option o : SMT.options()) {
            if (o.kind() != SMT.OptionKind.FLAG || o.valueIn(smt.smtConfig) == null) continue;
            Assert.assertEquals(o.name(), !o.name().equals("--no-pipeline"), !(Boolean) o.valueIn(smt.smtConfig));
        }
    }

    @Test
    public void repeatedOptionsAccumulate() {
        SMT smt = quiet();
        Assert.assertEquals(0, smt.processCommandLine(new String[] {
                "--set-option", ":produce-models true", "--set-option", ":produce-unsat-cores true" }, smt.smtConfig));
        SMT.Option setOption = SMT.options().stream().filter(o -> o.name().equals("--set-option")).findFirst().get();
        Assert.assertTrue(setOption.repeatable());
        Assert.assertEquals(List.of(":produce-models true", ":produce-unsat-cores true"), setOption.valueIn(smt.smtConfig));
    }
}
