package org.smtlib.test;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.util.concurrent.TimeUnit;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.SMT;

/** Attributes in theory definitions supplied with -L: a sort's :right-assoc drives the n-ary
 *  sugar (#203). JUnit because each test writes its own theory and logic files. */
public class TheoryAttributeTests {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    private SMT smt;
    private ByteArrayOutputStream outBuf;
    private PrintStream outPs;
    private File dir;

    @Before
    public void setUp() throws Exception {
        smt = new SMT();
        outBuf = new ByteArrayOutputStream();
        outPs = new PrintStream(outBuf);
        smt.smtConfig.log.setChannels(outPs, outPs);
        dir = Files.createTempDirectory("smttheory").toFile();
    }

    @After
    public void tearDown() {
        if (smt != null) smt.cleanup();
        File[] files = dir.listFiles();
        if (files != null) for (File f : files) f.delete();
        dir.delete();
    }

    /** Writes theory T with the given :sorts and :funs contents, and logic L of Core and T */
    private void writeTheory(String sorts, String funs) throws Exception {
        try (PrintWriter pw = new PrintWriter(new File(dir, "T.smt2"))) {
            pw.println("(theory T :smt-lib-version 2.7");
            pw.println(" :sorts (" + sorts + ")");
            if (funs != null) pw.println(" :funs (" + funs + ")");
            pw.println(" :definition \"test theory\")");
        }
        try (PrintWriter pw = new PrintWriter(new File(dir, "L.smt2"))) {
            pw.println("(logic L :smt-lib-version 2.7 :theories (Core T) :language \"test\")");
        }
    }

    /** Runs the script with the test solver and returns the output */
    private String run(String script) {
        smt.exec(new String[]{"-L", dir.getAbsolutePath(), "--solver", "test", "--text", "(set-logic L)" + script});
        outPs.flush();
        return outBuf.toString();
    }

    private static void assertNoError(String out) {
        Assert.assertFalse("Unexpected error:\n" + out, out.contains("(error"));
    }

    private static void assertContains(String out, String phrase) {
        Assert.assertTrue("Expected: " + phrase + "\nActual output:\n" + out, out.contains(phrase));
    }

    @Test public void rightAssocSortFolds() throws Exception {
        writeTheory("(P 2 :right-assoc) (E 0)", null);
        // f's flat sort is (P E (P E E)), so f = g type-checks; h's sort differs
        String out = run("(declare-fun f () (P E E E))(declare-fun g () (P E (P E E)))(assert (= f g))"
                + "(declare-fun h () (P (P E E) E))(assert (= h f))");
        assertContains(out, "(error \"Argument 2 of = has sort (P E (P E E)), expected (P (P E E) E)");
        Assert.assertEquals(out, 1, out.split("\\(error", -1).length - 1);
    }

    @Test public void sortWithoutRightAssocDoesNotFold() throws Exception {
        // The sugar comes from the attribute, not from the name ->
        writeTheory("(-> 2) (E 0)", null);
        assertContains(run("(declare-fun f () (-> E E E))"), "The sort symbol -> expects 2 arguments, not 3");
    }

    @Test public void rightAssocSortTwoArgumentsUnchanged() throws Exception {
        writeTheory("(P 2 :right-assoc) (E 0)", null);
        assertNoError(run("(declare-fun f () (P E E))(declare-fun g () (P E E))(assert (= f g))"));
    }
}
