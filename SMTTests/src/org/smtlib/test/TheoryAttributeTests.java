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
 *  sugar (#203); :left-assoc, :right-assoc, :chainable and :pairwise are validated when the
 *  theory is loaded (#217). JUnit because each test writes its own theory and logic files. */
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

    /** Runs the script with the test solver, in a fresh SMT, and returns the output */
    private String run(String script) {
        smt.cleanup();
        smt = new SMT();
        outBuf.reset();
        smt.smtConfig.log.setChannels(outPs, outPs);
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

    // ---- #217: function attributes ----

    private static final String SORTS = "(E 0) (F 0) (G 2)";

    private void assertLoadError(String funs, String phrase) throws Exception {
        writeTheory(SORTS, funs);
        String out = run("");
        assertContains(out, phrase);
        assertContains(out, "in theory T");
    }

    private void assertLoads(String funs) throws Exception {
        writeTheory(SORTS, funs);
        assertNoError(run(""));
    }

    @Test public void attributeWithValue() throws Exception {
        assertLoadError("(f E E E :left-assoc 3)", "The :left-assoc attribute takes no value");
    }

    @Test public void twoAssocAttributes() throws Exception {
        assertLoadError("(f E E E :left-assoc :right-assoc)",
                "The declaration of f has more than one of :left-assoc, :right-assoc, :chainable and :pairwise");
    }

    @Test public void assocNeedsTwoArguments() throws Exception {
        assertLoadError("(f E E :left-assoc)", "The :left-assoc attribute of f needs exactly two argument sorts");
        assertLoadError("(c E :chainable)", "The :chainable attribute of c needs exactly two argument sorts");
        assertLoadError("(g E E E E :pairwise)", "The :pairwise attribute of g needs exactly two argument sorts");
    }

    @Test public void leftAssocRank() throws Exception {
        assertLoadError("(f E F F :left-assoc)", "The :left-assoc attribute of f needs a rank of the form (A B A)");
        assertLoads("(f E F E :left-assoc)");
    }

    @Test public void rightAssocRank() throws Exception {
        assertLoadError("(f E F E :right-assoc)", "The :right-assoc attribute of f needs a rank of the form (A B B)");
        assertLoads("(f E F F :right-assoc)");
    }

    @Test public void chainablePairwiseRank() throws Exception {
        assertLoadError("(f E F Bool :chainable)", "The :chainable attribute of f needs a rank of the form (A A Bool)");
        assertLoadError("(f E E E :pairwise)", "The :pairwise attribute of f needs a rank of the form (A A Bool)");
        assertLoadError("(par (X Y) (f X Y Bool :pairwise))", "The :pairwise attribute of f needs a rank of the form (A A Bool)");
        assertLoads("(f E E Bool :chainable) (par (X) (h X X Bool :pairwise))");
    }

    @Test public void parRanks() throws Exception {
        // The result must unify with argument 1 (2) of a copy with fresh parameters
        assertLoads("(par (X) (f X E X :left-assoc))");
        assertLoads("(par (A) (h A E E :left-assoc))");
        assertLoads("(par (A B) (ap (G A B) A B :left-assoc))"); // HO-Core's @ shape
        assertLoads("(par (X) (ins X (G X X) (G X X) :right-assoc))");
        assertLoadError("(par (X) (m (G X X) X E :left-assoc))",
                "The :left-assoc attribute of m needs a rank of the form (A B A)");
    }

    @Test public void validAttributesTakeEffect() throws Exception {
        writeTheory(SORTS, "(f E F E :left-assoc) (e E) (x F)");
        assertNoError(run("(declare-fun y () E)(assert (= y (f e x x x)))"));
    }

    @Test public void userDefinedAttributesAccepted() throws Exception {
        assertLoads("(f E E E :my-attribute 3 :other)");
    }

    // ---- #217: sort attributes ----

    @Test public void rightAssocSortNeedsArityTwo() throws Exception {
        writeTheory("(P 3 :right-assoc)", null);
        String out = run("");
        assertContains(out, "The :right-assoc attribute of sort P needs arity 2");
        assertContains(out, "in theory T");
    }

    @Test public void rightAssocSortTakesNoValue() throws Exception {
        writeTheory("(P 2 :right-assoc 1)", null);
        assertContains(run(""), "The :right-assoc attribute takes no value");
    }

    @Test public void otherAssocAttributesOnSortWarnAndAreIgnored() throws Exception {
        writeTheory("(P 2 :left-assoc) (Q 2 :chainable) (R 2 :pairwise) (E 0)", null);
        String out = run("(declare-fun f () (P E E E))");
        assertContains(out, "WARNING: The :left-assoc attribute has no meaning on a sort declaration and is ignored (sort P, in theory T)");
        assertContains(out, "WARNING: The :chainable attribute");
        assertContains(out, "WARNING: The :pairwise attribute");
        assertContains(out, "The sort symbol P expects 2 arguments, not 3");
    }
}
