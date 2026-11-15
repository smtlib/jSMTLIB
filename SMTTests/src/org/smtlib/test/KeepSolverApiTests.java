package org.smtlib.test;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;

import org.junit.Assert;
import org.junit.Assume;
import org.junit.Test;
import org.smtlib.SMT;

/**
 * SMT.keepSolver and SMT.continueWith (#224): the solver an exec() started stays, with its state, for
 * further commands, which are processed as script commands are. Stays a JUnit test: the API has no
 * command-line form.
 */
public class KeepSolverApiTests {

    /** An SMT whose output goes to buf */
    private static SMT capturing(ByteArrayOutputStream buf, String... args) {
        SMT smt = new SMT();
        PrintStream out = new PrintStream(buf, true, StandardCharsets.UTF_8);
        smt.smtConfig.stdout = out;
        smt.smtConfig.stderr = out;
        smt.smtConfig.log.setChannels(out, out);
        Assert.assertEquals(0, smt.processCommandLine(args, smt.smtConfig));
        return smt;
    }

    private static String text(ByteArrayOutputStream buf) {
        return buf.toString(StandardCharsets.UTF_8).replace("\r\n", "\n");
    }

    @Test
    public void stateIsKeptForFurtherCommands() {
        ByteArrayOutputStream buf = new ByteArrayOutputStream();
        SMT smt = capturing(buf, "--solver", "test", "-q");
        smt.keepSolver = true;
        smt.smtConfig.text = "(set-logic QF_UF)(declare-fun p () Bool)(assert p)(check-sat)";
        Assert.assertEquals(0, smt.exec());
        Assert.assertEquals("unknown\n", text(buf));
        buf.reset();
        // p is still declared: no error
        Assert.assertEquals(0, smt.continueWith("(assert (not p))(check-sat)"));
        Assert.assertEquals("unknown\n", text(buf));
        buf.reset();
        Assert.assertEquals(1, smt.continueWith("(assert q)"));
        Assert.assertTrue(text(buf), text(buf).contains("Unknown constant symbol q"));
        smt.cleanup();
    }

    @Test
    public void withoutKeepSolverThereIsNoSolver() {
        ByteArrayOutputStream buf = new ByteArrayOutputStream();
        SMT smt = capturing(buf, "--solver", "test", "-q");
        smt.smtConfig.text = "(set-logic QF_UF)";
        Assert.assertEquals(0, smt.exec());
        Assert.assertEquals(1, smt.continueWith("(check-sat)"));
        Assert.assertTrue(text(buf), text(buf).contains("There is no solver"));
    }

    @Test
    public void cleanupEndsTheKeptSolver() {
        ByteArrayOutputStream buf = new ByteArrayOutputStream();
        SMT smt = capturing(buf, "--solver", "test", "-q");
        smt.keepSolver = true;
        smt.smtConfig.text = "(set-logic QF_UF)";
        Assert.assertEquals(0, smt.exec());
        smt.cleanup();
        Assert.assertEquals(1, smt.continueWith("(check-sat)"));
        Assert.assertTrue(text(buf), text(buf).contains("There is no solver"));
    }

    @Test
    public void exitInTheScriptEndsTheSolver() {
        ByteArrayOutputStream buf = new ByteArrayOutputStream();
        SMT smt = capturing(buf, "--solver", "test", "-q");
        smt.keepSolver = true;
        smt.smtConfig.text = "(set-logic QF_UF)(exit)";
        Assert.assertEquals(0, smt.exec());
        Assert.assertEquals(1, smt.continueWith("(check-sat)"));
        smt.cleanup();
    }

    @Test
    public void realSolverGivesModelValues() {
        String dir = System.getenv("SMT_SOLVER_DIR");
        Assume.assumeTrue("z3-4.16.0 not present", dir != null && new File(dir, "z3-4.16.0").exists());
        ByteArrayOutputStream buf = new ByteArrayOutputStream();
        SMT smt = capturing(buf, "--solver", "z3-4.16.0", "-q", "--set-option", ":produce-models true");
        smt.keepSolver = true;
        smt.smtConfig.text = "(set-logic QF_LIA)(declare-fun x () Int)(assert (= x 7))(check-sat)";
        Assert.assertEquals(0, smt.exec());
        Assert.assertEquals("sat\n", text(buf));
        buf.reset();
        Assert.assertEquals(0, smt.continueWith("(get-value (x))"));
        Assert.assertEquals("((x 7))\n", text(buf));
        smt.cleanup();
    }
}
