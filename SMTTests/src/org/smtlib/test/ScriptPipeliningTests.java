package org.smtlib.test;

import java.io.File;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;
import org.junit.Assert;
import org.junit.Assume;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.ICommand;
import org.smtlib.IParser;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.ISource;
import org.smtlib.SMT;

/**
 * Tests of executing a script with SMT.Configuration.pipeline set: commands are sent without waiting
 * for each response where the adapter allows it, and the result is as without pipelining -- the first
 * error, or else the response to the last command. check-sat waits for the earlier responses, so it is
 * not sent after an error. Adapters that do not pipeline (z3-4.3, the test solver) execute the script
 * one command at a time. A test is skipped if its solver's executable is not in SMT_SOLVER_DIR.
 */
public class ScriptPipeliningTests {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    /** The executable in SMT_SOLVER_DIR, or null if it is not there */
    private static String exe(String name) {
        String dir = System.getenv("SMT_SOLVER_DIR");
        if (dir == null) return null;
        String exe = new File(dir, name).getPath();
        // absolute, as createSolver would otherwise resolve a relative path against SMT_SOLVER_DIR a second time
        return new File(exe).isFile() || new File(exe + ".exe").isFile() ? new File(exe).getAbsolutePath() : null;
    }

    /** A configuration that pipelines scripts */
    private static SMT.Configuration config() {
        SMT.Configuration config = new SMT.Configuration();
        config.pipeline = true;
        return config;
    }

    /** Starts the named solver (a name configured in jsmtlib.properties), whose executable is exeName */
    private static ISolver start(SMT.Configuration config, String solverName, String exeName) throws Exception {
        String exe = exe(exeName);
        Assume.assumeTrue(exeName + " executable not available", exe != null);
        config.props = config.readProperties(); // the adapter for the solver name comes from jsmtlib.properties
        ISolver solver = config.createSolver(solverName, exe);
        IResponse r = solver.start();
        Assert.assertFalse("start: " + r, r.isError());
        return solver;
    }

    private static List<ICommand> parse(SMT.Configuration config, String text) throws Exception {
        ISource source = config.smtFactory.createSource(text, null);
        IParser parser = new org.smtlib.sexpr.Parser(config, source);
        List<ICommand> commands = new ArrayList<>();
        ICommand cmd;
        while ((cmd = parser.parseCommand()) != null) commands.add(cmd);
        return commands;
    }

    /** Executes the text as one script */
    static IResponse execute(SMT.Configuration config, ISolver solver, String text) throws Exception {
        return config.commandFactory.script(null, parse(config, text)).execute(solver);
    }

    static final String DECLS =
            "(declare-fun x () Int)\n"
            + "(declare-const y Int)\n"
            + "(declare-fun f (Int) Int)\n"
            + "(define-fun g ((i Int)) Int (+ i 1))\n"
            + "(declare-sort S 0)\n"
            + "(declare-fun s () S)\n"
            + "(assert (> x y))\n"
            + "(assert (= (g x) (+ x 1)))\n";

    /** A script's response is its last command's, and check-sat's answer is the check-sat status */
    private static void checkScript(String solverName, String exeName) throws Exception {
        SMT.Configuration config = config();
        ISolver solver = start(config, solverName, exeName);
        try {
            Assert.assertEquals("declarations", config.responseFactory.success(),
                    execute(config, solver, "(set-logic ALL)\n" + DECLS));
            Assert.assertEquals("check-sat", config.responseFactory.sat(),
                    execute(config, solver, "(declare-fun x2 () Int)\n(assert (> x2 x))\n(push 1)\n(check-sat)\n"));
            Assert.assertEquals("status", config.responseFactory.sat(), solver.checkSatStatus());
            Assert.assertEquals("unsat", config.responseFactory.unsat(), execute(config, solver,
                    "(pop 1)\n(assert (forall ((i Int)) (! (> (f i) i) :pattern ((f i)))))\n(assert (= y (f x)))\n(check-sat)\n"));
        } finally {
            solver.exit();
        }
    }

    /** The first error is returned; the check-sat after it is not sent; if continues, the solver is still usable.
     *  (Whether the commands between the error and check-sat were executed differs with pipelining.) */
    private static void checkError(String solverName, String exeName, boolean continues) throws Exception {
        SMT.Configuration config = config();
        ISolver solver = start(config, solverName, exeName);
        try {
            execute(config, solver, "(set-logic ALL)\n");
            IResponse r = execute(config, solver,
                    "(declare-fun x () Int)\n(assert (> undeclared 0))\n(assert (+ x true))\n(declare-fun z () Int)\n(check-sat)\n");
            Assert.assertTrue("expected an error: " + r, r.isError());
            String text = config.defaultPrinter.toString(r);
            Assert.assertTrue("the first error: " + text, text.contains("undeclared"));
            Assert.assertNull("check-sat was not executed", solver.checkSatStatus());
            if (continues) {
                Assert.assertEquals("check-sat after the error", config.responseFactory.sat(),
                        execute(config, solver, "(declare-fun z2 () Int)\n(assert (> z2 x))\n(check-sat)\n"));
            }
        } finally {
            solver.exit();
        }
    }

    /** A script executed after the solver's whole-run limit ended it gets the timeout response */
    private static void checkAfterWholeRunLimit(String solverName, String exeName) throws Exception {
        SMT.Configuration config = config();
        config.timeoutTotal = 1;
        ISolver solver = start(config, solverName, exeName);
        try {
            IResponse r = execute(config, solver, WholeRunTimeoutTests.HARD_QUERY);
            Assert.assertEquals("check-sat at the whole-run limit", config.responseFactory.timeout(), r);
            r = execute(config, solver, "(declare-fun u () Int)\n(assert (> u 0))\n");
            Assert.assertEquals("a script after the whole-run limit", config.responseFactory.timeout(), r);
        } finally {
            IResponse r = solver.exit();
            Assert.assertFalse("exit after the whole-run limit: " + r, r.isError());
        }
    }

    @Test
    public void z3Script() throws Exception {
        checkScript("z3-4.16.0", "z3-4.16.0");
    }

    @Test
    public void cvc5Script() throws Exception {
        checkScript("cvc5-1.3.2", "cvc5-1.3.2");
    }

    @Test
    public void smtinterpolScript() throws Exception {
        checkScript("smtinterpol-2.5", "smtinterpol-2.5.jar");
    }

    @Test
    public void yices2Script() throws Exception {
        // yices2 has no quantifiers in ALL
        SMT.Configuration config = config();
        ISolver solver = start(config, "yices2-2.7.0", "yices2-2.7.0");
        try {
            Assert.assertEquals("unsat", config.responseFactory.unsat(), execute(config, solver,
                    "(set-logic QF_UFLIA)\n(declare-fun x () Int)\n(declare-fun f (Int) Int)\n(assert (> (f x) x))\n(assert (= x (f x)))\n(check-sat)\n"));
        } finally {
            solver.exit();
        }
    }

    @Test // does not pipeline: executed one command at a time
    public void z3_4_3Script() throws Exception {
        // The Linux ARM64 build of z3-4.3.1 answers the final check-sat 'unknown' (see issue #101)
        String arch = System.getProperty("os.arch").toLowerCase();
        Assume.assumeFalse("z3-4.3.1 on Linux ARM64 (issue #101)",
                System.getProperty("os.name").toLowerCase().contains("linux")
                && (arch.contains("aarch64") || arch.contains("arm64")));
        checkScript("z3-4.3", "z3-4.3.1");
    }

    @Test
    public void z3Error() throws Exception {
        checkError("z3-4.16.0", "z3-4.16.0", true);
    }

    @Test
    public void cvc5Error() throws Exception {
        checkError("cvc5-1.3.2", "cvc5-1.3.2", false);
    }

    @Test
    public void yices2Error() throws Exception {
        checkError("yices2-2.7.0", "yices2-2.7.0", false);
    }

    @Test
    public void smtinterpolError() throws Exception {
        checkError("smtinterpol-2.5", "smtinterpol-2.5.jar", true);
    }

    @Test
    public void z3_4_3Error() throws Exception {
        checkError("z3-4.3", "z3-4.3.1", true);
    }

    @Test
    public void z3AfterWholeRunLimit() throws Exception {
        checkAfterWholeRunLimit("z3-4.16.0", "z3-4.16.0");
    }

    @Test
    public void cvc5AfterWholeRunLimit() throws Exception {
        checkAfterWholeRunLimit("cvc5-1.3.2", "cvc5-1.3.2");
    }

    @Test // not run as a process: executed one command at a time
    public void testSolver() throws Exception {
        SMT.Configuration config = config();
        ISolver solver = config.createSolver("test", null);
        Assert.assertFalse(solver.start().isError());
        try {
            Assert.assertEquals(config.responseFactory.success(), execute(config, solver, "(set-logic ALL)\n" + DECLS));
            IResponse r = execute(config, solver, "(declare-fun w () Int)\n(assert (> undeclared 0))\n(check-sat)\n");
            Assert.assertTrue("expected an error: " + r, r.isError());
        } finally {
            solver.exit();
        }
    }
}
