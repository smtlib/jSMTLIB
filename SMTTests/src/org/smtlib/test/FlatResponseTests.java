package org.smtlib.test;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.PrintStream;
import java.nio.file.Files;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.junit.rules.Timeout;
import org.smtlib.SMT;

/** Flat replies (success, unsupported, an empty line) to structured commands, and the solver
 *  log file, through the command-line tool and a stub solver (FlatAnswerProcess) that gives
 *  them (#140). The log file is set through the API: no command-line option sets it. */
public class FlatResponseTests {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);
    @Rule public TemporaryFolder folder = new TemporaryFolder();

    private static final String SAT_SCRIPT = "(set-option :produce-assertions true)\n(set-option :produce-models true)\n"
            + "(set-option :produce-assignments true)\n(set-logic QF_UF)\n(declare-fun p () Bool)\n(check-sat)\n"
            + "(get-assertions)\n(get-value (p))\n(get-assignment)\n";
    private static final String UNSAT_SCRIPT = "(set-option :produce-unsat-cores true)\n"
            + "(set-option :produce-unsat-assumptions true)\n(set-logic QF_UF)\n(check-sat)\n"
            + "(get-unsat-core)\n(get-unsat-assumptions)\n";

    /** The output of the command-line tool on the script, with the stub answering check-sat
     *  with checkSat, and the solver log written to logfile if not null */
    static String run(String checkSat, String script, String logfile) {
        String javaBin = System.getProperty("java.home") + File.separator + "bin" + File.separator + "java";
        SMT smt = new SMT();
        smt.smtConfig.props = smt.smtConfig.readProperties();
        smt.smtConfig.props.setProperty("org.smtlib.solver_flat.command",
                javaBin + ",-cp," + System.getProperty("java.class.path") + ",org.smtlib.test.FlatAnswerProcess," + checkSat);
        smt.smtConfig.logfile = logfile;
        ByteArrayOutputStream outBuf = new ByteArrayOutputStream();
        PrintStream out = new PrintStream(outBuf);
        smt.smtConfig.log.setChannels(out, out);
        smt.smtConfig.stdout = out;
        smt.smtConfig.stderr = out;
        smt.exec(new String[]{"--solver", "flat", "--text", script});
        smt.cleanup();
        out.flush();
        return outBuf.toString().replace("\r\n", "\n");
    }

    /** get-assertions answered "success" is out of step (#149); get-value's empty line (printing
     *  nothing) and get-assignment's "unsupported" are passed on as those responses */
    @Test
    public void flatRepliesAfterSat() {
        Assert.assertEquals("success\nsuccess\nsuccess\nsuccess\nsuccess\nsat\n(get-assertions)\n^^^^^^^^^^^^^^^^\n"
                + "(error \"Out of step: the response to (get-assertions) was success\")\nunsupported\n",
                run("sat", SAT_SCRIPT, null));
    }

    /** As above for get-unsat-core ("success", out of step) and get-unsat-assumptions ("unsupported") */
    @Test
    public void flatRepliesAfterUnsat() {
        Assert.assertEquals("success\nsuccess\nsuccess\nunsat\n(get-unsat-core)\n^^^^^^^^^^^^^^^^\n"
                + "(error \"Out of step: the response to (get-unsat-core) was success\")\nunsupported\n",
                run("unsat", UNSAT_SCRIPT, null));
    }

    /** The log records the command, everything sent and received, and the exit */
    @Test
    public void solverLog() throws Exception {
        File log = new File(folder.getRoot(), "solver.log");
        run("sat", SAT_SCRIPT, log.getPath());
        String text = new String(Files.readAllBytes(log.toPath())).replace("\r\n", "\n");
        Assert.assertTrue(text, text.startsWith(";; "));
        Assert.assertTrue(text, text.contains("org.smtlib.test.FlatAnswerProcess sat"));
        Assert.assertTrue(text, text.contains("(set-option :print-success true)\n;OUT: success\n")); // #142
        Assert.assertTrue(text, text.contains("(set-logic QF_UF)\n;OUT: success\n"));
        Assert.assertTrue(text, text.contains("(get-value ( p))\n;OUT: \n"));
        Assert.assertTrue(text, text.contains("(get-assignment)\n;OUT: unsupported\n"));
        Assert.assertTrue(text, text.trim().endsWith(";;Exiting solver"));
    }

    /** A log file that cannot be created is reported, and the run goes on without it */
    @Test
    public void solverLogThatCannotBeCreated() {
        PrintStream savedErr = System.err;
        ByteArrayOutputStream errBuf = new ByteArrayOutputStream();
        System.setErr(new PrintStream(errBuf));
        String out;
        try {
            out = run("sat", SAT_SCRIPT, new File(folder.getRoot(), "no/such/dir/solver.log").getPath());
        } finally {
            System.setErr(savedErr);
        }
        Assert.assertTrue(errBuf.toString(), errBuf.toString().startsWith("Failed to create solver log file "));
        Assert.assertEquals(run("sat", SAT_SCRIPT, null), out);
    }
}
