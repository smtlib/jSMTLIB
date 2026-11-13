package org.smtlib.test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;

import org.junit.Assert;
import org.junit.Test;
import org.smtlib.ICommand;
import org.smtlib.IResponse;
import org.smtlib.ISource;
import org.smtlib.SMT;
import org.smtlib.solvers.Solver_test;

/** (reset) returns to the command-line settings, as at startup: here the output channels a caller set before
 *  starting the solver, as --out and --diag do, which the tests/getset_option tests cannot show (#205 item 35). */
public class ResetStartupSettingsApiTests {

    private IResponse run(SMT.Configuration config, Solver_test solver, String text) throws Exception {
        ISource source = config.smtFactory.createSource(text, null);
        ICommand cmd = config.smtFactory.createParser(config, source).parseCommand();
        return solver.execute(cmd);
    }

    @Test
    public void resetRestoresTheStartupChannels() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        PrintStream out = new PrintStream(new ByteArrayOutputStream());
        PrintStream diag = new PrintStream(new ByteArrayOutputStream());
        config.stdout = new PrintStream(new ByteArrayOutputStream());
        config.stderr = new PrintStream(new ByteArrayOutputStream());
        config.log.setChannels(out, diag);
        Solver_test solver = new Solver_test(config, "test");
        solver.start();
        Assert.assertTrue(run(config, solver, "(set-option :regular-output-channel \"stderr\")").isOK());
        Assert.assertTrue(run(config, solver, "(set-option :diagnostic-output-channel \"stdout\")").isOK());
        Assert.assertNotSame(out, config.log.getOut());
        Assert.assertTrue(run(config, solver, "(reset)").isOK());
        Assert.assertSame(out, config.log.getOut());
        Assert.assertSame(diag, config.log.getDiag());
    }

    @Test
    public void resetRestoresQuietAndSeed() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        config.nosuccess = true;
        config.seed = 7;
        Solver_test solver = new Solver_test(config, "test");
        solver.start();
        Assert.assertTrue(run(config, solver, "(set-option :print-success true)").isOK());
        Assert.assertTrue(run(config, solver, "(set-option :random-seed 3)").isOK());
        Assert.assertTrue(run(config, solver, "(reset)").isOK());
        Assert.assertTrue(config.nosuccess);
        Assert.assertEquals("false", run(config, solver, "(get-option :print-success)").toString());
        Assert.assertEquals("7", run(config, solver, "(get-option :random-seed)").toString());
    }
}
