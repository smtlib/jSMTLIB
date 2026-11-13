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

/** jSMTLIB's --verbose (its own diagnostic output) and a script's :verbosity (the solver's option) are
 *  independent: neither the option nor a reset changes --verbose (#205 item 35). The tests/getset_option
 *  test ok_verbosityIsSolverOption checks the other direction, for every solver. */
public class VerboseVsVerbosityApiTests {

    private IResponse run(SMT.Configuration config, Solver_test solver, String text) throws Exception {
        ISource source = config.smtFactory.createSource(text, null);
        ICommand cmd = config.smtFactory.createParser(config, source).parseCommand();
        return solver.execute(cmd);
    }

    @Test
    public void verbosityAndResetLeaveVerboseAlone() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        config.verbose = 2;
        ByteArrayOutputStream buf = new ByteArrayOutputStream();
        config.log.setChannels(new PrintStream(buf), new PrintStream(buf));
        Solver_test solver = new Solver_test(config, "test");
        solver.start();
        Assert.assertTrue(run(config, solver, "(set-option :verbosity 0)").isOK());
        Assert.assertEquals(2, config.verbose);
        Assert.assertTrue(run(config, solver, "(reset)").isOK());
        Assert.assertEquals(2, config.verbose);
    }
}
