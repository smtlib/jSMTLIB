package org.smtlib.test;

import org.junit.Assert;
import org.junit.Test;
import org.smtlib.AbstractSolver;
import org.smtlib.ICommand;
import org.smtlib.IResponse;
import org.smtlib.ISource;
import org.smtlib.SMT;
import org.smtlib.solvers.Solver_test;

/** Once exited, the test solver answers every command but exit as process-based solvers do (the
 *  command-line driver stops at exit, so only API callers can send commands afterwards). */
public class SolverTestExitApiTests {

    private IResponse run(SMT.Configuration config, Solver_test solver, String text) throws Exception {
        ISource source = config.smtFactory.createSource(text, null);
        ICommand cmd = config.smtFactory.createParser(config, source).parseCommand();
        return solver.execute(cmd);
    }

    @Test
    public void commandsAfterExitAnswerExited() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        Solver_test solver = new Solver_test(config, "test");
        Assert.assertTrue(run(config, solver, "(set-logic QF_UF)").isOK());
        Assert.assertTrue(run(config, solver, "(exit)").isOK());
        for (String text: new String[]{"(declare-fun p () Bool)", "(check-sat)", "(echo \"x\")"}) {
            IResponse r = run(config, solver, text);
            Assert.assertTrue(text, r.isError());
            Assert.assertEquals(text, AbstractSolver.SOLVER_EXITED, ((IResponse.IError) r).errorMsg());
        }
        Assert.assertTrue(run(config, solver, "(exit)").isOK());
    }
}
