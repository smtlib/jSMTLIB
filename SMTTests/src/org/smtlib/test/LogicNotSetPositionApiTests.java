package org.smtlib.test;

import org.junit.Assert;
import org.junit.Test;
import org.smtlib.ICommand;
import org.smtlib.IResponse;
import org.smtlib.ISource;
import org.smtlib.SMT;
import org.smtlib.solvers.Solver_test;

/** A declaration issued before set-logic gets an error positioned at the command when executed
 *  through the API, not only through the command-line driver, which positions unpositioned errors. */
public class LogicNotSetPositionApiTests {

    @Test
    public void declarationErrorsHaveCommandPosition() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        Solver_test solver = new Solver_test(config, "test");
        String[] commands = {
            "(declare-fun f () Bool)", "(declare-const c Bool)", "(define-fun g () Bool true)",
            "(define-const h Bool true)", "(declare-sort S 0)", "(define-sort T () Bool)",
        };
        for (String text: commands) {
            ISource source = config.smtFactory.createSource(text, null);
            ICommand cmd = config.smtFactory.createParser(config, source).parseCommand();
            IResponse r = cmd.execute(solver);
            Assert.assertTrue(text, r.isError());
            Assert.assertNotNull(text, cmd.pos());
            Assert.assertEquals(text, cmd.pos(), ((IResponse.IError) r).pos());
        }
    }
}
