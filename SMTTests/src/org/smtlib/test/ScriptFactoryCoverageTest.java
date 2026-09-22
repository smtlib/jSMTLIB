package org.smtlib.test;

import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.ICommand;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IResponse;
import org.smtlib.ISort;
import org.smtlib.SMT;
import org.smtlib.impl.Sort;
import org.smtlib.solvers.Solver_test;

/**
 * Covers {@code ICommand.IFactory#script()}, the no-arg factory method for building a script
 * programmatically, and {@code ICommand.IScript#add(ICommand)}. Before these were added, the
 * only way to assemble a script via the API was {@code new org.smtlib.impl.Script()} plus
 * direct mutation of the (nullable) list returned by {@code commands()} -- see the standalone
 * {@code APIExample.java} demo, which does exactly that. Neither path went through
 * {@code ICommand.IFactory} or a typed mutator on the {@code IScript} interface itself.
 */
public class ScriptFactoryCoverageTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    SMT.Configuration config;
    Solver_test solver;

    @Before
    public void init() throws Exception {
        config = new SMT.Configuration();
        solver = new Solver_test(config, "test");
        solver.start();
        solver.set_logic("QF_UF", null);
    }

    @Test
    public void emptyScriptViaFactory() {
        ICommand.IScript script = config.commandFactory.script();
        Assert.assertNull(script.filename());
        Assert.assertNotNull(script.commands());
        Assert.assertTrue(script.commands().isEmpty());
    }

    @Test
    public void addCommandsAndExecute() throws Exception {
        ICommand.IScript script = config.commandFactory.script();

        ISymbol x = config.exprFactory.symbol("x");
        ISort boolSort = Sort.Bool();
        script.add(config.commandFactory.declare_const(x, boolSort));
        script.add(config.commandFactory.assertCommand(x));
        script.add(config.commandFactory.check_sat());

        Assert.assertEquals(3, script.commands().size());

        IResponse response = script.execute(solver);
        Assert.assertFalse(config.defaultPrinter.toString(response), response.isError());
    }
}
