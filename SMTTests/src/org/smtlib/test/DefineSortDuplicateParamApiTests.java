package org.smtlib.test;

import java.util.Arrays;

import org.junit.Assert;
import org.junit.Test;
import org.smtlib.ICommand;
import org.smtlib.IExpr;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.ISort;
import org.smtlib.SMT;
import org.smtlib.solvers.Solver_test;

/** A define-sort with a duplicated parameter, executed through the API, is reported as an error.
 *  The command-line driver rejects it earlier, in TypeChecker.validate; API and script callers skip
 *  that step, so TypeChecker.checkSortAbbreviation's own duplicate check is what catches it (#177). */
public class DefineSortDuplicateParamApiTests {

    @Test
    public void duplicateSortParameterIsAnError() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        ISolver solver = new Solver_test(config, "test");
        IExpr.IFactory f = config.exprFactory;
        ISort.IFactory sf = config.sortFactory;
        ICommand.IFactory cf = config.commandFactory;
        Assert.assertTrue(solver.set_logic("ALL", null).isOK());

        ISort.IParameter x1 = sf.createSortParameter(f.symbol("X"));
        ISort.IParameter x2 = sf.createSortParameter(f.symbol("X"));
        IResponse r = cf.define_sort(f.symbol("S"), Arrays.asList(x1, x2), x1).execute(solver);
        Assert.assertTrue(r.isError());
        Assert.assertEquals("Duplicate sort parameters: X", ((IResponse.IError) r).errorMsg());

        // S was not defined
        ISort use = sf.createSortExpression(f.symbol("S"),
                Arrays.asList(sf.createSortExpression(f.symbol("Int")), sf.createSortExpression(f.symbol("Int"))));
        r = cf.declare_const(f.symbol("y"), use).execute(solver);
        Assert.assertTrue(r.isError());
    }

    @Test
    public void distinctSortParametersAreAccepted() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        ISolver solver = new Solver_test(config, "test");
        IExpr.IFactory f = config.exprFactory;
        ISort.IFactory sf = config.sortFactory;
        ICommand.IFactory cf = config.commandFactory;
        Assert.assertTrue(solver.set_logic("ALL", null).isOK());

        ISort.IParameter x = sf.createSortParameter(f.symbol("X"));
        ISort.IParameter y = sf.createSortParameter(f.symbol("Y"));
        Assert.assertTrue(cf.define_sort(f.symbol("S"), Arrays.asList(x, y), x).execute(solver).isOK());
    }
}
