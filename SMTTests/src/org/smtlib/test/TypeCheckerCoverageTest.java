package org.smtlib.test;

import java.util.Collections;
import java.util.List;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.IExpr;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IResponse;
import org.smtlib.ISort;
import org.smtlib.SMT;
import org.smtlib.SymbolTable;
import org.smtlib.TypeChecker;

/**
 * Nodes that parsed SMT-LIB text never gives the type checker, but the API can (#146): a parse-error node
 * (IExpr.IError) as a term, and a function signature (ISort.IFcnSort) as a sort. Each is a type-check error.
 * (A keyword, sort family or sort abbreviation cannot reach it: they are not IExprs or ISorts.) Also, the
 * static check methods report an internal crash under their own name.
 */
public class TypeCheckerCoverageTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    SMT.Configuration config;
    SymbolTable symTable;

    @Before
    public void init() {
        config = new SMT.Configuration();
        symTable = new SymbolTable(config);
    }

    /** The response to cmd, on the test solver after (set-logic ALL) */
    private IResponse execute(org.smtlib.ICommand cmd) throws Exception {
        org.smtlib.ISolver solver = config.createSolver("test", null);
        solver.start();
        Assert.assertFalse(config.commandFactory.set_logic(config.exprFactory.symbol("ALL")).execute(solver).isError());
        IResponse r = cmd.execute(solver);
        solver.exit();
        return r;
    }

    @Test
    public void errorNodeAsTerm() throws Exception {
        IExpr eq = config.exprFactory.fcn(config.exprFactory.symbol("="),
                config.exprFactory.error("bad"), config.exprFactory.error("bad"));
        IResponse r = execute(config.commandFactory.assertCommand(eq));
        Assert.assertTrue(config.defaultPrinter.toString(r), r.isError()
                && ((IResponse.IError)r).errorMsg().equals("The expression contains an error node: bad"));
    }

    @Test
    public void fcnSortAsSort() throws Exception {
        ISort.IFcnSort fcnSort = config.sortFactory.createFcnSort(
                new ISort[] { config.sortFactory.Bool() }, config.sortFactory.Bool());
        IResponse r = execute(config.commandFactory.declare_fun(config.exprFactory.symbol("x"),
                Collections.<ISort>emptyList(), fcnSort));
        Assert.assertTrue(config.defaultPrinter.toString(r), r.isError() && ((IResponse.IError)r).errorMsg()
                .equals("A function signature is not a sort: (-> Bool Bool)"));
    }

    /** An object whose every method but pos() throws, standing in for an API-built node that crashes the
     *  TypeChecker; the static check methods must report it under their own name. */
    @SuppressWarnings("unchecked")
    private <T> T crashing(Class<T> c) {
        return (T)java.lang.reflect.Proxy.newProxyInstance(c.getClassLoader(), new Class<?>[]{c},
                (proxy, method, args) -> {
                    if (method.getName().equals("pos")) return null;
                    throw new IllegalStateException("boom");
                });
    }

    private void assertReported(List<IResponse> errs, String what) {
        Assert.assertEquals(errs.toString(), 1, errs.size());
        String msg = config.defaultPrinter.toString(errs.get(0));
        Assert.assertTrue(msg, msg.contains("while checking " + what + ": java.lang.IllegalStateException: boom"));
    }

    @Test
    public void internalErrorsNameTheirCheck() throws Exception {
        ISymbol f = config.exprFactory.symbol("f");
        assertReported(TypeChecker.checkAssertion(symTable, crashing(IExpr.class)), "an assertion");
        assertReported(TypeChecker.check(symTable, crashing(IExpr.class)), "an expression");
        assertReported(TypeChecker.checkFcn(symTable, f, Collections.singletonList(crashing(ISort.class)),
                config.sortFactory.Bool(), (org.smtlib.IPos)null), "a function declaration");
        assertReported(TypeChecker.checkFcn(symTable, f, Collections.<IExpr.IDeclaration>emptyList(),
                crashing(ISort.class), f), "a function definition");
    }
}
