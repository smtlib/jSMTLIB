package org.smtlib.test;

import java.io.IOException;
import java.util.Arrays;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;
import org.smtlib.ICommand;
import org.smtlib.IExpr;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.ISort;
import org.smtlib.SMT;
import org.smtlib.SolverProcess;
import org.smtlib.command.C_declare_fun;
import org.smtlib.solvers.Solver_simplify;
import org.smtlib.solvers.Solver_test;

/** A sort parameter named in an API-built sort (createSortExpression(A)) means the command's own
 *  parameter, as it does in parsed text, where the parser puts the parameter object itself in
 *  the sort (#209). The parser cannot build this form, so these are API tests. */
public class ApiSortParameterNamesTests {

    private SMT.Configuration config;
    private IExpr.IFactory f;
    private ISort.IFactory sf;
    private ICommand.IFactory cf;

    private void init() {
        config = new SMT.Configuration();
        config.relax = true; // for declare-fun par
        f = config.exprFactory;
        sf = config.sortFactory;
        cf = config.commandFactory;
    }

    private ISort named(String name, ISort... args) {
        return sf.createSortExpression(f.symbol(name), args);
    }

    private static void ok(IResponse r) {
        Assert.assertTrue(r.isError() ? ((IResponse.IError) r).errorMsg() : "", r.isOK());
    }

    private Solver_test testSolver() {
        Solver_test s = new Solver_test(config, "test");
        ok(s.start());
        return s;
    }

    private Solver_simplify simplifySolver() {
        Solver_simplify s = new Solver_simplify(config, "simplify") {
            { solverProcess = new FakeSolverProcess(); }
        };
        ok(s.start());
        return s;
    }

    /** define-sort T (A) (Array A Bool); (T Bool) is (Array Bool Bool) */
    private void defineSort(ISolver s) {
        ok(s.set_logic("ALL", null));
        ISort.IParameter a = sf.createSortParameter(f.symbol("A"));
        ok(cf.define_sort(f.symbol("T"), Arrays.asList(a), named("Array", named("A"), sf.Bool())).execute(s));
        ok(cf.declare_const(f.symbol("x"), named("T", sf.Bool())).execute(s));
        ok(cf.assertCommand(f.fcn(f.symbol("select"), f.symbol("x"), f.symbol("true"))).execute(s));
        // and not (Array Int Bool)
        Assert.assertTrue(cf.assertCommand(f.fcn(f.symbol("select"), f.symbol("x"), f.numeral(1))).execute(s).isError());
    }

    /** declare-fun par (P) (g P P); (g 1) is an Int */
    private void declareFunPar(ISolver s) {
        ok(s.set_logic("ALL", null));
        ISort.IParameter p = sf.createSortParameter(f.symbol("P"));
        ok(new C_declare_fun(f.symbol("g"), Arrays.asList(named("P")), named("P"), List.of(), Arrays.asList(p)).execute(s));
        IExpr g1 = f.fcn(f.symbol("g"), f.numeral(1));
        ok(cf.assertCommand(f.fcn(f.symbol("="), g1, f.numeral(1))).execute(s));
        Assert.assertTrue(cf.assertCommand(g1).execute(s).isError());
    }

    @Test
    public void defineSortTest() {
        init();
        defineSort(testSolver());
    }

    @Test
    public void defineSortSimplify() {
        init();
        defineSort(simplifySolver());
    }

    @Test
    public void declareFunParTest() {
        init();
        declareFunPar(testSolver());
    }

    @Test
    public void declareFunParSimplify() {
        init();
        declareFunPar(simplifySolver());
    }

    /** Answers every command without a real process. */
    static class FakeSolverProcess extends SolverProcess {
        FakeSolverProcess() {
            super(new String[]{"dummy"}, "\n", null);
        }

        @Override
        public void start(boolean listen) {
        }

        @Override
        public String sendAndListen(String... args) throws IOException {
            return "";
        }
    }
}
