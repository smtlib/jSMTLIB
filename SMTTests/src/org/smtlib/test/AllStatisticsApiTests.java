package org.smtlib.test;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.concurrent.TimeUnit;

import org.junit.After;
import org.junit.Assert;
import org.junit.Assume;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.junit.runners.ParameterizedWithNames;
import org.smtlib.IExpr;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.ISort;
import org.smtlib.SMT;
import org.smtlib.command.C_declare_fun;

/** (get-info :all-statistics) after a check-sat, for each solver in SMT_TEST_SOLVERS: the response
 *  must parse as a non-empty list of attributes, each a keyword with a value. The statistics
 *  themselves vary by solver, version and run, so their content is not checked. */
@RunWith(ParameterizedWithNames.class)
public class AllStatisticsApiTests {

    /** Solver families whose response does not conform, with the reason; for these the test checks that it
     *  is still reported as an error, so that a fixed solver is noticed */
    private static final Map<String,String> NONCONFORMING = Map.of(
        "cvc5", "not SMT-LIB: quoted statistic names, values with units (0ms), { } maps");

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    private final String solvername;
    private SMT.Configuration config;
    private ISolver solver;

    public AllStatisticsApiTests(String solvername) {
        this.solvername = solvername;
    }

    @Parameters
    public static Collection<String[]> data() {
        List<String[]> list = new ArrayList<>();
        for (String s : LogicTests.solvers) list.add(new String[]{s});
        return list;
    }

    @Before
    public void start() throws Exception {
        SMT smt = new SMT();
        config = smt.smtConfig;
        config.props = config.readProperties();
        solver = config.createSolver(solvername, LogicTests.executable(smt, solvername));
        IResponse r = solver.start();
        Assert.assertFalse("start: " + r, r.isError());
    }

    @After
    public void stop() {
        if (solver != null) solver.forceExit();
    }

    private void ok(IResponse r, String what) {
        Assert.assertFalse(what + ": " + config.defaultPrinter.toString(r), r.isError());
    }

    @Test
    public void allStatisticsIsAnAttributeList() throws Exception {
        IExpr.IFactory f = config.exprFactory;
        ISort bool = config.sortFactory.createSortExpression(f.symbol("Bool"));
        ok(solver.set_logic("QF_UF", null), "set-logic");
        ok(solver.declare_fun(new C_declare_fun(f.symbol("p"), new ArrayList<ISort>(), bool)), "declare-fun");
        ok(solver.assertExpr(f.symbol("p")), "assert");
        ok(solver.check_sat(), "check-sat");

        IResponse r = solver.get_info(f.keyword(":all-statistics"));
        String text = config.defaultPrinter.toString(r);
        Assume.assumeFalse("does not report statistics", config.responseFactory.unsupported().equals(r));
        String reason = NONCONFORMING.get(solvername.replaceAll("[_-][0-9].*", ""));
        if (reason != null) {
            Assert.assertTrue("expected the known non-conformance (" + reason + "), got: " + text, r.isError());
            return;
        }
        Assert.assertTrue("not an attribute list: " + text, r instanceof IResponse.IAttributeList);
        List<IExpr.IAttribute<?>> attributes = ((IResponse.IAttributeList)r).attributes();
        Assert.assertFalse("no statistics: " + text, attributes.isEmpty());
        for (IExpr.IAttribute<?> a : attributes) {
            Assert.assertNotNull("an attribute without a keyword: " + text, a.keyword());
            Assert.assertNotNull("an attribute without a value: " + text, a.attrValue());
        }
    }
}
