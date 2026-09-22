package org.smtlib.test;

import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.ICommand;
import org.smtlib.IExpr.IBinaryLiteral;
import org.smtlib.IExpr.IDecimal;
import org.smtlib.IExpr.IHexLiteral;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IResponse;
import org.smtlib.ISort;
import org.smtlib.SMT;
import org.smtlib.impl.Sort;
import org.smtlib.solvers.Solver_test;

/**
 * Covers a few in-memory AST-building entry points that, like {@link
 * CommandFactoryCoverageTest}, are only reachable by code that constructs a script
 * programmatically (the "API-constructed script" case) rather than by parsing text --
 * {@code sexpr.Parser} builds literals from lexer tokens directly, never through these
 * factory methods, and {@code Sort.FcnSort}'s single-argument (nullary) constructor is
 * never used internally either: every call site that builds an {@code impl.Sort.FcnSort}
 * (Sort.java's own {@code expand()}, and {@code impl.Factory#function}) always passes an
 * explicit (possibly empty) argument-sort array to the two-argument constructor instead.
 * Both are still real, documented, public API surface for a library consumer building an
 * AST by hand -- this is what actually exercises them.
 */
public class SortFactoryCoverageTest {

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

    /** The nullary convenience constructor: equivalent to the 2-arg form with an empty
     *  argument-sort array, but never exercised by any internal call site. */
    @Test
    public void fcnSortNullaryConstructor() {
        ISort boolSort = Sort.Bool();
        Sort.FcnSort nullary = new Sort.FcnSort(boolSort);
        Assert.assertEquals(0, nullary.argSorts().length);
        Assert.assertEquals(boolSort, nullary.resultSort());
        // Same shape as the 2-arg form with an explicit empty array.
        Sort.FcnSort explicit = new Sort.FcnSort(new ISort[0], boolSort);
        Assert.assertEquals(explicit.argSorts().length, nullary.argSorts().length);
        Assert.assertEquals(explicit.resultSort(), nullary.resultSort());
    }

    @Test
    public void declareConstViaCommandFactory() throws Exception {
        ISymbol x = config.exprFactory.symbol("x");
        ISort boolSort = Sort.Bool();
        ICommand.Ideclare_const c = config.commandFactory.declare_const(x, boolSort);
        Assert.assertEquals("declare-const", c.commandName());
        Assert.assertEquals(x, c.symbol());
        Assert.assertEquals("(declare-const x Bool)", config.defaultPrinter.toString(c));
        IResponse r = c.execute(solver);
        Assert.assertFalse(r.isError());
    }

    @Test
    public void declareSortViaCommandFactory() throws Exception {
        ISymbol s = config.exprFactory.symbol("S");
        INumeral arity = config.exprFactory.numeral(0);
        ICommand.Ideclare_sort c = config.commandFactory.declare_sort(s, arity);
        Assert.assertEquals("declare-sort", c.commandName());
        Assert.assertEquals("(declare-sort S 0)", config.defaultPrinter.toString(c));
        IResponse r = c.execute(solver);
        Assert.assertFalse(r.isError());
    }

    @Test
    public void declareSortParameterViaCommandFactory() throws Exception {
        ISymbol t = config.exprFactory.symbol("T");
        ICommand.Ideclare_sort_parameter c = config.commandFactory.declare_sort_parameter(t);
        Assert.assertEquals("declare-sort-parameter", c.commandName());
        Assert.assertEquals("(declare-sort-parameter T)", config.defaultPrinter.toString(c));
        IResponse r = c.execute(solver);
        Assert.assertFalse(r.isError());
    }

    @Test
    public void literalFactoryMethods() {
        INumeral n = config.exprFactory.numeral("42");
        Assert.assertEquals(42, n.intValue());

        IDecimal d = config.exprFactory.decimal("3.5");
        Assert.assertEquals("3.5", config.defaultPrinter.toString(d));

        IStringLiteral s = config.exprFactory.unquotedString("hello");
        Assert.assertEquals("hello", s.value());

        IBinaryLiteral b = config.exprFactory.binary("101");
        Assert.assertEquals("#b101", config.defaultPrinter.toString(b));

        IHexLiteral h = config.exprFactory.hex("ff");
        Assert.assertEquals("#xff", config.defaultPrinter.toString(h));
    }
}
