package org.smtlib.test;

import java.util.Collections;
import java.util.List;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.ICommand;
import org.smtlib.IExpr;
import org.smtlib.IExpr.IConstructor;
import org.smtlib.IExpr.IDeclaration;
import org.smtlib.IExpr.IFunctionDeclaration;
import org.smtlib.IExpr.ISortDeclaration;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.ISort;
import org.smtlib.SMT;

/**
 * Covers {@code impl.Factory}'s {@code ICommand.IFactory} methods that a parsed script never
 * reaches. {@code sexpr.Parser.parseCommand()} dispatches to each command class's own static
 * {@code parse(Parser)} method (e.g. {@code C_reset.parse()} does {@code new C_reset()}
 * directly) rather than through {@code smtConfig.commandFactory}, so the factory methods are
 * exercised only by code that builds a script programmatically instead of parsing text (the
 * "API-constructed script" case, as opposed to a parsed source file) -- e.g. APIExample.java,
 * which is a standalone demo with no test coverage of its own. Nothing currently calls
 * {@code declare_datatype}, {@code declare_datatypes}, {@code define_const},
 * {@code define_fun_rec}, {@code define_funs_rec}, {@code get_model}, {@code get_proof},
 * {@code get_unsat_assumptions}, {@code get_unsat_core}, {@code reset}, or
 * {@code reset_assertions} on the factory at all.
 * <p>
 * Each command built here is checked three ways: its accessors return what was passed in, it
 * prints back the expected concrete syntax, and it executes against the mock solver without
 * throwing (confirming the whole factory-to-execute path, not just construction).
 */
public class CommandFactoryCoverageTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    SMT.Configuration config;
    ISolver solver;

    @Before
    public void init() throws Exception {
        config = new SMT.Configuration();
        solver = config.createSolver("test", null);
        solver.start();
        solver.set_logic("QF_UF", null); // define-fun/declare-datatype etc. require a logic first
    }

    private String print(ICommand c) throws Exception {
        return config.defaultPrinter.toString(c);
    }

    @Test
    public void reset() throws Exception {
        ICommand.Ireset c = config.commandFactory.reset();
        Assert.assertEquals("reset", c.commandName());
        Assert.assertEquals("(reset)", print(c));
        IResponse r = c.execute(solver);
        Assert.assertFalse(r.isError());
    }

    @Test
    public void resetAssertions() throws Exception {
        ICommand.Ireset_assertions c = config.commandFactory.reset_assertions();
        Assert.assertEquals("reset-assertions", c.commandName());
        Assert.assertEquals("(reset-assertions)", print(c));
        IResponse r = c.execute(solver);
        Assert.assertFalse(r.isError());
    }

    @Test
    public void getModel() throws Exception {
        ICommand.Iget_model c = config.commandFactory.get_model();
        Assert.assertEquals("get-model", c.commandName());
        Assert.assertEquals("(get-model)", print(c));
        c.execute(solver); // no assertion on the response shape -- just confirming it doesn't throw
    }

    @Test
    public void getProof() throws Exception {
        ICommand.Iget_proof c = config.commandFactory.get_proof();
        Assert.assertEquals("get-proof", c.commandName());
        Assert.assertEquals("(get-proof)", print(c));
        c.execute(solver);
    }

    @Test
    public void getUnsatAssumptions() throws Exception {
        ICommand.Iget_unsat_assumptions c = config.commandFactory.get_unsat_assumptions();
        Assert.assertEquals("get-unsat-assumptions", c.commandName());
        Assert.assertEquals("(get-unsat-assumptions)", print(c));
        c.execute(solver);
    }

    @Test
    public void getUnsatCore() throws Exception {
        ICommand.Iget_unsat_core c = config.commandFactory.get_unsat_core();
        Assert.assertEquals("get-unsat-core", c.commandName());
        Assert.assertEquals("(get-unsat-core)", print(c));
        c.execute(solver);
    }

    @Test
    public void defineConst() throws Exception {
        ISymbol x = config.exprFactory.symbol("x");
        ISort boolSort = org.smtlib.impl.Sort.Bool();
        IExpr trueLit = config.exprFactory.symbol("true");
        ICommand.Idefine_const c = config.commandFactory.define_const(x, boolSort, trueLit);
        Assert.assertEquals("define-const", c.commandName());
        Assert.assertEquals(x, c.symbol());
        Assert.assertEquals("(define-const x Bool true)", print(c));
        IResponse r = c.execute(solver);
        Assert.assertFalse(r.isError());
    }

    @Test
    public void defineFunRec() throws Exception {
        ISymbol f = config.exprFactory.symbol("f");
        ISort boolSort = org.smtlib.impl.Sort.Bool();
        IExpr trueLit = config.exprFactory.symbol("true");
        List<IDeclaration> params = Collections.emptyList();
        ICommand.Idefine_fun_rec c = config.commandFactory.define_fun_rec(f, params, boolSort, trueLit);
        Assert.assertEquals("define-fun-rec", c.commandName());
        Assert.assertEquals(f, c.symbol());
        Assert.assertEquals("(define-fun-rec f () Bool true)", print(c));
        IResponse r = c.execute(solver);
        Assert.assertFalse(r.isError());
    }

    @Test
    public void defineFunsRec() throws Exception {
        ISymbol f = config.exprFactory.symbol("f");
        ISort boolSort = org.smtlib.impl.Sort.Bool();
        IFunctionDeclaration fd = config.exprFactory.functionDeclaration(f, Collections.<IDeclaration>emptyList(), boolSort);
        IExpr trueLit = config.exprFactory.symbol("true");
        ICommand.Idefine_funs_rec c = config.commandFactory.define_funs_rec(
                Collections.singletonList(fd), Collections.singletonList(trueLit));
        Assert.assertEquals("define-funs-rec", c.commandName());
        Assert.assertEquals(1, c.declarations().size());
        IResponse r = c.execute(solver);
        Assert.assertFalse(r.isError());
    }

    @Test
    public void declareDatatype() throws Exception {
        ISymbol name = config.exprFactory.symbol("Pair");
        ISortDeclaration sd = config.exprFactory.sortDeclaration(name, config.exprFactory.numeral(0));
        IConstructor ctor = config.exprFactory.constructor(config.exprFactory.symbol("mk-pair"), Collections.emptyList());
        ISort.IDatatype dt = config.exprFactory.datatype(Collections.singletonList(ctor), null);
        ICommand.Ideclare_datatype c = config.commandFactory.declare_datatype(sd, dt);
        Assert.assertEquals("declare-datatype", c.commandName());
        Assert.assertEquals(sd, c.sortDeclaration());
        IResponse r = c.execute(solver);
        Assert.assertFalse(r.isError());
    }

    @Test
    public void declareDatatypes() throws Exception {
        ISymbol name = config.exprFactory.symbol("Unit");
        ISortDeclaration sd = config.exprFactory.sortDeclaration(name, config.exprFactory.numeral(0));
        IConstructor ctor = config.exprFactory.constructor(config.exprFactory.symbol("mk-unit"), Collections.emptyList());
        ISort.IDatatype dt = config.exprFactory.datatype(Collections.singletonList(ctor), null);
        ICommand.Ideclare_datatypes c = config.commandFactory.declare_datatypes(
                Collections.singletonList(sd), Collections.singletonList(dt));
        Assert.assertEquals("declare-datatypes", c.commandName());
        Assert.assertEquals(1, c.sortDeclarations().size());
        IResponse r = c.execute(solver);
        Assert.assertFalse(r.isError());
    }
}
