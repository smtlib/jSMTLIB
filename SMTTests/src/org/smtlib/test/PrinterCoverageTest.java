package org.smtlib.test;

import java.io.StringWriter;
import java.util.Collections;
import java.util.List;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.smtlib.IExpr;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.ILogic;
import org.smtlib.IParser;
import org.smtlib.IResponse;
import org.smtlib.ISort;
import org.smtlib.ISource;
import org.smtlib.ITheory;
import org.smtlib.SMT;
import org.smtlib.sexpr.Sexpr;

/**
 * Covers the parts of {@code org.smtlib.sexpr.Printer} that {@link RoundTripTest}
 * cannot reach:
 * <ul>
 * <li>{@link ISort.IFamily}, {@link ISort.IAbbreviation}, and {@link ISort.IFcnSort} are
 * symbol-table <em>definition</em> objects (see {@link ISort.IDefinition}) - a
 * {@code declare-sort}/{@code define-sort} command prints its own name/arity/parameter
 * fields directly (see {@code Printer.visit(ICommand.Ideclare_sort)} and
 * {@code visit(ICommand.Idefine_sort)}), never by way of one of these objects, and a sort
 * *reference* is always an {@link ISort.IApplication} (possibly zero-arity), never a bare
 * {@code IFamily}. So these three kinds of sort can never appear in a parsed command's
 * write() output, and {@link RoundTripTest}'s command-level round-tripping structurally
 * cannot exercise them - they are only ever printed via direct {@code toString()}/{@code
 * accept()} calls, which is what this test does instead. ({@link ISort.IApplication} and
 * {@link ISort.IParameter}, by contrast, are already covered by {@link RoundTripTest} via
 * {@code roundtrip.smt2}'s sort-valued command arguments and {@code define-sort} parameter
 * lists respectively.)
 * <li>{@link ILogic}/{@link ITheory} are parsed and printed independently of the
 * {@link ICommand} stream (see {@code IParser.parseLogic()}/{@code parseTheory()}), so they
 * need their own round-trip coverage.
 * <li>The structured {@link IResponse} subtypes ({@code IAssertionsResponse},
 * {@code IAssignmentResponse}, {@code IProofResponse}, {@code IValueResponse},
 * {@code IUnsatCoreResponse}, {@code IUnsatAssumptionsResponse}, {@code IAttributeList})
 * are solver-side results, built via {@code IResponse.IFactory} in Java code (e.g. a
 * {@code get-value} command execution), never parsed from command/logic/theory text - so
 * they need direct construction too.
 * <li>{@code Sexpr.Token}/{@code Sexpr.Expr} (in {@code org.smtlib.sexpr.Sexpr}) are never
 * constructed by the parser either - the parser builds the real typed leaf AST classes
 * directly instead of going through {@code ISexpr.IToken}, and {@code ISexpr.IFactory}
 * itself isn't actually wired up anywhere in {@code SMT.Configuration}.
 * </ul>
 */
public class PrinterCoverageTest {

    SMT.Configuration config;

    @Before
    public void init() {
        config = new SMT.Configuration();
    }

    @Test
    public void sortFamily() throws Exception {
        ISymbol name = config.exprFactory.symbol("MySort");
        INumeral arity = config.exprFactory.numeral(2);
        ISort.IFamily family = config.sortFactory.createSortFamily(name, arity);
        // A family is referenced by its bare identifier; the full
        // "(declare-sort name arity)" syntax is assembled by the declare-sort
        // command's own write(), never by printing an IFamily.
        Assert.assertEquals("MySort", family.toString());
    }

    @Test
    public void sortAbbreviation() throws Exception {
        ISymbol name = config.exprFactory.symbol("MyAbbrev");
        ISort.IParameter param = config.sortFactory.createSortParameter(config.exprFactory.symbol("T"));
        java.util.List<ISort.IParameter> params = java.util.Collections.singletonList(param);
        ISort.IAbbreviation abbrev = config.sortFactory.createSortAbbreviation(name, params, config.sortFactory.Bool());
        Assert.assertEquals("(MyAbbrev (T) Bool)", abbrev.toString());
    }

    @Test
    public void fcnSort() throws Exception {
        // Not real SMT-LIB syntax - function signatures are only ever written via
        // declare-fun's own separate argument-list/result-sort fields. This is purely
        // an internal diagnostic form (e.g. Utils.java's symbol-table error messages).
        ISort fcnSort = config.sortFactory.createFcnSort(
                new ISort[] { config.sortFactory.Bool(), config.sortFactory.Bool() },
                config.sortFactory.Bool());
        Assert.assertEquals("(Bool Bool) -> Bool", fcnSort.toString());
    }

    /** Parses a (logic ...) definition and confirms the printed form exactly reproduces
     * the input. Deliberately uses a single attribute: ILogic/ITheory keep attributes in a
     * {@code HashMap}, so with more than one attribute present, print order relative to the
     * source is not guaranteed. */
    @Test
    public void logicRoundTrip() throws Exception {
        String text = "(logic MyTestLogic :written-by \"Cesare Tinelli\")";
        ISource source = config.smtFactory.createSource(text, "logicRoundTrip");
        IParser parser = new org.smtlib.sexpr.Parser(config, source);
        ILogic logic = parser.parseLogic();
        Assert.assertNotNull(logic);
        StringWriter sw = new StringWriter();
        org.smtlib.sexpr.Printer.write(sw, logic);
        Assert.assertEquals(text, sw.toString());
    }

    /** Parses a (theory ...) definition and confirms the printed form exactly reproduces
     * the input. See {@link #logicRoundTrip()} for why only one attribute is used. */
    @Test
    public void theoryRoundTrip() throws Exception {
        String text = "(theory MyTestTheory :written-by \"Cesare Tinelli\")";
        ISource source = config.smtFactory.createSource(text, "theoryRoundTrip");
        IParser parser = new org.smtlib.sexpr.Parser(config, source);
        ITheory theory = parser.parseTheory();
        Assert.assertNotNull(theory);
        StringWriter sw = new StringWriter();
        org.smtlib.sexpr.Printer.write(sw, theory);
        Assert.assertEquals(text, sw.toString());
    }

    @Test
    public void errorResponse() throws Exception {
        IResponse.IError err = config.responseFactory.error("bad thing");
        Assert.assertEquals("(error \"bad thing\")", err.toString());
    }

    @Test
    public void assertionsResponse() throws Exception {
        List<IExpr> exprs = Collections.singletonList((IExpr) config.exprFactory.symbol("true"));
        IResponse.IAssertionsResponse r = config.responseFactory.get_assertions_response(exprs);
        String eol = System.getProperty("line.separator");
        Assert.assertEquals("(" + eol + "true" + eol + ")", r.toString());
    }

    @Test
    public void assignmentResponse() throws Exception {
        List<IResponse.IPair<ISymbol, Boolean>> pairs = Collections.singletonList(
                config.responseFactory.pair(config.exprFactory.symbol("x"), Boolean.TRUE));
        IResponse.IAssignmentResponse r = config.responseFactory.get_assignment_response(pairs);
        Assert.assertEquals("((x true))", r.toString());
    }

    @Test
    public void proofResponse() throws Exception {
        IResponse.IProofResponse r = config.responseFactory.get_proof_response();
        // Proofs are not yet implemented (Printer.visit(IProofResponse) is a placeholder).
        Assert.assertEquals("PROOF", r.toString());
    }

    @Test
    public void valueResponse() throws Exception {
        List<IResponse.IPair<IExpr, IExpr>> pairs = Collections.singletonList(
                config.responseFactory.pair((IExpr) config.exprFactory.symbol("x"), (IExpr) config.exprFactory.numeral(1)));
        IResponse.IValueResponse r = config.responseFactory.get_value_response(pairs);
        Assert.assertEquals("((x 1))", r.toString());
    }

    @Test
    public void unsatCoreResponse() throws Exception {
        List<ISymbol> names = Collections.singletonList(config.exprFactory.symbol("a"));
        IResponse.IUnsatCoreResponse r = config.responseFactory.get_unsat_core_response(names);
        Assert.assertEquals("(a )", r.toString());
    }

    @Test
    public void unsatAssumptionsResponse() throws Exception {
        List<ISymbol> names = Collections.singletonList(config.exprFactory.symbol("a"));
        IResponse.IUnsatAssumptionsResponse r = config.responseFactory.get_unsat_assumptions_response(names);
        Assert.assertEquals("(a )", r.toString());
    }

    @Test
    public void attributeListResponse() throws Exception {
        IAttribute<?> attr = config.exprFactory.attribute(
                config.exprFactory.keyword(":status"), config.exprFactory.symbol("sat"));
        IResponse.IAttributeList r = config.responseFactory.get_info_response(attr);
        Assert.assertEquals("(:status sat )", r.toString());
    }

    @Test
    public void sexprToken() throws Exception {
        Sexpr.Token<String> token = new Sexpr.Token<>("hello");
        Assert.assertEquals("hello", token.toString());
    }

    @Test
    public void sexprExpr() throws Exception {
        Sexpr.Expr wrapped = new Sexpr.Expr(config.exprFactory.symbol("wrapped"));
        Assert.assertEquals("wrapped", wrapped.toString());
    }
}
