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
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IResponse;
import org.smtlib.ISort;
import org.smtlib.SMT;
import org.smtlib.SymbolTable;
import org.smtlib.TypeChecker;

/**
 * Covers TypeChecker.visit() overrides for node kinds that can never arise from parsing
 * SMT-LIB text, so no .tst-style script can reach them through the normal command
 * pipeline -- the same category {@link PrinterCoverageTest} already covers for
 * {@code org.smtlib.sexpr.Printer}, for the same three sort-definition kinds plus two
 * IExpr placeholder kinds specific to type-checking:
 * <ul>
 * <li>{@link ISort.IFamily}, {@link ISort.IAbbreviation}, {@link ISort.IFcnSort} are
 * symbol-table *definition* objects (see {@link ISort.IDefinition}), never the sort
 * *reference* (always an {@link ISort.IApplication}) that a parsed command's sort
 * expression actually produces -- see PrinterCoverageTest's identical rationale, and its
 * sortFamily()/sortAbbreviation()/fcnSort() tests for the same construction this reuses.
 * <li>{@link IExpr.IKeyword}: TypeChecker.visit(IKeyword) says directly in its own comment
 * that it should never be called -- a bare keyword can only appear as part of an attribute
 * or option, contexts TypeChecker never visits as a plain term.
 * <li>{@link IExpr.IError}: a parse-error placeholder node; a malformed sub-expression that
 * would produce one causes the surrounding command's parse to fail before type-checking is
 * ever reached at all.
 * </ul>
 * Each of these five overrides just records an "INTERNAL ERROR"-labeled response (or, for
 * IError, does nothing but return null) without inspecting anything solver- or
 * scope-dependent, so a bare SymbolTable with nothing declared is enough to call them
 * directly and confirm they behave as documented rather than throwing.
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

    private String soleErrorMessage(TypeChecker tc) {
        Assert.assertEquals(1, tc.result.size());
        List<IResponse> result = tc.result;
        return ((IResponse.IError) result.get(0)).errorMsg();
    }

    @Test
    public void keyword() throws Exception {
        IExpr.IKeyword kw = config.exprFactory.keyword(":anything");
        TypeChecker tc = new TypeChecker(symTable);
        Assert.assertNull(tc.visit(kw));
        Assert.assertTrue(soleErrorMessage(tc).contains("Did not expect to be type-checking a keyword"));
    }

    @Test
    public void error() throws Exception {
        IExpr.IError err = config.exprFactory.error("some parse error");
        TypeChecker tc = new TypeChecker(symTable);
        // Unlike the other four, visit(IError) records nothing -- it's a no-op placeholder.
        Assert.assertNull(tc.visit(err));
        Assert.assertTrue(tc.result.isEmpty());
    }

    @Test
    public void sortFamily() throws Exception {
        ISymbol name = config.exprFactory.symbol("MySort");
        INumeral arity = config.exprFactory.numeral(2);
        ISort.IFamily family = config.sortFactory.createSortFamily(name, arity, null);
        TypeChecker tc = new TypeChecker(symTable);
        Assert.assertNull(tc.visit(family));
        Assert.assertTrue(soleErrorMessage(tc).contains("unexpected type-checking of a ISort.IFamily"));
    }

    @Test
    public void sortAbbreviation() throws Exception {
        ISymbol name = config.exprFactory.symbol("MyAbbrev");
        ISort.IParameter param = config.sortFactory.createSortParameter(config.exprFactory.symbol("T"));
        List<ISort.IParameter> params = Collections.singletonList(param);
        ISort.IAbbreviation abbrev = config.sortFactory.createSortAbbreviation(name, params, config.sortFactory.Bool());
        TypeChecker tc = new TypeChecker(symTable);
        Assert.assertNull(tc.visit(abbrev));
        Assert.assertTrue(soleErrorMessage(tc).contains("unexpected type-checking of a ISort.IAbbreviation"));
    }

    @Test
    public void fcnSort() throws Exception {
        ISort.IFcnSort fcnSort = config.sortFactory.createFcnSort(
                new ISort[] { config.sortFactory.Bool(), config.sortFactory.Bool() },
                config.sortFactory.Bool());
        TypeChecker tc = new TypeChecker(symTable);
        Assert.assertNull(tc.visit(fcnSort));
        Assert.assertTrue(soleErrorMessage(tc).contains("unexpected type-checking of a ISort.IFcnSort"));
    }
}
