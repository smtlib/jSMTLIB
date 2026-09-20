package org.smtlib.test.bugs;

import java.util.Collections;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.ISort;
import org.smtlib.SMT;

/**
 * Pins down impl/Sort.java's {@code Abbreviation.equals()}/{@code hashCode()}: both
 * considered only {@code identifier()}, ignoring {@code parameters()}/{@code
 * sortExpression()} -- flagged by an adjacent {@code // FIXME - equals and hasCode should
 * consider parameters and sort expression} that {@code hashCode()}'s own comment then
 * contradicted ("The identifier is supposed to be unique across all in-scope
 * definitions"). Two abbreviations sharing a name but defined with different parameter
 * lists or defining expressions compared equal before this fix.
 * <p>
 * Asserts the correct behavior: two {@code IAbbreviation}s with the same identifier but a
 * different defining sort expression are NOT equal, and (as a byproduct of the fix) don't
 * share a hash code either.
 */
public class SortAbbreviationEqualityBugTest {

    @Test
    public void differentSortExpressionIsNotEqual() {
        SMT.Configuration config = new SMT.Configuration();
        ISymbol name = config.exprFactory.symbol("MyAbbrev");
        ISort.IParameter param = config.sortFactory.createSortParameter(config.exprFactory.symbol("T"));
        List<ISort.IParameter> params = Collections.singletonList(param);

        // A bare Application (e.g. an "Int" sort built via createSortExpression) needs a
        // symbol-table-resolved definition() before it can be equals()-compared at all
        // (Application.equals() calls expand(), which NPEs without one) -- a Parameter is
        // self-contained (expand() just returns itself), so it's a simpler way to get a
        // second, genuinely different ISort here without dragging in a symbol table.
        ISort otherSort = config.sortFactory.createSortParameter(config.exprFactory.symbol("SomeOtherSort"));
        ISort.IAbbreviation boolAbbrev = config.sortFactory.createSortAbbreviation(name, params, config.sortFactory.Bool());
        ISort.IAbbreviation intAbbrev = config.sortFactory.createSortAbbreviation(name, params, otherSort);

        Assert.assertNotEquals("same name but different defining sort expression must not be equal",
                boolAbbrev, intAbbrev);
        Assert.assertNotEquals("different defining sort expression should (in practice) hash differently",
                boolAbbrev.hashCode(), intAbbrev.hashCode());
    }

    @Test
    public void differentParametersIsNotEqual() {
        SMT.Configuration config = new SMT.Configuration();
        ISymbol name = config.exprFactory.symbol("MyAbbrev");
        List<ISort.IParameter> oneParam = Collections.singletonList(
                config.sortFactory.createSortParameter(config.exprFactory.symbol("T")));
        List<ISort.IParameter> twoParams = java.util.Arrays.asList(
                config.sortFactory.createSortParameter(config.exprFactory.symbol("T")),
                config.sortFactory.createSortParameter(config.exprFactory.symbol("U")));

        ISort.IAbbreviation oneParamAbbrev = config.sortFactory.createSortAbbreviation(name, oneParam, config.sortFactory.Bool());
        ISort.IAbbreviation twoParamAbbrev = config.sortFactory.createSortAbbreviation(name, twoParams, config.sortFactory.Bool());

        Assert.assertNotEquals("same name but a different parameter list must not be equal",
                oneParamAbbrev, twoParamAbbrev);
    }

    @Test
    public void sameEverythingIsStillEqual() {
        SMT.Configuration config = new SMT.Configuration();
        ISymbol name = config.exprFactory.symbol("MyAbbrev");
        ISort.IParameter param = config.sortFactory.createSortParameter(config.exprFactory.symbol("T"));
        List<ISort.IParameter> params = Collections.singletonList(param);

        ISort.IAbbreviation a = config.sortFactory.createSortAbbreviation(name, params, config.sortFactory.Bool());
        ISort.IAbbreviation b = config.sortFactory.createSortAbbreviation(name, params, config.sortFactory.Bool());

        Assert.assertEquals("identical identifier/parameters/sortExpression must still be equal", a, b);
        Assert.assertEquals("identical identifier/parameters/sortExpression must still hash equal", a.hashCode(), b.hashCode());
    }
}
