package org.smtlib.test.TO_BE_FIXED;

import java.util.Collections;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.ISort;
import org.smtlib.ISort.IAbbreviation;
import org.smtlib.ISort.IApplication;
import org.smtlib.ISort.IFamily;
import org.smtlib.SMT;

/**
 * Pins down impl/Sort.java's {@code Application.equals()} (around line 246) vs.
 * {@code hashCode()} (around line 339): {@code equals()} expands sort abbreviations before
 * comparing ({@code expand().equalsNoExpand(...)}), so a user-defined alias and its literal
 * expansion are equal -- but {@code hashCode()} is computed directly from the unexpanded
 * sort ID and parameters. A textbook equals/hashCode contract violation: two objects that are
 * {@code .equals()} need not have the same {@code .hashCode()}.
 * <p>
 * Built directly via the sort factory (an abbreviation "MyAlias" for a 0-ary family "Base",
 * both self-contained -- {@code IApplication.expand()} only requires {@code definition()} to
 * have been set, not a full symbol table/type-checking pass), rather than through
 * define-sort/declare-fun and a real parse.
 * <p>
 * Not currently exploited (no existing {@code HashSet<ISort>}/{@code HashMap<ISort,...>} was
 * found in the codebase), but silently breaks the moment any future caller puts {@code ISort}
 * objects in a hash-based collection for deduplication or caching.
 * <p>
 * Asserts the correct behavior (equal hash codes for equal sorts). This currently FAILS
 * against today's code, documenting the bug.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/70">issue #70</a>.
 */
public class SortEqualsHashCodeBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    @Test
    public void aliasAndItsExpansionHaveEqualHashCodes() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        ISymbol baseName = config.exprFactory.symbol("Base");
        INumeral zero = config.exprFactory.numeral(0L);

        // "Base": a plain 0-ary sort family (e.g. playing the role of a concrete sort like Int).
        IFamily baseFamily = config.sortFactory.createSortFamily(baseName, zero, null);
        IApplication baseApp = config.sortFactory.createSortExpression(baseName, new ISort[0]);
        baseApp.definition(baseFamily);

        // "MyAlias": a parameterless abbreviation for Base (as define-sort would create).
        ISymbol aliasName = config.exprFactory.symbol("MyAlias");
        IAbbreviation aliasAbbrev = config.sortFactory.createSortAbbreviation(
                aliasName, Collections.emptyList(), baseApp);
        IApplication aliasApp = config.sortFactory.createSortExpression(aliasName, new ISort[0]);
        aliasApp.definition(aliasAbbrev);

        // The alias and its expansion are equal...
        Assert.assertEquals(baseApp, aliasApp);
        // ...so, per the equals/hashCode contract, they must have equal hash codes too.
        Assert.assertEquals(baseApp.hashCode(), aliasApp.hashCode());
    }
}
