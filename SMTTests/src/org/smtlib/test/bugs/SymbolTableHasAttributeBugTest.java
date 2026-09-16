package org.smtlib.test.bugs;

import java.util.Arrays;
import java.util.List;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.ISort;
import org.smtlib.ISort.IFcnSort;
import org.smtlib.SMT;
import org.smtlib.SymbolTable;
import org.smtlib.IExpr.ISymbol;

/**
 * Pins down SymbolTable.java:766's hasAttribute(Entry, String): it iterates
 * entry.attributes with no null check, while signature() (SymbolTable.java:583) correctly
 * guards the same nullable field three lines above it. Any plain (non-associative,
 * non-par-polymorphic) arity-2 entry has attributes == null -- exactly what
 * define-fun/declare-fun create (see Solver_test.define_fun / TypeChecker.checkFcnsRec,
 * both of which call {@code new SymbolTable.Entry(name, sort, null, null)}). Calling such a
 * function with 3+ arguments makes SymbolTable.lookup() try matchAssociative() on that
 * arity-2 candidate, and matchAssociative()'s first line is hasAttribute(entry,
 * ":left-assoc") -- an uncaught NullPointerException instead of a clean arity error.
 * <p>
 * This test asserts the correct behavior once hasAttribute() is fixed to guard a null
 * attributes list the way signature() does: matchAssociative() falls through to "does not
 * accept more than two arguments" (a NoMatch), which lookup() catches and turns into a plain
 * null result (no matching declaration) rather than propagating. It currently FAILS against
 * today's code (NullPointerException instead), documenting the bug.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/21">issue #21</a>.
 */
public class SymbolTableHasAttributeBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    SMT.Configuration config;
    SymbolTable symTable;

    @Before
    public void init() {
        config = new SMT.Configuration();
        symTable = new SymbolTable(config);
    }

    @Test
    public void threeArgCallToPlainTwoArgFunctionReturnsNoMatch() throws Exception {
        ISymbol f = config.exprFactory.symbol("f");
        ISort bool = config.sortFactory.Bool();
        IFcnSort fcnSort = config.sortFactory.createFcnSort(new ISort[] { bool, bool }, bool);
        // attributes == null, matching how define-fun/declare-fun build their entries --
        // not an :left-assoc/:right-assoc/:chainable/:pairwise declaration.
        SymbolTable.Entry entry = new SymbolTable.Entry(f, fcnSort, null, null);
        symTable.add(entry, true);

        List<ISort> threeArgs = Arrays.asList(bool, bool, bool);
        Assert.assertNull(symTable.lookup(f, threeArgs, null, null));
    }
}
