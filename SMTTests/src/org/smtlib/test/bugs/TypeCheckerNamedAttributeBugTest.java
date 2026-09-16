package org.smtlib.test.bugs;

import java.util.Arrays;
import java.util.List;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.IExpr;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IAttributedExpr;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IResponse;
import org.smtlib.SMT;
import org.smtlib.SymbolTable;
import org.smtlib.TypeChecker;

/**
 * Pins down TypeChecker.java:1156-1161's handling of a malformed {@code :named} attribute:
 * visit(IAttributedExpr) records an error when the attribute's value is not an ISymbol, but
 * has no continue/return -- it falls through to an unconditional {@code (ISymbol)v} cast,
 * throwing ClassCastException (or, when the value is missing entirely, NullPointerException
 * once the resulting null-keyed entry collides with another one).
 * <p>
 * Both tests below call TypeChecker.visit(IAttributedExpr) directly (as
 * TypeCheckerCoverageTest does for its own node kinds) rather than going through
 * TypeChecker.checkAssertion(), whose blanket {@code catch (Exception e)} would otherwise
 * swallow the exception into a second, discarded "INTERNAL ERROR" response (assertExpr()
 * returns only errs.get(0)) -- masking the defect rather than exercising it directly.
 * <p>
 * Both tests assert the clean, single-error outcome that TypeChecker.java:1156-1161 should
 * produce once fixed (continue/return after recording the "Expected a symbol after :named"
 * error, instead of falling through to the cast) -- so both currently FAIL against today's
 * code, documenting the bug.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/20">issue #20</a>.
 */
public class TypeCheckerNamedAttributeBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    SMT.Configuration config;
    SymbolTable symTable;

    @Before
    public void init() {
        config = new SMT.Configuration();
        symTable = new SymbolTable(config);
    }

    private static String errorMessage(IResponse r) {
        return ((IResponse.IError) r).errorMsg();
    }

    /** (assert (! true :named 5)) -- the attribute value is an INumeral, not an ISymbol.
     *  Today: throws ClassCastException while casting the INumeral to ISymbol. */
    @Test
    public void namedValueNotASymbolRecordsCleanError() throws Exception {
        IKeyword named = config.exprFactory.keyword(":named");
        INumeral five = config.exprFactory.numeral(5L);
        IExpr base = config.exprFactory.symbol("true");
        IAttributedExpr ae = config.exprFactory.attributedExpr(base, named, five);
        TypeChecker tc = new TypeChecker(symTable);

        Assert.assertNull(tc.visit(ae));
        Assert.assertEquals(1, tc.result.size());
        Assert.assertTrue(errorMessage(tc.result.get(0)).contains("Expected a symbol after :named"));
    }

    /** Two bare (valueless) :named attributes on the same expression. Today: the first
     *  attribute's entry (keyed by a null ISymbol, from casting the null attrValue) is added
     *  successfully; the second collides with it, and the "already defined" error message
     *  calls v.toString() on the same null value, throwing NullPointerException. Once fixed,
     *  neither bare attribute should ever reach entry creation, so both should independently
     *  report the same clean "Expected a symbol after :named" error with no collision. */
    @Test
    public void twoBareNamedAttributesBothRecordCleanErrors() throws Exception {
        IKeyword named = config.exprFactory.keyword(":named");
        IAttribute<?> attr1 = config.exprFactory.attribute(named);
        IAttribute<?> attr2 = config.exprFactory.attribute(named);
        IExpr base = config.exprFactory.symbol("true");
        List<IAttribute<?>> attrs = Arrays.asList(attr1, attr2);
        IAttributedExpr ae = config.exprFactory.attributedExpr(base, attrs);
        TypeChecker tc = new TypeChecker(symTable);

        Assert.assertNull(tc.visit(ae));
        Assert.assertEquals(2, tc.result.size());
        Assert.assertTrue(errorMessage(tc.result.get(0)).contains("Expected a symbol after :named"));
        Assert.assertTrue(errorMessage(tc.result.get(1)).contains("Expected a symbol after :named"));
    }
}
