package org.smtlib.test.bugs;

import java.util.Collections;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.IExpr;
import org.smtlib.IParser;
import org.smtlib.ISource;
import org.smtlib.SMT;
import org.smtlib.logic.LRA;
import org.smtlib.logic.Logic;

/**
 * Pins down {@code LRA.isConst()} (LRA.java:21-33) and its duplicate {@code Logic.isRealConst()}
 * (Logic.java:155-169): both recognize a unary minus of a literal numeral/decimal, and a
 * division of two numerals, as linear-arithmetic constants -- but neither recursed when a unary
 * minus wraps a division, e.g. {@code (- (/ 1 2))}: the minus branch only checked whether its
 * single argument was itself a bare {@code INumeral}/{@code IDecimal}, so a division nested one
 * level inside fell through to {@code return false}.
 * <p>
 * This under-recognizes valid linear terms: {@code (* (- (/ 1 2)) x)} is linear (constant
 * coefficient -1/2 times a free variable) but {@code isConst()} said the coefficient wasn't a
 * constant, so {@code LRA.validExpression()} (and the AUFLIRA-family callers of
 * {@code Logic.isRealConst()} via {@code isLinearReal()}) would incorrectly reject it as
 * nonlinear.
 * <p>
 * Fixed by recursing (calling {@code isConst}/{@code isRealConst} on the wrapped argument)
 * instead of only checking for a literal numeral/decimal.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/45">issue #45</a>.
 */
public class LinearConstUnaryMinusOfDivisionBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    private IExpr parse(SMT.Configuration config, String text) throws Exception {
        ISource source = config.smtFactory.createSource(text, null);
        IParser p = new org.smtlib.sexpr.Parser(config, source);
        return p.parseExpr();
    }

    @Test
    public void lraIsConstRecognizesUnaryMinusOfDivision() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        LRA logic = new LRA(config, config.exprFactory.symbol("QF_LRA"), Collections.emptyList());

        IExpr expr = parse(config, "(- (/ 1 2))");
        Assert.assertTrue("(- (/ 1 2)) is a linear-arithmetic constant", logic.isConst(expr));
    }

    @Test
    public void logicIsRealConstRecognizesUnaryMinusOfDivision() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        // AUFLIRA is a concrete Logic subclass that inherits isRealConst() unmodified.
        Logic logic = new org.smtlib.logic.AUFLIRA(config, config.exprFactory.symbol("AUFLIRA"), Collections.emptyList());

        IExpr expr = parse(config, "(- (/ 1 2))");
        Assert.assertTrue("(- (/ 1 2)) is a linear-arithmetic constant", logic.isRealConst(expr));
    }

    @Test
    public void linearTermWithNegatedDivisionCoefficientIsAccepted() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        LRA logic = new LRA(config, config.exprFactory.symbol("QF_LRA"), Collections.emptyList());

        // (* (- (/ 1 2)) x) -- a constant coefficient of -1/2 times a free variable x --
        // is a linear term and must not be rejected as nonlinear.
        IExpr expr = parse(config, "(* (- (/ 1 2)) x)");
        logic.validExpression(expr); // must not throw
    }
}
