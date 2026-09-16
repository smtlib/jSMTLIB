package org.smtlib.test.bugs;

import java.io.StringWriter;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.IExpr;
import org.smtlib.IExpr.IDeclaration;
import org.smtlib.IExpr.IForall;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.ISort;
import org.smtlib.SMT;

/**
 * Pins down (and confirms the fix for) {@code solvers.Printer.visit(IForall)}/
 * {@code visit(IExists)}: the Bool-sorted-quantifier-parameter workaround (rewriting
 * {@code (forall ((b Bool)) body)} to {@code (and (let ((b true)) body) (let ((b false))
 * body))}, since not every solver this Printer targets accepts a Bool-sorted quantified
 * variable) only fired when the quantifier had exactly one parameter. A quantifier with a
 * Bool-sorted parameter *and* other parameters -- e.g.
 * {@code (forall ((b Bool) (x Int)) body)} -- fell through to standard printing, emitting
 * the very "Bool" quantified variable the workaround exists to avoid.
 * <p>
 * Fixed by unfolding one Bool-sorted parameter at a time (recursing on the rest), so any
 * number of Bool-sorted parameters mixed with any number of non-Bool ones are all unfolded,
 * with an ordinary quantifier printed over whatever non-Bool parameters remain in each case.
 * <p>
 * Three tests: forall and exists each with one Bool parameter alongside one non-Bool
 * parameter (confirming the mixed case now unfolds, and reduces to an ordinary quantifier
 * over just the remaining non-Bool parameter in each branch), and forall with two Bool
 * parameters and nothing else (confirming the recursion correctly produces a full 4-way
 * case split with no quantifier left at all, matching the original single-parameter case's
 * own no-quantifier base case).
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/63">issue #63</a>.
 */
public class PrinterMultiParamBoolQuantifierBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    @Test
    public void forallWithBoolAndNonBoolParametersUnfoldsTheBoolOne() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        ISymbol bSym = config.exprFactory.symbol("b");
        ISymbol xSym = config.exprFactory.symbol("x");
        ISort boolSort = config.sortFactory.Bool();
        ISort intSort = config.sortFactory.createSortExpression(config.exprFactory.symbol("Int"), new ISort[0]);
        IDeclaration bDecl = config.exprFactory.declaration(bSym, boolSort);
        IDeclaration xDecl = config.exprFactory.declaration(xSym, intSort);
        List<IDeclaration> params = Arrays.asList(bDecl, xDecl);
        IExpr body = bSym; // simplest possible Bool-sorted body: just "b" itself
        IForall forall = config.exprFactory.forall(params, body);

        StringWriter sw = new StringWriter();
        org.smtlib.solvers.Printer.write(sw, forall);
        String printed = sw.toString();

        // The Bool-sorted parameter must never appear as a quantified sort in the output --
        // that's exactly what the workaround exists to avoid.
        Assert.assertFalse("printed output must not quantify over a Bool sort: " + printed,
                printed.contains("Bool"));
        // forall with a Bool-sorted parameter unfolds via "and"; the non-Bool parameter (x)
        // still needs an ordinary quantifier in each of the two (true/false) branches.
        Assert.assertTrue("expected an \"and\"-combined case split: " + printed,
                printed.startsWith("(and "));
        int forallCount = printed.split("\\(forall \\(", -1).length - 1;
        Assert.assertEquals("expected one nested forall (over x) per Bool branch: " + printed,
                2, forallCount);
    }

    @Test
    public void existsWithBoolAndNonBoolParametersUnfoldsTheBoolOne() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        ISymbol bSym = config.exprFactory.symbol("b");
        ISymbol xSym = config.exprFactory.symbol("x");
        ISort boolSort = config.sortFactory.Bool();
        ISort intSort = config.sortFactory.createSortExpression(config.exprFactory.symbol("Int"), new ISort[0]);
        IDeclaration bDecl = config.exprFactory.declaration(bSym, boolSort);
        IDeclaration xDecl = config.exprFactory.declaration(xSym, intSort);
        List<IDeclaration> params = Arrays.asList(bDecl, xDecl);
        IExpr body = bSym;
        IExpr.IExists exists = config.exprFactory.exists(params, body);

        StringWriter sw = new StringWriter();
        org.smtlib.solvers.Printer.write(sw, exists);
        String printed = sw.toString();

        Assert.assertFalse("printed output must not quantify over a Bool sort: " + printed,
                printed.contains("Bool"));
        Assert.assertTrue("expected an \"or\"-combined case split: " + printed,
                printed.startsWith("(or "));
        int existsCount = printed.split("\\(exists \\(", -1).length - 1;
        Assert.assertEquals("expected one nested exists (over x) per Bool branch: " + printed,
                2, existsCount);
    }

    /** Two Bool-sorted parameters should unfold into a 4-way case split (one branch per
     *  combination of true/false for each), with no wrapping quantifier left at all once
     *  every parameter has been unfolded (matching the original single-parameter case's own
     *  base case, which prints no quantifier around the bare body either). */
    @Test
    public void forallWithTwoBoolParametersUnfoldsBoth() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        ISymbol b1 = config.exprFactory.symbol("b1");
        ISymbol b2 = config.exprFactory.symbol("b2");
        ISort boolSort = config.sortFactory.Bool();
        IDeclaration b1Decl = config.exprFactory.declaration(b1, boolSort);
        IDeclaration b2Decl = config.exprFactory.declaration(b2, boolSort);
        List<IDeclaration> params = Arrays.asList(b1Decl, b2Decl);
        IExpr body = b1;
        IForall forall = config.exprFactory.forall(params, body);

        StringWriter sw = new StringWriter();
        org.smtlib.solvers.Printer.write(sw, forall);
        String printed = sw.toString();

        Assert.assertFalse("printed output must not quantify over a Bool sort: " + printed,
                printed.contains("Bool"));
        Assert.assertFalse("no quantifier should remain once every parameter is unfolded: " + printed,
                printed.contains("forall") || printed.contains("exists"));
        // A 4-way case split: one outer "and" combining the b1=true/b1=false branches, and
        // one "and" inside each of those two branches combining b2=true/b2=false.
        int andCount = printed.split("\\(and ", -1).length - 1;
        Assert.assertEquals("expected three \"and\" combiners (outer + one per b1 branch) for a 4-way case split: " + printed,
                3, andCount);
        int bodyCount = printed.split("b1\\)", -1).length - 1;
        Assert.assertEquals("expected the body to appear once per leaf of the 4-way case split: " + printed,
                4, bodyCount);
    }
}
