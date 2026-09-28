package org.smtlib.test.bugs;

import java.io.StringWriter;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.ICommand;
import org.smtlib.IExpr;
import org.smtlib.IExpr.IDeclaration;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IParser;
import org.smtlib.IResponse;
import org.smtlib.ISort;
import org.smtlib.ISource;
import org.smtlib.SMT;
import org.smtlib.solvers.Solver_test;

/**
 * Pins down (and confirms the fix for) {@code impl.Factory.forall(params, e, patterns)} and
 * {@code exists(params, e, patterns)}: each trigger was stored directly as the value of its
 * {@code :pattern} attribute, so a trigger {@code (f x)} printed as {@code :pattern (f x)}.
 * In SMT-LIB a pattern is a parenthesized list of terms, so the correct text is
 * {@code :pattern ((f x))}. z3 happened to accept the malformed form; cvc5 rejects it
 * ("Pattern must be a list of fully-applied terms"), and jSMTLIB's own TypeChecker rejected
 * it too ("Expected a sequence after :pattern"), since the parser represents a parsed
 * {@code :pattern} value as an {@code ISexpr.ISeq}.
 * <p>
 * Fixed by making the value of each such attribute an {@link IExpr.IPatternTerms} (a list of
 * terms) that prints as {@code ( t1 ... tn )} and that the TypeChecker accepts. The parser now
 * builds the same representation for a {@code :pattern} inside an annotated term.
 */
public class FactoryPatternParenthesesBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    /** Builds (forall ((x Int)) (! (= (f x) x) :pattern ((f x)))) through the factory. */
    private IExpr forallWithTrigger(SMT.Configuration config) {
        IExpr.IFactory f = config.exprFactory;
        ISymbol x = f.symbol("x");
        ISort intSort = config.sortFactory.createSortExpression(f.symbol("Int"), new ISort[0]);
        List<IDeclaration> params = Arrays.asList(f.declaration(x, intSort));
        IExpr fx = f.fcn(f.symbol("f"), x);
        return f.forall(params, f.fcn(f.symbol("="), fx, x), Arrays.asList(fx));
    }

    private String print(SMT.Configuration config, IExpr e) throws Exception {
        StringWriter sw = new StringWriter();
        org.smtlib.sexpr.Printer.write(config, sw, e);
        return sw.toString();
    }

    private IResponse run(SMT.Configuration config, Solver_test solver, String command) throws Exception {
        ISource source = config.smtFactory.createSource(command, null);
        IParser p = config.smtFactory.createParser(config, source);
        ICommand c = p.parseCommand();
        Assert.assertNotNull("failed to parse: " + command, c);
        return c.execute(solver);
    }

    @Test
    public void forallTriggerIsPrintedAsAListOfTerms() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        String printed = print(config, forallWithTrigger(config));
        Assert.assertTrue("expected ':pattern ((f x))' in: " + printed, printed.contains(":pattern ((f x))"));
    }

    @Test
    public void existsTriggerIsPrintedAsAListOfTerms() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        IExpr.IFactory f = config.exprFactory;
        ISymbol x = f.symbol("x");
        ISort intSort = config.sortFactory.createSortExpression(f.symbol("Int"), new ISort[0]);
        IExpr fx = f.fcn(f.symbol("f"), x);
        IExpr e = f.exists(Arrays.asList(f.declaration(x, intSort)), f.fcn(f.symbol("="), fx, x), Arrays.asList(fx));
        String printed = print(config, e);
        Assert.assertTrue("expected ':pattern ((f x))' in: " + printed, printed.contains(":pattern ((f x))"));
    }

    @Test
    public void eachTriggerIsItsOwnPattern() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        IExpr.IFactory f = config.exprFactory;
        ISymbol x = f.symbol("x");
        ISort intSort = config.sortFactory.createSortExpression(f.symbol("Int"), new ISort[0]);
        IExpr fx = f.fcn(f.symbol("f"), x);
        IExpr gx = f.fcn(f.symbol("g"), x);
        IExpr e = f.forall(Arrays.asList(f.declaration(x, intSort)), f.fcn(f.symbol("="), fx, gx), Arrays.asList(fx, gx));
        String printed = print(config, e);
        Assert.assertTrue("expected two single-term patterns in: " + printed,
                printed.contains(":pattern ((f x)) :pattern ((g x))"));
    }

    @Test
    public void multiPatternIsPrintedAsOneList() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        IExpr.IFactory f = config.exprFactory;
        IExpr fx = f.fcn(f.symbol("f"), f.symbol("x"));
        IExpr gy = f.fcn(f.symbol("g"), f.symbol("y"));
        IExpr e = f.attributedExpr(f.symbol("b"), f.keyword(":pattern"), f.patternTerms(Arrays.asList(fx, gy)));
        Assert.assertEquals("(! b :pattern ((f x) (g y)))", print(config, e));
    }

    @Test
    public void factoryBuiltTriggerTypeChecks() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        Solver_test solver = new Solver_test(config, "test");
        Assert.assertFalse(solver.start().isError());
        Assert.assertFalse(run(config, solver, "(set-logic ALL)").isError());
        Assert.assertFalse(run(config, solver, "(declare-fun f (Int) Int)").isError());
        IResponse r = solver.assertExpr(forallWithTrigger(config));
        Assert.assertFalse("factory-built :pattern must type-check: " + r, r.isError());
    }

    @Test
    public void printedTriggerParsesAndTypeChecks() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        Solver_test solver = new Solver_test(config, "test");
        Assert.assertFalse(solver.start().isError());
        Assert.assertFalse(run(config, solver, "(set-logic ALL)").isError());
        Assert.assertFalse(run(config, solver, "(declare-fun f (Int) Int)").isError());
        IResponse r = run(config, solver, "(assert " + print(config, forallWithTrigger(config)) + ")");
        Assert.assertFalse("printed :pattern must re-parse and type-check: " + r, r.isError());
    }

    private IExpr parseExpr(SMT.Configuration config, String text) throws Exception {
        ISource source = config.smtFactory.createSource(text, null);
        return new org.smtlib.sexpr.Parser(config, source).parseExpr();
    }

    @Test
    public void parsedPatternIsAListOfTerms() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        String text = "(! (f x) :pattern ((f x) (g x)))";
        IExpr e = parseExpr(config, text);
        Assert.assertTrue(e instanceof IExpr.IAttributedExpr);
        Object v = ((IExpr.IAttributedExpr)e).attributes().get(0).attrValue();
        Assert.assertTrue("expected an IPatternTerms, got " + v.getClass(), v instanceof IExpr.IPatternTerms);
        Assert.assertEquals(2, ((IExpr.IPatternTerms)v).terms().size());
        Assert.assertEquals(text, print(config, e)); // parse/print round trip is exact
    }

    /** Runs set-logic, declares f, and asserts the given formula; returns the assert's response. */
    private IResponse assertWithF(String formula) throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        Solver_test solver = new Solver_test(config, "test");
        Assert.assertFalse(solver.start().isError());
        Assert.assertFalse(run(config, solver, "(set-logic ALL)").isError());
        Assert.assertFalse(run(config, solver, "(declare-fun f (Int) Int)").isError());
        return run(config, solver, "(assert " + formula + ")");
    }

    @Test
    public void emptyPatternIsAllowed() throws Exception { // SMT-LIB 2.7, Section 3.6.5
        SMT.Configuration config = new SMT.Configuration();
        IExpr e = parseExpr(config, "(! (f x) :pattern ())");
        Object v = ((IExpr.IAttributedExpr)e).attributes().get(0).attrValue();
        Assert.assertTrue(v instanceof IExpr.IPatternTerms);
        Assert.assertEquals(0, ((IExpr.IPatternTerms)v).terms().size());
        Assert.assertEquals("(! (f x) :pattern ())", print(config, e));
        IResponse r = assertWithF("(forall ((x Int)) (! (= (f x) x) :pattern ()))");
        Assert.assertFalse("an empty :pattern must be accepted: " + r, r.isError());
    }

    @Test
    public void patternOutsideAQuantifierBodyIsRejected() throws Exception {
        IResponse r = assertWithF("(= (! (f 0) :pattern ((f 0))) 0)");
        Assert.assertTrue("a :pattern not on a quantifier body must be rejected: " + r, r.isError());
        r = assertWithF("(forall ((x Int)) (= (! (f x) :pattern ((f x))) x))");
        Assert.assertTrue("a :pattern on a subterm of the body must be rejected: " + r, r.isError());
    }

    @Test
    public void patternTermWithABinderIsRejected() throws Exception {
        IResponse r = assertWithF("(forall ((x Int)) (! (= (f x) x) :pattern ((f (let ((y x)) y)))))");
        Assert.assertTrue("a pattern term containing a binder must be rejected: " + r, r.isError());
    }

    @Test
    public void patternTermWithAnAnnotationIsRejected() throws Exception {
        IResponse r = assertWithF("(forall ((x Int)) (! (= (f x) x) :pattern ((f (! x :named n)))))");
        Assert.assertTrue("a pattern term containing an annotation must be rejected: " + r, r.isError());
    }

    @Test
    public void nonListPatternIsStillReportedByTheTypeChecker() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        Solver_test solver = new Solver_test(config, "test");
        Assert.assertFalse(solver.start().isError());
        Assert.assertFalse(run(config, solver, "(set-logic ALL)").isError());
        Assert.assertFalse(run(config, solver, "(declare-fun f (Int) Int)").isError());
        IResponse r = run(config, solver, "(assert (forall ((x Int)) (! (= (f x) x) :pattern f)))");
        Assert.assertTrue("a non-list :pattern value must be rejected: " + r, r.isError());
    }
}
