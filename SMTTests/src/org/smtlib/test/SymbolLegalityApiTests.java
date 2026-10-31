package org.smtlib.test;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.smtlib.IExpr;
import org.smtlib.IExpr.IDeclaration;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IResponse;
import org.smtlib.SMT;
import org.smtlib.SMT.Configuration.SMTLIB;
import org.smtlib.SymbolTable;
import org.smtlib.TypeChecker;
import org.smtlib.impl.SMTExpr;
import org.smtlib.impl.Sort;

/** Legality checks that only API-built nodes can reach: text is rejected by the parser first.
 *  Covers SMT.Configuration.isReservedWord/isOKSymbol, the type checker's reports of illegal
 *  symbols and empty binder lists, and printing of the parenthesized forms the parser keeps. */
public class SymbolLegalityApiTests {

    SMT.Configuration config;
    IExpr.IFactory f;

    @Before
    public void init() {
        config = new SMT.Configuration();
        f = config.exprFactory;
    }

    /** Type checks e directly (no logic is set, so TypeChecker.check's logic check can't run) */
    private List<IResponse> check(IExpr e) throws Exception {
        TypeChecker tc = new TypeChecker(new SymbolTable(config));
        e.accept(tc);
        return tc.result;
    }

    private String soleError(List<IResponse> result) {
        Assert.assertEquals(1, result.size());
        return ((IResponse.IError) result.get(0)).errorMsg();
    }

    @Test
    public void reservedWordsDependOnVersion() {
        Assert.assertTrue(config.isReservedWord("lambda"));
        Assert.assertTrue(config.isReservedWord("HEXADECIMAL"));
        config.smtlib = SMTLIB.V26;
        Assert.assertFalse(config.isReservedWord("lambda"));
        Assert.assertTrue(config.isReservedWord("match"));
        config.smtlib = SMTLIB.V25;
        Assert.assertFalse(config.isReservedWord("match"));
        Assert.assertTrue(config.isReservedWord("BINARY"));
        config.smtlib = SMTLIB.V20;
        Assert.assertFalse(config.isReservedWord("BINARY"));
        Assert.assertFalse(config.isReservedWord("echo"));
        Assert.assertTrue(config.isReservedWord("par"));
        Assert.assertTrue(config.isReservedWord("assert"));
        config.relax = true;
        Assert.assertFalse(config.isReservedWord("assert"));
        Assert.assertTrue(config.isReservedWord("par"));
    }

    @Test
    public void okSymbols() {
        Assert.assertTrue(config.isOKSymbol("a b"));
        Assert.assertTrue(config.isOKSymbol(""));
        Assert.assertTrue(config.isOKSymbol("é"));
        Assert.assertFalse(config.isOKSymbol("a|b"));
        Assert.assertFalse(config.isOKSymbol("a\\b"));
        Assert.assertFalse(config.isOKSymbol("a\u0001b"));
        Assert.assertFalse(config.isOKSymbol("let"));
        config.smtlib = SMTLIB.V20;
        Assert.assertFalse(config.isOKSymbol("é"));
    }

    @Test
    public void illegalSymbolTerm() throws Exception {
        Assert.assertEquals("Not a legal SMT-LIB symbol: \"a|b\"", soleError(check(f.symbol("a|b"))));
        Assert.assertEquals("A reserved word may not be used as a symbol here: let", soleError(check(f.symbol("let"))));
    }

    @Test
    public void reservedAttributeValue() throws Exception {
        IExpr e = f.attributedExpr(f.symbol("true"), f.keyword(":named"), f.symbol("forall"));
        Assert.assertEquals("A reserved word may not be used as a symbol here: forall", soleError(check(e)));
    }

    @Test
    public void emptyBinders() throws Exception {
        List<IDeclaration> none = new LinkedList<>();
        Assert.assertEquals("At least one variable must be bound by forall", soleError(check(f.forall(none, f.symbol("true")))));
        Assert.assertEquals("At least one variable must be bound by exists", soleError(check(f.exists(none, f.symbol("true")))));
        Assert.assertEquals("At least one variable must be bound by let",
                soleError(check(f.let(new LinkedList<IExpr.IBinding>(), f.symbol("true")))));
    }

    @Test
    public void reservedBoundVariable() throws Exception {
        List<IDeclaration> decls = Collections.singletonList(f.declaration(f.symbol("match"), config.sortFactory.Bool()));
        // The first error; with no logic loaded, Bool is reported as undeclared too
        List<IResponse> result = check(f.forall(decls, f.symbol("true")));
        Assert.assertEquals("A reserved word may not be used as a symbol here: match",
                ((IResponse.IError) result.get(0)).errorMsg());
    }

    /** The first error; with no logic loaded, the literal's sort is reported as unknown too */
    private String firstError(List<IResponse> result) {
        return ((IResponse.IError) result.get(0)).errorMsg();
    }

    @Test
    public void negativeLiterals() throws Exception {
        Assert.assertEquals("A numeral may not be negative: -5", firstError(check(f.numeral("-5"))));
        Assert.assertEquals("A decimal may not be negative: -1.5", firstError(check(f.decimal("-1.5"))));
    }

    @Test
    public void decimalsPrintWithPoint() {
        Assert.assertEquals("5.0", config.defaultPrinter.toString(f.decimal("5")));
        Assert.assertEquals("5.00", config.defaultPrinter.toString(f.decimal("5.00")));
        Assert.assertEquals("5000.0", config.defaultPrinter.toString(f.decimal("5E3")));
    }

    @Test
    public void okStrings() {
        Assert.assertTrue(config.isOKString("a \"b\" \\ c\t\n"));
        Assert.assertTrue(config.isOKString("é"));
        Assert.assertFalse(config.isOKString("a\u0001b"));
        config.smtlib = SMTLIB.V20;
        Assert.assertFalse(config.isOKString("é"));
    }

    @Test
    public void illegalStringLiteral() throws Exception {
        Assert.assertEquals("A string literal may not contain the character with code 7",
                firstError(check(f.unquotedString("a\u0007b"))));
    }

    @Test
    public void emptyAnnotation() throws Exception {
        // p is undeclared (no logic), which is reported first
        IExpr e = f.attributedExpr(f.symbol("p"), new LinkedList<IExpr.IAttribute<?>>());
        List<IResponse> result = check(e);
        Assert.assertEquals(2, result.size());
        Assert.assertEquals("An annotated term must have at least one attribute", ((IResponse.IError) result.get(1)).errorMsg());
    }

    @Test
    public void barsStrippedOnlyInPairs() throws Exception {
        Assert.assertEquals("ab", f.symbol("|ab|").value());
        Assert.assertEquals("", f.symbol("||").value());
        Assert.assertEquals("|", f.symbol("|").value());
        Assert.assertEquals("|ab", f.symbol("|ab").value());
        Assert.assertEquals("Not a legal SMT-LIB symbol: \"|ab\"", soleError(check(f.symbol("|ab"))));
    }

    @Test
    public void parenthesizedFormsPrint() {
        ISymbol c = f.symbol("c");
        Assert.assertEquals("c", f.pattern(c, new LinkedList<ISymbol>()).toString());
        Assert.assertEquals("(c)", new SMTExpr.Pattern(c, new LinkedList<ISymbol>(), true).toString());
        Assert.assertEquals("S", new Sort.Application(f.symbol("S"), new LinkedList<>()).toString());
        Assert.assertEquals("(S)", new Sort.Application(f.symbol("S"), new LinkedList<>(), true).toString());
    }
}
