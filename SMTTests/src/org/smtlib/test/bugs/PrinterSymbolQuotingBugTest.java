package org.smtlib.test.TO_BE_FIXED;

import java.io.StringWriter;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.SMT;
import org.smtlib.sexpr.Printer;

/**
 * Pins down sexpr/Printer.java:136-142's {@code visit(ISymbol)}, whose root cause is in
 * {@code impl/SMTExpr.java}'s {@code Symbol} class:
 *
 * <pre>public Void visit(ISymbol e) throws IVisitor.VisitorException {
 *     // FIXME: toString() is correct for parsed symbols but not for programmatically
 *     // constructed ones with special characters -- those need bar-quoting via value().
 *     append(e.toString());
 *     return null;
 * }</pre>
 *
 * {@code e.toString()} returns the symbol's {@code originalString}, which for a symbol that
 * came from parsing bar-quoted text already includes the enclosing {@code |...|}. But a
 * symbol built programmatically from an arbitrary string (e.g.
 * {@code exprFactory.symbol("has space")}) has {@code originalString} set to that raw string
 * with no bars at all -- printing it unconditionally via {@code toString()} produces text
 * that isn't valid SMT-LIB syntax (a bare symbol cannot contain whitespace or other
 * symbol-breaking characters per the grammar) and can't be re-parsed.
 * <p>
 * Asserts the correct behavior: printing a symbol whose value requires bar-quoting (contains
 * a space) should produce valid, bar-quoted, re-parseable output. This currently FAILS
 * against today's code (printed unquoted), documenting the bug.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/75">issue #75</a>.
 */
public class PrinterSymbolQuotingBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    @Test
    public void programmaticallyBuiltSymbolWithSpaceIsBarQuotedWhenPrinted() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        ISymbol sym = config.exprFactory.symbol("has space");

        StringWriter sw = new StringWriter();
        Printer.write(sw, sym);
        String printed = sw.toString();

        Assert.assertEquals("|has space|", printed);
    }
}
