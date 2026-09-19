package org.smtlib.test.bugs;

import java.io.StringWriter;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.SMT;
import org.smtlib.sexpr.Printer;
import org.smtlib.sexpr.Sexpr;

/**
 * Pins down issue #87: {@code sexpr/Printer.visit(ISexpr.IToken<?>)}, the generic
 * token-printing fallback, bypassed quoting for string-valued tokens --
 * {@code append(String.valueOf(e.value()))} with no call to the quoting logic {@code
 * visit(IStringLiteral)} already uses ({@code smtConfig.utils.quote(...)}) -- so a
 * string-valued token containing a character that needs escaping (e.g. an embedded
 * double-quote) printed through this generic path produced unparseable output. Related in
 * spirit to #75 ({@code visit(ISymbol)} bar-quoting, already fixed), but for the generic
 * sexpr-token fallback rather than symbols specifically.
 * <p>
 * {@code ISexpr.IToken<T>} is generic and not constructed anywhere in this codebase's own
 * command/parsing paths today -- the parser always builds the real typed leaf AST classes
 * directly instead (see issue #84, which removed the unused {@code ISexpr.IFactory} on that
 * basis) -- but {@code Sexpr.Token} itself is public API surface an external embedder of the
 * library could use directly, so the bug is real even though nothing internal currently
 * exercises it.
 * <p>
 * Fixed by quoting a String-valued token's value the same way {@code visit(IStringLiteral)}
 * does; non-String token values are printed exactly as before ({@code String.valueOf}).
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/87">issue #87</a>.
 */
public class PrinterTokenStringQuotingBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    @Test
    public void stringValuedTokenIsQuotedWhenItNeedsEscaping() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        String raw = "say \"hi\"";
        Sexpr.Token<String> token = new Sexpr.Token<>(raw);

        StringWriter sw = new StringWriter();
        Printer.write(config, sw, token);

        Assert.assertEquals(config.utils.quote(raw), sw.toString());
    }

    @Test
    public void simpleStringValuedTokenStaysBare() throws Exception {
        // A String value with nothing that would break tokenization must still print
        // as-is, unquoted -- matching PrinterCoverageTest.sexprToken()'s existing
        // expectation, which this must not regress.
        SMT.Configuration config = new SMT.Configuration();
        Sexpr.Token<String> token = new Sexpr.Token<>("hello");

        StringWriter sw = new StringWriter();
        Printer.write(config, sw, token);

        Assert.assertEquals("hello", sw.toString());
    }

    @Test
    public void nonStringTokenIsUnaffected() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        Sexpr.Token<Integer> token = new Sexpr.Token<>(42);

        StringWriter sw = new StringWriter();
        Printer.write(config, sw, token);

        Assert.assertEquals("42", sw.toString());
    }
}
