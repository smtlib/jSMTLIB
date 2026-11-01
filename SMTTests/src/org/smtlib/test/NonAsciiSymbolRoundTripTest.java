package org.smtlib.test;

import java.io.StringWriter;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.IExpr;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IParser;
import org.smtlib.SMT;
import org.smtlib.SMT.Configuration.SMTLIB;
import org.smtlib.sexpr.Printer;

/**
 * Symbols built through the API with non-ASCII characters print as text that parses back to an
 * equal symbol, which prints identically. Non-ASCII characters are allowed in quoted symbols from
 * SMT-LIB 2.5 on; 2.0 rejects them when parsing and isOKSymbol reports them illegal. Stays a JUnit
 * test: the symbols are built through the factory, not parsed.
 */
public class NonAsciiSymbolRoundTripTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    /** Non-ASCII symbols (all need bars), some also needing bars for other reasons, and a plain ASCII one */
    private static final String[] VALUES = {
        "caf\u00e9", "\u03c0", "x\u0663", "\u65e5\u672c\u8a9e", "\ud835\udd38",
        "has space \u00e9", "\u00e9(x)", "1\u00e9", "a\nb\u00e9", "abc"
    };

    private static String print(SMT.Configuration config, IExpr e) throws Exception {
        StringWriter sw = new StringWriter();
        Printer.write(config, sw, e);
        return sw.toString();
    }

    private static SMT.Configuration config(SMTLIB version, JUnitListener listener) {
        SMT.Configuration config = new SMT.Configuration();
        config.smtlib = version;
        config.log.clearListeners();
        config.log.addListener(listener);
        return config;
    }

    private static IExpr parse(SMT.Configuration config, String text) throws Exception {
        IParser p = new org.smtlib.sexpr.Parser(config, config.smtFactory.createSource(text, null));
        return p.parseExpr();
    }

    @Test
    public void nonAsciiSymbolsRoundTripFrom25() throws Exception {
        for (SMTLIB version : new SMTLIB[]{ SMTLIB.V25, SMTLIB.V26, SMTLIB.V27 }) {
            for (String value : VALUES) {
                JUnitListener listener = new JUnitListener();
                SMT.Configuration config = config(version, listener);
                ISymbol sym = config.exprFactory.symbol(value);
                String printed = print(config, sym);
                IExpr parsed = parse(config, printed);
                String where = version + " " + printed;
                Assert.assertTrue(where, config.isOKSymbol(value));
                Assert.assertTrue(where + ": " + listener.msgs, listener.msgs.isEmpty());
                Assert.assertTrue(where, parsed instanceof ISymbol);
                Assert.assertEquals(where, value, ((ISymbol)parsed).value());
                Assert.assertEquals(where, sym, parsed);
                Assert.assertEquals(where, printed, print(config, parsed));
            }
        }
    }

    @Test
    public void nonAsciiSymbolIsAParseErrorIn20() throws Exception {
        JUnitListener listener = new JUnitListener();
        SMT.Configuration config = config(SMTLIB.V20, listener);
        Assert.assertFalse(config.isOKSymbol("caf\u00e9"));
        String printed = print(config, config.exprFactory.symbol("caf\u00e9"));
        Assert.assertEquals("|caf\u00e9|", printed);
        try {
            parse(config, printed);
            Assert.fail("expected a ParserException");
        } catch (IParser.ParserException e) {
            Assert.assertEquals("Invalid character: ASCII(decimal) = 233", e.getMessage());
        }
    }
}
