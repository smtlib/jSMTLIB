package org.smtlib.test;

import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.SMT;
import org.smtlib.sexpr.ILexToken;
import org.smtlib.sexpr.Lexer;

/**
 * Lexer.getToken(String) lexes its argument on its own, whatever the Lexer's own source (none, or
 * other text), and leaves that source's scanning undisturbed. A JUnit test: getToken(String) is
 * API with no command-line route.
 */
public class LexerGetTokenStringTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    private static SMT.Configuration config() {
        SMT.Configuration config = new SMT.Configuration();
        config.log.clearListeners();
        config.log.addListener(new JUnitListener());
        return config;
    }

    private static void check(Lexer lexer, String text, String kind) throws Exception {
        ILexToken token = lexer.getToken(text);
        Assert.assertEquals(text, kind, token.kind());
        Assert.assertEquals(text, text, token.pos().source().chars().toString());
    }

    private static void checkAll(Lexer lexer) throws Exception {
        check(lexer, "42", "numeral");
        check(lexer, "abc", "symbol");
        check(lexer, "|a b|", "symbol");
        check(lexer, "\"ab\"", "string-literal");
        check(lexer, " \"ab\"", "string-literal");
        check(lexer, "\"ab", "error");
        check(lexer, "|ab", "error");
        check(lexer, "007", "error");
    }

    @Test
    public void lexerWithoutSource() throws Exception {
        checkAll(new Lexer(config(), null));
    }

    @Test
    public void lexerWithOtherSource() throws Exception {
        SMT.Configuration config = config();
        Lexer lexer = new Lexer(config, config.smtFactory.createSource("(assert (= x y)) ; a longer source", null));
        checkAll(lexer);
        Assert.assertTrue(lexer.getToken().isLP());
        Assert.assertEquals("assert", lexer.getToken().toString());
    }
}
