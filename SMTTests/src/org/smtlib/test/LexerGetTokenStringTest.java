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
 * Lexer.getToken(config, text) returns the first token of text, with positions in text. A JUnit
 * test: getToken(config, text) is API with no command-line route.
 */
public class LexerGetTokenStringTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    private static void check(SMT.Configuration config, String text, String kind) throws Exception {
        ILexToken token = Lexer.getToken(config, text);
        Assert.assertEquals(text, kind, token.kind());
        Assert.assertEquals(text, text, token.pos().source().chars().toString());
    }

    @Test
    public void firstTokenOfText() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        config.log.clearListeners();
        config.log.addListener(new JUnitListener());
        check(config, "42", "numeral");
        check(config, "abc", "symbol");
        check(config, "|a b|", "symbol");
        check(config, "\"ab\"", "string-literal");
        check(config, " \"ab\"", "string-literal");
        check(config, "\"ab", "error");
        check(config, "|ab", "error");
        check(config, "007", "error");
    }
}
