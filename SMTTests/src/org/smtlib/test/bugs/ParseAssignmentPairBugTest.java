package org.smtlib.test.bugs;

import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.IResponse;
import org.smtlib.ISource;
import org.smtlib.SMT;
import org.smtlib.sexpr.Parser;

/**
 * Pins down sexpr/Parser.java:922-928's {@code parseAssignmentPair()}:
 *
 * <pre>public IResponse.IPair&lt;ISymbol,Boolean&gt; parseAssignmentPair() throws ParserException {
 *     parseLP();
 *     ISymbol sym = parseSymbol();
 *     ISymbol val = parseSymbol();
 *     parseRP();
 *     return smtConfig.responseFactory.pair(sym, Boolean.valueOf(val.value()));
 * }</pre>
 *
 * {@code Boolean.valueOf(String)} returns {@code true} only for (case-insensitively) "true",
 * and silently returns {@code false} for *any* other string -- there's no validation that the
 * token was actually "true" or "false" before accepting it. This is used when parsing a real
 * solver's get-assignment response, so a malformed or unexpected token from a quirky solver
 * (e.g. "1", "yes", a typo) is silently reinterpreted as false rather than flagged as a
 * protocol violation.
 * <p>
 * Asserts the correct behavior: a value token that is neither "true" nor "false" should be
 * rejected with a parse error, not silently accepted as false.
 * <p>
 * Fixed by having {@code parseAssignmentPair()} explicitly check the value token is
 * (case-insensitively) "true" or "false" and raise a {@code ParserException} for anything else,
 * instead of delegating straight to {@code Boolean.valueOf}'s permissive parsing.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/73">issue #73</a>.
 */
public class ParseAssignmentPairBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    @Test
    public void nonBooleanValueTokenIsRejected() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        ISource source = config.smtFactory.createSource("(x maybe)", null);
        Parser p = new Parser(config, source);

        boolean threw = false;
        IResponse.IPair<?, ?> pair = null;
        try {
            pair = p.parseAssignmentPair();
        } catch (org.smtlib.IParser.ParserException e) {
            threw = true;
        }

        Assert.assertTrue("a non-boolean value token (\"maybe\") should be rejected as a parse error, "
                + "not silently accepted as false" + (pair != null ? " (got: " + pair.first() + " -> " + pair.second() + ")" : ""),
                threw);
    }
}
