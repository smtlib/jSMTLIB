package org.smtlib.test.bugs;

import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.SMT;
import org.smtlib.impl.SMTExpr;

/**
 * Regression test for a concrete, reachable manifestation of the former SMT.Configuration
 * static-state leak (see issue #22) that was worse than the generic aliasing covered by
 * {@link org.smtlib.test.bugs.ConfigurationSharedStateBugTest}: {@code SMTExpr.StringLiteral}'s
 * constructor calls {@code smtConfig.utils.unescape(value)} at *token construction time*, and
 * used to read a static {@code SMTExpr.smtConfig} field -- not whichever Configuration was
 * actually driving the parse that constructed this token.
 * <p>
 * Escaping rules are version-dependent ({@code Utils.unescape}: V2.0 treats {@code \\} as an
 * escape for a literal backslash; V2.5+ does not treat {@code \} specially at all, only
 * {@code ""}). With the static field, the *same* raw quoted text would unescape differently
 * depending on which Configuration happened to be the most recently constructed one anywhere in
 * the process -- regardless of which Configuration's parser was actually producing the token.
 * {@code StringLiteral} now takes its Configuration as an explicit constructor argument instead,
 * so each token consistently reflects the Configuration that built it.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/22">issue #22</a>.
 * <p>
 * Stays a JUnit test: the bug only manifests when two {@code Configuration} instances exist
 * side by side in one process and one's escaping rules are checked against the other's --
 * every CLI invocation is its own separate process with exactly one {@code Configuration}, so
 * there is no script-observable way to construct this scenario.
 */
public class StaticSmtConfigStringLiteralBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    @Test
    public void stringLiteralEscapingFlipsWhenAnUnrelatedConfigurationIsConstructed() throws Exception {
        // Config A: latest version (non-V2.0) -- backslash is not a special escape character.
        SMT.Configuration a = new SMT.Configuration();
        a.smtlib = null;

        // Raw SMT-LIB text (with enclosing quotes): a, backslash, backslash, b.
        String raw = "\"a\\\\b\"";

        String underA = new SMTExpr.StringLiteral(a, raw, true).value();
        // Correct/expected: under A's (non-V2.0) rules, backslash is ordinary -- unchanged.
        Assert.assertEquals("a\\\\b", underA);

        // Some unrelated code elsewhere in the process constructs a second Configuration
        // (e.g. a concurrent session, or Utils.findLogic/findTheory's own internal clone()).
        SMT.Configuration b = new SMT.Configuration();
        b.smtlib = "V2.0";

        // The SAME raw text, still conceptually parsed "as far as Configuration A is
        // concerned" -- StringLiteral's constructor now takes the Configuration explicitly, so
        // this is unaffected by B's existence and still reflects A's own rules.
        String stillUnderA = new SMTExpr.StringLiteral(a, raw, true).value();
        Assert.assertEquals("a\\\\b", stillUnderA);
    }
}
