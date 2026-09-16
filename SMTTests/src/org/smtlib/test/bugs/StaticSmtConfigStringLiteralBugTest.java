package org.smtlib.test.bugs;

import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.SMT;
import org.smtlib.impl.SMTExpr;

/**
 * Pins down a concrete, reachable manifestation of the SMT.Configuration static-state leak
 * (SMT.java:88-90 -- see issue #22) that is worse than the generic aliasing already covered
 * by {@link ConfigurationSharedStateBugTest}: {@code SMTExpr.StringLiteral}'s constructor
 * (impl/SMTExpr.java:78) calls {@code smtConfig.utils.unescape(value)} at *token construction
 * time*, reading the static {@code SMTExpr.smtConfig} field directly -- not whichever
 * Configuration is actually driving the parse that's constructing this token.
 * <p>
 * Escaping rules are version-dependent ({@code Utils.unescape}: V2.0 treats {@code \\} as an
 * escape for a literal backslash; V2.5+ does not treat {@code \} specially at all, only
 * {@code ""}). So the *same* raw quoted text unescapes differently depending on which
 * Configuration happens to be the most recently constructed one anywhere in the process --
 * regardless of which Configuration's parser is actually producing this token. String-literal
 * tokens for a parse already in progress can flip meaning mid-run if a second Configuration is
 * constructed elsewhere (e.g. a concurrent session, or a nested findLogic/findTheory call).
 * <p>
 * Asserts the correct, unreachable-today behavior: constructing a StringLiteral should
 * consistently reflect a *specific* Configuration's escaping rules, not whichever
 * Configuration was constructed most recently. This currently FAILS against today's code
 * (the raw text unescapes differently before/after an unrelated second Configuration is
 * built), documenting the bug.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/22">issue #22</a>.
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

        String underA = new SMTExpr.StringLiteral(raw, true).value();
        // Correct/expected: under A's (non-V2.0) rules, backslash is ordinary -- unchanged.
        Assert.assertEquals("a\\\\b", underA);

        // Some unrelated code elsewhere in the process constructs a second Configuration
        // (e.g. a concurrent session, or Utils.findLogic/findTheory's own internal clone()).
        SMT.Configuration b = new SMT.Configuration();
        b.smtlib = "V2.0";

        // The SAME raw text, still conceptually parsed "as far as Configuration A is
        // concerned" -- but StringLiteral's constructor reads the static SMTExpr.smtConfig
        // field, which is now B, not A. Correct behavior: this should be unaffected by B's
        // existence and still reflect A's own rules.
        String stillUnderA = new SMTExpr.StringLiteral(raw, true).value();
        Assert.assertEquals("a\\\\b", stillUnderA);
    }
}
