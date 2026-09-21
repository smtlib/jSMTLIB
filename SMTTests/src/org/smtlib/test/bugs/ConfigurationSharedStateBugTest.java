package org.smtlib.test.bugs;

import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.SMT;

/**
 * Pins down (and confirms the fix for) SMT.java:104 (Configuration.clone()).
 * <p>
 * See also <a href="https://github.com/smtlib/jSMTLIB/issues/22">issue #22</a> -- a related
 * but still-open SMT.Configuration static-state bug (SMT.java:88-90), whose tests live in
 * {@code org.smtlib.test.TO_BE_FIXED} since it's not yet fixed.
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/23">issue #23</a> (this one).
 * <p>
 * Stays a JUnit test: the bug only manifests when two {@code Configuration} instances exist
 * side by side in one process and one's settings are checked against the other's -- every CLI
 * invocation is its own separate process with exactly one {@code Configuration}, so there is
 * no script-observable way to construct this scenario.
 */
public class ConfigurationSharedStateBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    /** SMT.java:104 (Configuration.clone()) -- FIXED. The original line did
     *  "utils.smtConfig = this;", operating on the original (this) rather than the clone (c)
     *  it just built; a first attempt at fixing it ("c.utils.smtConfig = c;") was still
     *  incomplete, since c.utils remained the SAME shared Utils object as the original's (a
     *  shallow field copy from super.clone()) -- so that line also silently repointed the
     *  original's own utils.smtConfig at the clone. The real fix gives the clone its own
     *  Utils instance: {@code c.utils = new Utils(c);}.
     *  <p>
     *  This test checks both directions: the clone's own utils must reflect the clone's own
     *  settings, AND the original's utils must keep reflecting the original's own settings
     *  after cloning (the second half is exactly what the incomplete first fix would still
     *  fail). Demonstrated via Utils.quote(), whose escaping rules depend on
     *  smtConfig.isVersion(V2.0) (see ParseExpressionErrors' errorBadSymbol8a for the same
     *  version-dependent escaping).
     *  <p>
     *  Confirmed to manifest in real usage: {@code Utils.findLogic}/{@code findTheory} both
     *  clone smtConfig on every call (e.g. every {@code set-logic} command) -- before the
     *  complete fix, calling findLogic once and then changing the *original* Configuration's
     *  own smtlib field no longer had any effect on that Configuration's own utils.quote()
     *  output, because utils.smtConfig had been silently repointed at the (by-then-discarded)
     *  clone from the findLogic call.
     *  See <a href="https://github.com/smtlib/jSMTLIB/issues/23">issue #23</a>. */
    @Test
    public void cloneAndOriginalEachKeepTheirOwnUtils() throws Exception {
        SMT.Configuration original = new SMT.Configuration();
        original.smtlib = "V2.0";
        SMT.Configuration clone = original.clone();

        // Fixed: the clone gets its own independent Utils instance.
        Assert.assertNotSame(original.utils, clone.utils);

        // Diverge the clone's own version setting from the original's.
        clone.smtlib = "V2.7";

        // The clone's own quoting reflects the clone's own V2.7 setting (backslash left
        // unescaped), not the original's V2.0 setting (which would escape it to "\\\\").
        Assert.assertEquals("\"a\\b\"", clone.utils.quote("a\\b"));

        // The original's own quoting is unaffected by the clone's existence or its later
        // mutation -- still V2.0 (backslash escaped). This is exactly what the incomplete
        // "c.utils.smtConfig = c;" fix got wrong: it left original.utils.smtConfig pointing
        // at the clone instead.
        Assert.assertEquals("\"a\\\\b\"", original.utils.quote("a\\b"));
    }
}
