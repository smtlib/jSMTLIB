package org.smtlib.test.bugs;

import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.SMT;
import org.smtlib.impl.Response;
import org.smtlib.impl.SMTExpr;
import org.smtlib.sexpr.Printer;

/**
 * Pins down two related SMT.Configuration bugs (SMT.java:88-90 and SMT.java:104) that both
 * contradict the class's own doc comment claiming separate Configuration/SMT instances "can
 * be run independently and in parallel". See
 * <a href="https://github.com/smtlib/jSMTLIB/issues/22">issue #22</a> (constructor) and
 * <a href="https://github.com/smtlib/jSMTLIB/issues/23">issue #23</a> (clone()).
 */
public class ConfigurationSharedStateBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    /** SMT.java:88-90 (Configuration constructor): Printer.smtConfig = this; Response.smtConfig
     *  = this; SMTExpr.smtConfig = this -- all three targets are plain static fields, so
     *  constructing a second Configuration silently repoints the first instance's
     *  printing/response/escaping rules at the second instance's settings. This test currently
     *  fails (it documents the bug); once these three fields are made non-static (or otherwise
     *  scoped per-Configuration), it should be rewritten to assert that c1 keeps sole ownership
     *  of its own printer/response/expr state after c2 is constructed.
     *  See <a href="https://github.com/smtlib/jSMTLIB/issues/22">issue #22</a>. */
    @Test
    public void secondConfigurationConstructionRepointsFirstInstancesStatics() throws Exception {
        SMT.Configuration c1 = new SMT.Configuration();
        Assert.assertSame(c1, Printer.smtConfig);
        Assert.assertSame(c1, Response.smtConfig);
        Assert.assertSame(c1, SMTExpr.smtConfig);

        SMT.Configuration c2 = new SMT.Configuration();

        // BUG: c1's supposedly-independent static state now points at c2, not c1.
        Assert.assertSame(c1, Printer.smtConfig);
        Assert.assertSame(c1, Response.smtConfig);
        Assert.assertSame(c1, SMTExpr.smtConfig);
    }

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
