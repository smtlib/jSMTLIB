package org.smtlib.test.TO_BE_FIXED;

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
 * Pins down SMT.java:88-90 (the Configuration constructor), which contradicts the class's
 * own doc comment claiming separate Configuration/SMT instances "can be run independently
 * and in parallel". Not yet fixed -- this is an architectural change (the three fields need
 * to become instance-scoped, threaded through where they're needed), not a one-line patch,
 * and no user-visible behavior is immediately broken by it in ordinary single-Configuration
 * use, so it's kept here rather than in the main {@code bugs} package until someone takes it
 * on.
 * <p>
 * See also {@link org.smtlib.test.bugs.ConfigurationSharedStateBugTest} for the related,
 * already-fixed issue #23 (Configuration.clone()), and
 * {@link StaticSmtConfigStringLiteralBugTest} for a sharper, concrete manifestation of this
 * same bug via {@code SMTExpr.StringLiteral} construction.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/22">issue #22</a>.
 */
public class ConfigurationStaticLeakBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    /** SMT.java:88-90 (Configuration constructor): Printer.smtConfig = this; Response.smtConfig
     *  = this; SMTExpr.smtConfig = this -- all three targets are plain static fields, so
     *  constructing a second Configuration silently repoints the first instance's
     *  printing/response/escaping rules at the second instance's settings. This test currently
     *  fails (it documents the bug); once these three fields are made non-static (or otherwise
     *  scoped per-Configuration), it should be rewritten to assert that c1 keeps sole ownership
     *  of its own printer/response/expr state after c2 is constructed. */
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
}
