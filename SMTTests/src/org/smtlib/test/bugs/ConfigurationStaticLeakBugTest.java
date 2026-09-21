package org.smtlib.test.bugs;

import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.SMT;
import org.smtlib.IExpr.IStringLiteral;

/**
 * Regression test for the former SMT.Configuration static-state leak (SMT.java's
 * Configuration constructor used to do {@code Printer.smtConfig = this},
 * {@code Response.smtConfig = this}, {@code SMTExpr.smtConfig = this} -- three plain static
 * fields, so constructing a second Configuration silently repointed the first instance's
 * printing/response/escaping rules at the second instance's settings), which contradicted the
 * class's own doc comment claiming separate Configuration/SMT instances "can be run
 * independently and in parallel".
 * <p>
 * Fixed by making {@code sexpr.Printer}, {@code Response.Factory}, and
 * {@code SMTExpr.StringLiteral}/{@code Logic} all instance-scoped to (or explicitly
 * parameterized by) the Configuration that constructs them, instead of reading a shared static.
 * This test constructs two Configurations and confirms each one's expression-factory
 * string-literal construction stays tied to itself, unaffected by the other's existence.
 * <p>
 * See also {@link org.smtlib.test.bugs.ConfigurationSharedStateBugTest} for the related,
 * already-fixed issue #23 (Configuration.clone()), and
 * {@link StaticSmtConfigStringLiteralBugTest} for the sharper, concrete manifestation of this
 * same bug via {@code SMTExpr.StringLiteral} construction.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/22">issue #22</a>.
 * <p>
 * Stays a JUnit test: the bug only manifests when two {@code Configuration} instances exist
 * side by side in one process and one's expression-factory state is checked against the
 * other's -- every CLI invocation is its own separate process with exactly one
 * {@code Configuration}, so there is no script-observable way to construct this scenario.
 */
public class ConfigurationStaticLeakBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    /** Constructing a second Configuration must not repoint the first one's expression-factory
     *  string-literal construction (formerly routed through the static SMTExpr.smtConfig). */
    @Test
    public void secondConfigurationConstructionDoesNotRepointFirstInstancesExprFactory() throws Exception {
        SMT.Configuration c1 = new SMT.Configuration();
        IStringLiteral lit1 = c1.exprFactory.unquotedString("hello");
        Assert.assertEquals("hello", lit1.value());

        SMT.Configuration c2 = new SMT.Configuration();
        // Must not throw and must not have altered c1's own literal.
        c2.exprFactory.unquotedString("world");

        Assert.assertEquals("hello", lit1.value());
        Assert.assertEquals("hello", c1.exprFactory.unquotedString("hello").value());
    }
}
