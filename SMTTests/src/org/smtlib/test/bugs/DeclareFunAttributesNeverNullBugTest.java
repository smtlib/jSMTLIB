package org.smtlib.test.bugs;

import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.SMT;
import org.smtlib.command.C_declare_fun;

/**
 * Pins down issue #42 point 2: {@code C_declare_fun.attributes()} used to be {@code null} when
 * no trailing attributes were given, unlike {@code parameters()} (whose {@code null} is
 * load-bearing -- it distinguishes the non-standard par-polymorphic form from an ordinary
 * declaration, and stays {@code null} deliberately) or {@code argSorts()} (already always a
 * real list from every construction path). Unlike {@code parameters()}, {@code attributes()}'s
 * null-vs-empty drew no real distinction anywhere: its one consumer ({@code
 * Solver_test.declare_fun()}) already treated them identically, and the concrete syntax has no
 * way to write an explicit-but-empty attribute clause to begin with.
 * <p>
 * Fixed by making {@code attributes()} never null -- {@code Collections.emptyList()} when none
 * were given -- across every construction path (the convenience constructors, the parser, and
 * defensively in the field-setting constructor for any direct caller), matching {@code
 * argSorts()}'s existing guarantee.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/42">issue #42</a>.
 */
public class DeclareFunAttributesNeverNullBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    @Test
    public void attributesIsNeverNullViaTheThreeArgConvenienceConstructor() {
        SMT.Configuration config = new SMT.Configuration();
        C_declare_fun cmd = new C_declare_fun(
                config.exprFactory.symbol("f"), java.util.Collections.emptyList(),
                config.sortFactory.Bool());

        Assert.assertNotNull("attributes() must never be null", cmd.attributes());
        Assert.assertTrue(cmd.attributes().isEmpty());
    }

    @Test
    public void attributesIsNeverNullEvenIfNullIsPassedDirectly() {
        SMT.Configuration config = new SMT.Configuration();
        // The 5-arg constructor is the one real callers (including external embedders via the
        // public API) can reach directly with a literal null -- must still be coalesced.
        C_declare_fun cmd = new C_declare_fun(
                config.exprFactory.symbol("f"), java.util.Collections.emptyList(),
                config.sortFactory.Bool(), null, null);

        Assert.assertNotNull("attributes() must never be null, even if null was passed in",
                cmd.attributes());
        Assert.assertTrue(cmd.attributes().isEmpty());
        Assert.assertNull("parameters() null-ness is load-bearing and must be preserved",
                cmd.parameters());
    }
}
