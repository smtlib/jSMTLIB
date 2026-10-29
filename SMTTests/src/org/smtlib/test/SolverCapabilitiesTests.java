package org.smtlib.test;

import java.util.Properties;

import org.junit.Assert;
import org.junit.Test;
import org.smtlib.SolverCapabilities;
import org.smtlib.SolverCapabilities.Capability;
import org.smtlib.SolverCapabilities.Support;

/** {@link SolverCapabilities} (#157): the lookup rules against made-up properties, and the
 *  built-in entries of jsmtlib.properties */
public class SolverCapabilitiesTests {

    private static final String P = "org.smtlib.solver_";

    /** The solver names configured in jsmtlib.properties, each of which must record every capability */
    private static final String[] BUILT_IN = { "z3", "z3-4.3", "z3-4.5.0", "z3-4.6.0", "z3-4.7.1", "z3-4.8.12",
        "z3-4.16.0", "cvc5", "cvc5-1.3.2",
        "yices2", "yices2-2.6.5", "yices2-2.7.0", "smtinterpol-2.5", "bitwuzla", "simplify", "altergo" };

    private static Properties props(String... keyValues) {
        Properties p = new Properties();
        for (int i = 0; i < keyValues.length; i += 2) p.setProperty(P + keyValues[i], keyValues[i + 1]);
        return p;
    }

    private static Support q(Properties p, String solver, Capability c) {
        return SolverCapabilities.supports(p, solver, c);
    }

    @Test
    public void listedNegatedAndUnmentioned() {
        Properties p = props("s.capabilities", "strings, -proofs");
        Assert.assertEquals(Support.YES, q(p, "s", Capability.STRINGS));
        Assert.assertEquals(Support.NO, q(p, "s", Capability.PROOFS));
        Assert.assertEquals(Support.UNKNOWN, q(p, "s", Capability.DATATYPES));
    }

    @Test
    public void noEntryIsUnknown() {
        Assert.assertEquals(Support.UNKNOWN, q(props(), "s", Capability.STRINGS));
        Assert.assertEquals(Support.UNKNOWN, q(props(), "s-1.0", Capability.STRINGS));
    }

    @Test
    public void familyFallback() {
        Properties p = props("s.capabilities", "strings", "s-1.0.capabilities", "-strings");
        Assert.assertEquals(Support.NO, q(p, "s-1.0", Capability.STRINGS));
        Assert.assertEquals(Support.YES, q(p, "s-2.0", Capability.STRINGS));
        // What an exact entry does not mention is taken from the family, capability by capability
        Properties p2 = props("s.capabilities", "proofs,-strings", "s-1.0.capabilities", "strings");
        Assert.assertEquals(Support.YES, q(p2, "s-1.0", Capability.PROOFS));
        Assert.assertEquals(Support.YES, q(p2, "s-1.0", Capability.STRINGS));
        Assert.assertEquals(Support.UNKNOWN, q(p2, "s-1.0", Capability.DATATYPES));
    }

    @Test
    public void familyName() {
        Assert.assertEquals("z3", SolverCapabilities.family("z3-4.12.6"));
        Assert.assertEquals("yices2", SolverCapabilities.family("yices2-2.7.0"));
        Assert.assertEquals("smtinterpol", SolverCapabilities.family("smtinterpol-2.5"));
        Assert.assertNull(SolverCapabilities.family("cvc5"));
        Assert.assertNull(SolverCapabilities.family("my-solver"));
    }

    @Test
    public void capabilityNames() {
        Assert.assertEquals(Capability.FLOATING_POINT, Capability.lookup("floating-point"));
        Assert.assertEquals(Capability.FLOATING_POINT, Capability.lookup("Floating_Point"));
        Assert.assertEquals(Capability.DATATYPES, Capability.lookup("DATATYPES"));
        Assert.assertNull(Capability.lookup("sequences"));
    }

    @Test(expected = IllegalArgumentException.class)
    public void unknownTokenIsAnError() {
        q(props("s.capabilities", "strings,sequences"), "s", Capability.STRINGS);
    }

    @Test(expected = IllegalArgumentException.class)
    public void contradictionIsAnError() {
        q(props("s.capabilities", "strings,-strings"), "s", Capability.STRINGS);
    }

    @Test(expected = IllegalArgumentException.class)
    public void unknownCapabilityNameIsAnError() {
        SolverCapabilities.supports("cvc5", "sequences");
    }

    /** Every built-in solver records every capability, so UNKNOWN never hides a forgotten entry */
    @Test
    public void builtInEntriesAreComplete() {
        for (String s : BUILT_IN) {
            for (Capability c : Capability.values()) {
                Assert.assertNotEquals(s + " " + c.token, Support.UNKNOWN, SolverCapabilities.supports(s, c));
            }
        }
    }

    @Test
    public void builtInSamples() {
        Assert.assertEquals(Support.YES, SolverCapabilities.supports("cvc5", "strings"));
        Assert.assertEquals(Support.YES, SolverCapabilities.supports("z3-4.12.6", Capability.FLOATING_POINT));
        Assert.assertEquals(Support.NO, SolverCapabilities.supports("z3-4.3", Capability.FLOATING_POINT));
        Assert.assertEquals(Support.NO, SolverCapabilities.supports("z3-4.7.1", Capability.STRINGS));
        Assert.assertEquals(Support.YES, SolverCapabilities.supports("z3-4.7.1", Capability.DATATYPES));
        Assert.assertEquals(Support.NO, SolverCapabilities.supports("z3-4.6.0", Capability.DATATYPES));
        Assert.assertEquals(Support.NO, SolverCapabilities.supports("yices2", Capability.DATATYPES));
        Assert.assertEquals(Support.YES, SolverCapabilities.supports("bitwuzla", Capability.FLOATING_POINT));
        Assert.assertEquals(Support.NO, SolverCapabilities.supports("bitwuzla", Capability.PROOFS));
        Assert.assertEquals(Support.YES, SolverCapabilities.supports("altergo", Capability.DATATYPES));
        Assert.assertEquals(Support.UNKNOWN, SolverCapabilities.supports("unconfigured", Capability.STRINGS));
    }
}
