package org.smtlib.test.bugs;

import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.SMT;

/**
 * Pins down (and, for two of the three, fixes) SMT.java's documented-but-broken
 * command-line short aliases (see SMT.usage()), each tested against
 * SMT.processCommandLine() directly.
 * <p>
 * -r now aliases --relax (fixed in code: the parsing loop previously never checked for
 * it). -v and -e were, on inspection, never actually broken in the way the usage() text
 * implied -- their doc lines were misleading, not their code -- so both were fixed by
 * correcting the docs instead of the parsing:
 * <ul>
 * <li>-v is shorthand for {@code --verbose 1} (a bare flag, consuming no argument), not
 * {@code --verbose <int>} as usage() used to claim; usage()/help() now say so.
 * <li>-e remains --exec's alias (requires a following path argument, sets
 * options.executable); --echo has no short form of its own and is set only by the long
 * "--echo" flag. usage()'s incorrect "--echo [-e]" claim has been removed.
 * </ul>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/26">issue #26</a>.
 */
public class SMTCommandLineAliasBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    /** -r is documented as an alias for --relax, but the parsing loop never checks for it
     *  (only the literal "--relax" string is checked) -- it falls through to the generic
     *  "starts with -" branch and is rejected as an unknown option. */
    @Test
    public void dashRAliasesRelax() throws Exception {
        SMT smt = new SMT();
        int rc = smt.processCommandLine(new String[] { "-r" }, smt.smtConfig);
        Assert.assertEquals(0, rc);
        Assert.assertTrue("-r should enable relax, like --relax", smt.smtConfig.relax);
    }

    /** -v is shorthand for --verbose 1 -- a bare flag, not an integer-taking option. This
     *  documents the chosen, still-current behavior (the code was never wrong here; only
     *  usage()'s old "--verbose [-v] &lt;int&gt;" line, now corrected, was misleading). A
     *  following non-option token is a file argument, exactly as if -v weren't there. */
    @Test
    public void dashVIsShorthandForVerboseOne() throws Exception {
        SMT smt = new SMT();
        int rc = smt.processCommandLine(new String[] { "-v", "3" }, smt.smtConfig);
        Assert.assertEquals(0, rc);
        Assert.assertEquals(1, smt.smtConfig.verbose);
        Assert.assertEquals("the trailing token is a file argument, not consumed by -v",
                java.util.Collections.singletonList("3"), smt.smtConfig.files);
    }

    /** -e remains --exec's alias (requires a following path argument, sets
     *  options.executable) -- --echo has no short form; it is set only by the long
     *  "--echo" flag. This documents the chosen, still-current behavior (not a bug),
     *  now that usage()'s incorrect "--echo [-e]" claim has been removed. */
    @Test
    public void dashEStillAliasesExecNotEcho() throws Exception {
        SMT smt = new SMT();
        // --solver is required alongside an explicit executable (processCommandLine
        // otherwise rejects it after the parsing loop, independent of -e/--exec parsing).
        int rc = smt.processCommandLine(
                new String[] { "-e", "/path/to/solver", "--solver", "test" }, smt.smtConfig);
        Assert.assertEquals(0, rc);
        Assert.assertEquals("/path/to/solver", smt.smtConfig.executable);
        Assert.assertFalse(smt.smtConfig.echo);

        SMT smt2 = new SMT();
        int rc2 = smt2.processCommandLine(new String[] { "--echo" }, smt2.smtConfig);
        Assert.assertEquals(0, rc2);
        Assert.assertTrue(smt2.smtConfig.echo);
    }
}
