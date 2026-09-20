package org.smtlib.test.bugs;

import org.junit.Assert;
import org.junit.Test;
import org.smtlib.ISource;
import org.smtlib.impl.Pos;

/**
 * Pins down impl/Pos.java's {@code Source.lineNumber(int pos)}: when the character at
 * {@code pos-1} is {@code \r} and {@code pos == chars().length()} (a lone trailing
 * carriage return at the very end of the source, with nothing after it), the \n-lookahead
 * check does {@code charAt(i+1)}, i.e. {@code charAt(pos)} -- one past the end of the
 * sequence.
 * <p>
 * Asserts the correct behavior: {@code lineNumber} at the end of a source ending in a bare
 * trailing {@code \r} returns the right line count without throwing.
 */
public class SourceLineNumberTrailingCRBugTest {

    @Test
    public void trailingCRAtEndOfSourceDoesNotThrow() {
        ISource source = new Pos.Source("ab\r", null);
        int line = source.lineNumber(3); // pos == chars().length()
        Assert.assertEquals("the trailing \\r itself starts a new (empty) second line", 2, line);
    }

    @Test
    public void trailingCRLFAtEndOfSourceStillWorks() {
        // Sanity check the sibling case (pos-1 is \r, pos < length, and charAt(pos) really
        // is \n) still collapses \r\n into a single line increment, matching the fix's
        // added bounds check not changing this pre-existing, already-correct behavior.
        ISource source = new Pos.Source("ab\r\ncd", null);
        Assert.assertEquals(2, source.lineNumber(6));
    }
}
