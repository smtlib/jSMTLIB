package org.smtlib.test.bugs;

import java.io.StringReader;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.CharSequenceReader;

/**
 * Pins down {@code CharSequenceInfinite.subSequence(start, end)}:
 *
 * <pre>public CharSequence subSequence(int start, int end) {
 *     charAt(end-1); // Just to be sure it has been read  // FIXME - what if start == end == 0, or values are negative
 *     return CharBuffer.wrap(buf,start,end-start);
 * }</pre>
 *
 * {@code subSequence(0, 0)} -- a legal empty subsequence per the {@code CharSequence}
 * contract (any {@code 0 <= start <= end <= length()} is valid, including
 * {@code start == end}) -- called {@code charAt(end-1)} = {@code charAt(-1)}.
 * {@code charAt(int index)}'s own bounds logic ({@code if (index >= amountRead) { ... }})
 * doesn't treat a negative index as needing more input ({@code -1 >= amountRead} is false
 * when nothing has been read yet), so it fell through to {@code return buf[index];} =
 * {@code buf[-1]}, throwing {@code ArrayIndexOutOfBoundsException}. Already flagged by the
 * code's own FIXME on the same line.
 * <p>
 * Fixed by skipping the "ensure read" priming call when {@code start == end} -- nothing
 * needs to have been read to return an empty subsequence.
 * <p>
 * Uses {@code CharSequenceReader} (a concrete subclass) since {@code CharSequenceInfinite}
 * itself is abstract.
 */
public class CharSequenceInfiniteSubSequenceBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    @Test
    public void emptySubSequenceAtStartDoesNotThrow() throws Exception {
        CharSequenceReader csr = new CharSequenceReader(new StringReader("abc"), 100, 0, 2);

        CharSequence sub = csr.subSequence(0, 0);

        Assert.assertEquals(0, sub.length());
    }
}
