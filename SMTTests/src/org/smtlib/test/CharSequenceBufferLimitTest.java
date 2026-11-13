package org.smtlib.test;

import java.io.IOException;
import java.io.StringReader;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.CharSequenceInfinite;
import org.smtlib.CharSequenceReader;

/** CharSequenceInfinite's buffer growth (#192 item 14): sizes are computed without int overflow and capped at
 *  maxBufferSize, here lowered so the limit is reached; input beyond it is an error, not a crash. */
public class CharSequenceBufferLimitTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    /** A reader of text with a 10-char initial buffer, the given growth factor, and the given maximum */
    static class Limited extends CharSequenceReader {
        Limited(String text, double sizeMultiple, int max) {
            super(new StringReader(text), 10, 0, sizeMultiple);
            maxBufferSize = max;
        }

        int bufferLength() {
            return buf.length;
        }
    }

    private static String chars(int n) {
        return "a".repeat(n);
    }

    @Test
    public void growsUpToTheLimit() {
        Limited r = new Limited(chars(100), 2, 50);
        Assert.assertEquals('a', r.charAt(15)); // needs 17: 10 -> 20
        Assert.assertEquals(20, r.bufferLength());
        Assert.assertEquals('a', r.charAt(47)); // needs 49: 20 -> 40 -> 80, capped at 50
        Assert.assertEquals(50, r.bufferLength());
    }

    /** newlength*sizeMultiple+sizeIncrease beyond int range, beyond long range, or infinite, is capped at the
     *  maximum, not wrapped or saturated to Integer.MAX_VALUE */
    @Test
    public void hugeGrowthFactorIsCapped() {
        for (double factor: new double[] {1e12, 1e300, Double.POSITIVE_INFINITY}) {
            Limited r = new Limited(chars(100), factor, 50);
            Assert.assertEquals("factor " + factor, 'a', r.charAt(15));
            Assert.assertEquals("factor " + factor, 50, r.bufferLength());
        }
    }

    @Test
    public void beyondTheLimitIsAnError() {
        Limited r = new Limited(chars(100), 2, 50);
        try {
            r.charAt(60);
            Assert.fail("expected an error beyond the maximum buffer size");
        } catch (RuntimeException e) {
            Assert.assertTrue(String.valueOf(e.getCause()), e.getCause() instanceof IOException
                    && e.getCause().getMessage().equals("The input is longer than the allowed maximum of 50 characters"));
        }
    }

    /** An index near Integer.MAX_VALUE (index + 2 would wrap) is an error too */
    @Test
    public void indexNearIntMaxIsAnError() {
        Limited r = new Limited(chars(100), 2, 50);
        try {
            r.charAt(Integer.MAX_VALUE - 1);
            Assert.fail("expected an error beyond the maximum buffer size");
        } catch (RuntimeException e) {
            Assert.assertTrue(String.valueOf(e.getCause()), e.getCause() instanceof IOException);
        }
    }

    @Test
    public void endOfInputWithinTheLimit() {
        Limited r = new Limited(chars(30), 2, 50);
        Assert.assertEquals(CharSequenceInfinite.endChar, r.charAt(40));
        Assert.assertEquals(31, r.length());
    }

    @Test
    public void defaultLimitIsTheLargestSafeArray() {
        CharSequenceReader r = new CharSequenceReader(new StringReader("")) {
            { Assert.assertEquals(Integer.MAX_VALUE - 8, maxBufferSize); }
        };
        Assert.assertEquals(Integer.MAX_VALUE - 8, CharSequenceInfinite.MAX_BUFFER_SIZE);
        Assert.assertNotNull(r);
    }
}
