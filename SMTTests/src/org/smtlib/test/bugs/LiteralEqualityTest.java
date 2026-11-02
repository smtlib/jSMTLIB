package org.smtlib.test.bugs;

import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.IExpr;
import org.smtlib.SMT;

/**
 * Binary and hex literals are bit-vectors whose width is their digit count, so equal literals have the
 * same width and value: #b01 differs from #b1 and #x00 from #x0. Hex digits are case-insensitive, so
 * #x0A equals #x0a, with an equal hash code.
 * <p>
 * A JUnit test because it checks equals/hashCode, which no script output observes.
 */
public class LiteralEqualityTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    private final SMT.Configuration config = new SMT.Configuration();

    private IExpr.IBinaryLiteral bin(String digits) { return config.exprFactory.binary(digits); }

    private IExpr.IHexLiteral hex(String digits) { return config.exprFactory.hex(digits); }

    private static void assertEqualWithHash(Object a, Object b) {
        Assert.assertEquals(a, b);
        Assert.assertEquals(b, a);
        Assert.assertEquals(a.hashCode(), b.hashCode());
    }

    @Test
    public void binaryWidthMatters() {
        Assert.assertNotEquals(bin("01"), bin("1"));
        Assert.assertNotEquals(bin("1"), bin("01"));
        Assert.assertNotEquals(bin("000"), bin("0"));
    }

    @Test
    public void binarySameDigitsEqual() {
        assertEqualWithHash(bin("0101"), bin("0101"));
        Assert.assertNotEquals(bin("0101"), bin("0110"));
    }

    @Test
    public void hexWidthMatters() {
        Assert.assertNotEquals(hex("00"), hex("0"));
        Assert.assertNotEquals(hex("0A"), hex("a"));
        Assert.assertNotEquals(hex("a"), hex("0A"));
    }

    @Test
    public void hexCaseInsensitive() {
        assertEqualWithHash(hex("0A"), hex("0a"));
        assertEqualWithHash(hex("DeadBeef"), hex("deadBEEF"));
        Assert.assertNotEquals(hex("0A"), hex("0B"));
    }

    @Test
    public void binaryAndHexDiffer() {
        // #b1010 and #xa have the same value but are different literals
        Assert.assertNotEquals(bin("1010"), hex("a"));
        Assert.assertNotEquals(hex("a"), bin("1010"));
    }
}
