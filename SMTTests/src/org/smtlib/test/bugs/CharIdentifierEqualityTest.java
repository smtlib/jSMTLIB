package org.smtlib.test.bugs;

import java.util.Collections;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.IExpr;
import org.smtlib.IExpr.IIdentifier;
import org.smtlib.SMT;

/**
 * The Strings theory's (_ char H) constants: leading zeros in H don't change the code point, so
 * (_ char #x41) and (_ char #x041) are equal identifiers with equal hash codes, although their hex
 * literals differ. Other indexed identifiers compare their indices as written.
 * <p>
 * A JUnit test because it checks equals/hashCode, which no script output observes.
 */
public class CharIdentifierEqualityTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    private final SMT.Configuration config = new SMT.Configuration();

    private IIdentifier id(String head, IExpr.IIndex index) {
        return config.exprFactory.id(config.exprFactory.symbol(head), Collections.singletonList(index));
    }

    private IIdentifier hexId(String head, String digits) {
        return id(head, config.exprFactory.hex(digits));
    }

    @Test
    public void leadingZerosDontMatter() {
        IIdentifier a = hexId("char", "41");
        for (String digits : new String[] {"041", "0041", "00041"}) {
            IIdentifier b = hexId("char", digits);
            Assert.assertEquals(digits, a, b);
            Assert.assertEquals(digits, b, a);
            Assert.assertEquals(digits, a.hashCode(), b.hashCode());
        }
    }

    @Test
    public void caseDoesntMatter() {
        IIdentifier a = hexId("char", "2b");
        IIdentifier b = hexId("char", "2B");
        Assert.assertEquals(a, b);
        Assert.assertEquals(a.hashCode(), b.hashCode());
    }

    @Test
    public void differentCodePointsDiffer() {
        Assert.assertNotEquals(hexId("char", "41"), hexId("char", "42"));
    }

    @Test
    public void hexAndNumeralIndicesDiffer() {
        IIdentifier hex = hexId("char", "41");
        IIdentifier num = id("char", config.exprFactory.numeral(65));
        Assert.assertNotEquals(hex, num);
        Assert.assertNotEquals(num, hex);
    }

    @Test
    public void otherHeadsDiffer() {
        Assert.assertNotEquals(hexId("char", "41"), hexId("chr", "41"));
        Assert.assertNotEquals(hexId("chr", "41"), hexId("char", "41"));
    }
}
