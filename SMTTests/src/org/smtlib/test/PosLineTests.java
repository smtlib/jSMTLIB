package org.smtlib.test;

import org.junit.Assert;
import org.junit.Test;
import org.smtlib.ISource;
import org.smtlib.impl.Pos;

/** Pos.Source.lineBeginning and textLine: a line terminator belongs to the line it ends (#192 item 15) */
public class PosLineTests {

    private static ISource source(String text) {
        return new Pos.Source(text, null);
    }

    @Test
    public void midLine() {
        Assert.assertEquals(3, source("ab\ncde\n").lineBeginning(5));
    }

    @Test
    public void onLineFeed() {
        // position 6 is the \n ending "cde"
        Assert.assertEquals(3, source("ab\ncde\nf").lineBeginning(6));
        Assert.assertEquals("cde\n", source("ab\ncde\nf").textLine(6));
    }

    @Test
    public void onCarriageReturnLineFeed() {
        // positions 7 and 8 are the \r\n ending "cde"
        Assert.assertEquals(4, source("ab\r\ncde\r\nf").lineBeginning(7));
        Assert.assertEquals(4, source("ab\r\ncde\r\nf").lineBeginning(8));
    }

    @Test
    public void emptyLine() {
        // position 3 is the \n ending the empty second line
        Assert.assertEquals(3, source("ab\n\nc").lineBeginning(3));
    }

    @Test
    public void firstLine() {
        Assert.assertEquals(0, source("ab\ncd").lineBeginning(2));
        Assert.assertEquals(0, source("ab\ncd").lineBeginning(0));
    }
}
