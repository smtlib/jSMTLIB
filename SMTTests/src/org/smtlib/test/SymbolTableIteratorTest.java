package org.smtlib.test;

import java.util.NoSuchElementException;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.SMT;
import org.smtlib.SymbolTable;

/** {@link SymbolTable.Iterator}'s next() past the end, which a for-each traversal (the only way the
 *  iterator is otherwise used) never reaches. remove() is java.util.Iterator's default, which
 *  throws UnsupportedOperationException (#146). */
public class SymbolTableIteratorTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    @Test
    public void nextPastEndThrows() {
        SymbolTable table = new SymbolTable(new SMT.Configuration());
        SymbolTable.Iterator it = table.iterator();
        Assert.assertFalse("a freshly-constructed SymbolTable should have nothing to iterate", it.hasNext());
        try {
            it.next();
            Assert.fail("next() past the end should throw NoSuchElementException");
        } catch (NoSuchElementException e) {
            // expected
        }
    }
}
