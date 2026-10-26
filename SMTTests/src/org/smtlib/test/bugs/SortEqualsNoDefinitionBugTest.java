package org.smtlib.test.bugs;

import org.junit.Assert;
import org.junit.Test;
import org.smtlib.ISort;
import org.smtlib.SMT;

/** Regression test for #141: Sort.Application.equals() expanded the sort through its
 *  definition, and threw a NullPointerException for a sort with no definition attached
 *  (as one made directly by the sort factory has, before the type checker resolves it). */
public class SortEqualsNoDefinitionBugTest {

    @Test
    public void equalsWithoutDefinition() {
        SMT.Configuration config = new SMT().smtConfig;
        ISort u = config.sortFactory.createSortExpression(config.exprFactory.symbol("U"));
        ISort u2 = config.sortFactory.createSortExpression(config.exprFactory.symbol("U"));
        ISort v = config.sortFactory.createSortExpression(config.exprFactory.symbol("V"));
        Assert.assertTrue(u.equals(u2));
        Assert.assertFalse(u.equals(v));
        Assert.assertEquals(u.hashCode(), u2.hashCode());
    }
}
