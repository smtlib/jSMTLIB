package org.smtlib.test;

import java.util.List;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.IExpr;
import org.smtlib.ISort;
import org.smtlib.SMT;
import org.smtlib.SymbolTable;
import org.smtlib.Utils;

/**
 * Demonstrates that sort_symbol_decl attributes now survive into the symbol table.
 * HO-Core.smt2 declares ":sorts ( (-> 2 :right-assoc) )", but Utils.loadTheory's :sorts
 * loop used to read only the name and arity of each declaration and silently drop any
 * trailing attribute* -- ISort.IFamily had no attributes() at all. This checks the fix
 * end to end: load the theory by name (the same path set-logic uses), then confirm the
 * resulting ISort.IFamily for -> carries the :right-assoc attribute.
 */
public class SortAttributeTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    @Test
    public void arrowSortCarriesRightAssocAttribute() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        SymbolTable symTable = new SymbolTable(config);
        Utils utils = new Utils(config);

        Assert.assertNull(utils.loadTheory("HO-Core", symTable));

        ISort.IDefinition def = symTable.lookupSort(config.exprFactory.symbol("->"));
        Assert.assertTrue(def instanceof ISort.IFamily);
        List<IExpr.IAttribute<?>> attrs = ((ISort.IFamily) def).attributes();
        Assert.assertEquals(1, attrs.size());
        Assert.assertEquals(":right-assoc", attrs.get(0).keyword().value());
    }

    @Test
    public void sortWithNoAttributesHasEmptyList() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        SymbolTable symTable = new SymbolTable(config);
        Utils utils = new Utils(config);

        Assert.assertNull(utils.loadTheory("Core", symTable));

        ISort.IDefinition def = symTable.lookupSort(config.exprFactory.symbol("Bool"));
        Assert.assertTrue(def instanceof ISort.IFamily);
        Assert.assertTrue(((ISort.IFamily) def).attributes().isEmpty());
    }
}
