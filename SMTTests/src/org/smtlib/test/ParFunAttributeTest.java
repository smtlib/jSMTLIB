package org.smtlib.test;

import java.util.List;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.ISort;
import org.smtlib.SMT;
import org.smtlib.SymbolTable;
import org.smtlib.SymbolTable.Entry;
import org.smtlib.Utils;

/**
 * Demonstrates that par_fun_symbol_decl declarations (( par ( symbol+ ) ( identifier sort+
 * attribute* ) )) now register a real, parameterized SymbolTable.Entry instead of being
 * silently skipped -- Utils.loadFuns used to just `continue` past any :funs entry starting
 * with "par" (no par-polymorphic function support existed at all), which is why @, select,
 * and store all needed hardcoded special-casing in TypeChecker instead of going through the
 * normal SymbolTable.lookup() path. Parallel to SortAttributeTest, which covers the same gap
 * for sort_symbol_decl.
 */
public class ParFunAttributeTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    private SMT.Configuration config;
    private SymbolTable symTable;

    private Entry soleEntry(String name, int arity) {
        List<Entry> entrylist = symTable.lookup(config.exprFactory.symbol(name));
        Assert.assertNotNull(name + " not found in symbol table", entrylist);
        List<Entry> entries = new java.util.ArrayList<>();
        for (Entry e : entrylist) {
            if (e.sort.argSorts().length == arity) entries.add(e);
        }
        Assert.assertFalse(name + " has no arity-" + arity + " entry", entries.isEmpty());
        Assert.assertEquals(1, entries.size());
        return entries.get(0);
    }

    @Test
    public void selectAndStoreCarryParameters() throws Exception {
        config = new SMT.Configuration();
        symTable = new SymbolTable(config);
        Utils utils = new Utils(config);

        Assert.assertNull(utils.loadTheory("ArraysEx", symTable));

        // (select (Array X Y) X Y): domain sorts [(Array X Y), X], result Y.
        Entry select = soleEntry("select", 2);
        Assert.assertNotNull(select.parameters);
        Assert.assertEquals(2, select.parameters.size());
        ISort.IParameter x = select.parameters.get(0);
        ISort.IParameter y = select.parameters.get(1);
        Assert.assertTrue(select.sort.argSorts()[0] instanceof ISort.IApplication);
        ISort.IApplication arraySort = (ISort.IApplication) select.sort.argSorts()[0];
        // The (Array X Y) argument must be built from the very same X/Y parameter objects
        // declared for select, not merely distinct placeholders with matching names --
        // IParameter.equals() is identity-based, so this also confirms the parameter scope
        // used while resolving the whole declaration was shared, not re-pushed per sort.
        Assert.assertEquals(x, arraySort.param(0));
        Assert.assertEquals(y, arraySort.param(1));
        Assert.assertEquals(x, select.sort.argSorts()[1]);
        Assert.assertEquals(y, select.sort.resultSort());

        // (store (Array X Y) X Y (Array X Y)): domain sorts [(Array X Y), X, Y], result (Array X Y).
        Entry store = soleEntry("store", 3);
        Assert.assertNotNull(store.parameters);
        Assert.assertEquals(2, store.parameters.size());
    }

    @Test
    public void hoCoreAtCarriesLeftAssocAttributeAndParameters() throws Exception {
        config = new SMT.Configuration();
        symTable = new SymbolTable(config);
        Utils utils = new Utils(config);

        Assert.assertNull(utils.loadTheory("HO-Core", symTable));

        // (@ (-> A B) A B :left-assoc): domain sorts [(-> A B), A], result B, attrs [:left-assoc].
        Entry at = soleEntry("@", 2);
        Assert.assertNotNull(at.parameters);
        Assert.assertEquals(2, at.parameters.size());
        Assert.assertNotNull(at.attributes);
        Assert.assertEquals(1, at.attributes.size());
        Assert.assertEquals(":left-assoc", at.attributes.get(0).keyword().value());

        ISort.IParameter a = at.parameters.get(0);
        ISort.IParameter b = at.parameters.get(1);
        Assert.assertTrue(at.sort.argSorts()[0] instanceof ISort.IApplication);
        ISort.IApplication arrowSort = (ISort.IApplication) at.sort.argSorts()[0];
        Assert.assertEquals(a, arrowSort.param(0));
        Assert.assertEquals(b, arrowSort.param(1));
        Assert.assertEquals(a, at.sort.argSorts()[1]);
        Assert.assertEquals(b, at.sort.resultSort());
    }
}
