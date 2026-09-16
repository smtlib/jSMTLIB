package org.smtlib.test.bugs;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.Utils;

/**
 * Pins down Utils.java:1075-1088's {@code cat(T[]... arrays)}: it builds the result array
 * via {@code Array.newInstance(arrays[0].getClass(), n)} -- since arrays[0] is itself a
 * {@code T[]}, this creates a 2-D array, not a flat one. The sibling overload
 * (Utils.java:1093, {@code cat(T[] aa, T... rest)}) does this correctly via
 * {@code aa[0].getClass()}, i.e. the *element* type, not the array type. This overload is
 * currently dead code in the rest of the codebase (only the sibling is ever called), so it
 * is invoked here via reflection, keyed on its erased parameter type ({@code Object[][]}, a
 * single varargs parameter) to select it unambiguously over the two-parameter sibling
 * overload ({@code Object[], Object[]}, after erasure).
 * <p>
 * Asserts the correct, flat concatenation. This currently FAILS against today's code (an
 * ArrayStoreException from copying String elements into a String[][]-shaped destination),
 * documenting the bug.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/27">issue #27</a>.
 */
public class UtilsCatArraysBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    @Test
    public void catConcatenatesArraysFlatNotNested() throws Exception {
        Method catArrays = Utils.class.getMethod("cat", Object[][].class);
        String[] a = { "a", "b" };
        String[] b = { "c" };
        Object[] invokeArgs = new Object[] { new String[][] { a, b } };

        Object result;
        try {
            result = catArrays.invoke(null, invokeArgs);
        } catch (InvocationTargetException e) {
            throw (Exception) e.getCause();
        }

        Assert.assertArrayEquals(new String[] { "a", "b", "c" }, (String[]) result);
    }
}
