package org.smtlib.test.bugs;

import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.SMT;
import org.smtlib.command.C_declare_const;

/**
 * Pins down issue #39: {@code C_declare_const.java:32}'s {@code emptyList} field is a
 * {@code static final private List<ISort>} backed by a mutable {@code LinkedList}, shared as
 * the "empty arg-sorts list" across every {@code C_declare_const} instance ever constructed in
 * the process. {@code C_declare_fun} (the superclass) stores the passed-in list by reference
 * with no defensive copy, so anything that ever mutates one {@code declare-const} command's
 * {@code argSorts()} list -- plausible, since similar sort-lists elsewhere in the codebase are
 * built and mutated via {@code List.add()}/{@code .remove()} -- silently corrupts the shared
 * list for every other {@code declare-const} command, past or future.
 * <p>
 * The sibling {@code C_define_const.java} gets this right for the same purpose:
 * {@code super(symbol, Collections.emptyList(), resultSort, expression)} -- an immutable empty
 * list, safe to alias.
 * <p>
 * Fixed by using {@code Collections.emptyList()} in {@code C_declare_const} too.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/39">issue #39</a>.
 * <p>
 * Stays a JUnit test: no parsed script command ever mutates a command object's own
 * {@code argSorts()} list after construction, so the only way to observe whether two
 * instances share a backing list is to construct them directly and mutate one by hand.
 */
public class DeclareConstSharedEmptyListBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    @Test
    public void mutatingOneInstancesArgSortsDoesNotCorruptAnother() {
        SMT.Configuration config = new SMT.Configuration();
        C_declare_const first = new C_declare_const(
                config.exprFactory.symbol("a"), config.sortFactory.Bool());
        C_declare_const second = new C_declare_const(
                config.exprFactory.symbol("b"), config.sortFactory.Bool());

        Assert.assertTrue("sanity check: a fresh declare-const has no argument sorts",
                first.argSorts().isEmpty());

        boolean mutable = true;
        try {
            first.argSorts().add(config.sortFactory.Bool());
        } catch (UnsupportedOperationException e) {
            mutable = false;
        }

        if (mutable) {
            Assert.assertTrue(
                    "mutating one declare-const's (empty) argSorts() list must not affect "
                    + "another instance's -- they must not share a mutable backing list",
                    second.argSorts().isEmpty());
        }
        // If argSorts() is properly immutable (Collections.emptyList()), the mutation attempt
        // itself throwing is the fix working as intended -- nothing further to check.
    }
}
