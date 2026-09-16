package org.smtlib.test.bugs;

import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.ISource;
import org.smtlib.ITheory;
import org.smtlib.IParser;
import org.smtlib.IResponse;
import org.smtlib.SMT;
import org.smtlib.SymbolTable;
import org.smtlib.Utils;

/**
 * Pins down Utils.java's loadFuns()/loadParFun(): both assume every theory-file {@code :funs}
 * entry is well-formed. A malformed entry -- e.g. {@code (foo)}, a fun_symbol_decl with a
 * name but no sort at all -- throws an unchecked IndexOutOfBoundsException instead of a
 * graceful error:
 * <ul>
 * <li>{@code loadFuns()}'s per-entry loop collects declared sorts into a list until it hits
 * a keyword or runs out of tokens, then does {@code sorts.remove(sorts.size() - 1)} to split
 * off the trailing sort as the result sort. If no sorts were collected at all (a bare
 * {@code (name)} with nothing else), that list is empty and {@code remove(-1)} throws.
 * </ul>
 * This matters beyond the theory files bundled with jSMTLIB itself: {@code findTheory()} (and
 * so {@code loadFuns()}) is reachable from a user-supplied {@code --logics} directory (see
 * {@code Utils.openLogicStream()}'s explicit-path branch), so a hand-edited or generated
 * theory file with one malformed {@code :funs} entry can crash the whole run with an
 * uncaught RuntimeException, not a clean "ill-formed" error message the way the analogous
 * checks elsewhere in the same method (e.g. {@code loadParFun()}'s own well-formedness
 * checks) already do.
 * <p>
 * Reproduced directly against the public {@code Utils.loadTheory(ITheory, SymbolTable)}
 * entry point, parsing a small in-memory theory string rather than going through any file/
 * classpath machinery.
 * <p>
 * Asserts the correct behavior: a clean {@code IResponse.IError} instead of a thrown
 * exception. This currently FAILS against today's code (IndexOutOfBoundsException),
 * documenting the bug.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/31">issue #31</a>.
 */
public class UtilsLoadFunsBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    @Test
    public void funEntryWithNoSortAtAllReportsCleanError() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        Utils utils = new Utils(config);
        SymbolTable symTable = new SymbolTable(config);

        // "foo" has a name and nothing else -- no argument sorts, no result sort, no
        // attributes -- so loadFuns()'s sort-collecting loop never adds anything to `sorts`
        // before falling off the end of the declaration.
        String theoryText = "(theory Test :smt-lib-version 2.6 :funs ((foo)))";
        ISource source = config.smtFactory.createSource(theoryText, null);
        IParser p = new org.smtlib.sexpr.Parser(config, source);
        ITheory theory = p.parseTheory();

        IResponse response = utils.loadTheory(theory, symTable);

        Assert.assertTrue("expected a clean IResponse.IError, not a thrown exception",
                response instanceof IResponse.IError);
    }
}
