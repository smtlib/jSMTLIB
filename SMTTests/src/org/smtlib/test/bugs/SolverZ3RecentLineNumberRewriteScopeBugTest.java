package org.smtlib.test.bugs;

import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.IResponse;
import org.smtlib.SMT;
import org.smtlib.solvers.Solver_z3_recent;

/**
 * Pins down issue #59: {@code Solver_z3_recent.parseResponse()} (Solver_z3_recent.java:108-120)
 * rewrote every occurrence of the pattern {@code line (\d+)} anywhere in the *entire* response
 * string to compensate for {@code linesOffset} (extra lines jSMTLIB prepends before the user's
 * script, e.g. a print-success priming command) -- not scoped to error text specifically. A
 * response that happens to contain a coincidentally-matching token elsewhere (e.g. inside a
 * returned string literal) would be mis-rewritten even though it was never a genuine z3 line
 * reference.
 * <p>
 * Fixed by scoping the rewrite to responses that actually carry an {@code (error ...)}, since
 * z3 only ever reports a line number inside an error response.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/59">issue #59</a>.
 */
public class SolverZ3RecentLineNumberRewriteScopeBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    /** Exposes the protected parseResponse()/linesOffset for direct testing, without ever
     *  starting a real z3 process (the constructor only builds a SolverProcess object). */
    static class TestableSolver extends Solver_z3_recent {
        TestableSolver(SMT.Configuration config) {
            super(config, "z3");
            linesOffset = 1;
        }
        IResponse callParseResponse(String response) {
            return parseResponse(response);
        }
    }

    @Test
    public void lineReferenceInsideAnErrorIsStillCompensated() {
        SMT.Configuration config = new SMT.Configuration();
        TestableSolver solver = new TestableSolver(config);

        IResponse r = solver.callParseResponse("(error \"line 5 column 2: foo\")");
        Assert.assertTrue(r.isError());
        Assert.assertEquals("line 4 column 2: foo", ((IResponse.IError) r).errorMsg());
    }

    @Test
    public void coincidentalLineTextOutsideAnErrorIsNotRewritten() {
        SMT.Configuration config = new SMT.Configuration();
        TestableSolver solver = new TestableSolver(config);

        // A get-value-style response whose returned string value happens to contain text
        // matching "line N" -- not a genuine z3 source-line reference, so linesOffset must
        // not touch it.
        String response = "((x \"line 5 of the report\"))";
        IResponse r = solver.callParseResponse(response);

        Assert.assertFalse(r.isError());
        Assert.assertTrue("the coincidental \"line 5\" text must be left untouched",
                config.defaultPrinter.toString(r).contains("line 5 of the report"));
    }
}
