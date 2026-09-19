package org.smtlib.test.bugs;

import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.ICommand;
import org.smtlib.IParser;
import org.smtlib.IResponse;
import org.smtlib.ISource;
import org.smtlib.SMT;
import org.smtlib.solvers.Solver_simplify;

/**
 * Resolves issue #68's hygiene items in {@code Solver_simplify.java}:
 * <ul>
 * <li>Removed three redundant overrides ({@code get_assertions}, {@code set_info}, and
 * {@code get_value} -- the last a word-for-word duplicate of {@code Solver_test.get_value()},
 * not merely a one-line passthrough) that the class's own "Pure overrides are redundant"
 * comment already anticipated removing. Behaviorally identical either way, since
 * {@code Solver_simplify extends Solver_test}.
 * <li>Fixed a copy-pasted error message in {@code define_fun}'s catch blocks that said
 * "Failed to declare-fun" (the wrong command name) -- a plain text correction, not covered
 * by a dedicated test here since those catch blocks only fire on an actual IOException/
 * VisitorException thrown while translating to Simplify's syntax, not on the ordinary
 * ill-typed-definition path issue #55's test already exercises.
 * <li>Consolidated four near-duplicate {@code // FIXME - check for error in s} markers into
 * one explanation in the class doc comment, rather than resolving them with unverified
 * protocol-parsing logic (no live Simplify binary or documented response format available).
 * </ul>
 * This is a characterization test -- none of the above changes observable behavior, so
 * every assertion here already held before the cleanup too.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/68">issue #68</a>.
 */
public class SolverSimplifyHygieneCleanupBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    private IResponse doCommand(SMT.Configuration config, Solver_simplify solver, String text) throws Exception {
        ISource source = config.smtFactory.createSource(text, null);
        IParser p = new org.smtlib.sexpr.Parser(config, source);
        ICommand cmd = p.parseCommand();
        return cmd.execute(solver);
    }

    @Test
    public void getAssertionsStillWorks() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        Solver_simplify solver = new Solver_simplify(config, "simplify");
        doCommand(config, solver, "(set-option :produce-assertions true)");
        doCommand(config, solver, "(set-logic QF_UF)");
        doCommand(config, solver, "(assert true)");

        IResponse r = doCommand(config, solver, "(get-assertions)");
        Assert.assertFalse(r.isError());
    }

    @Test
    public void setInfoStillWorks() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        Solver_simplify solver = new Solver_simplify(config, "simplify");

        IResponse r = doCommand(config, solver, "(set-info :source |test|)");
        Assert.assertFalse(r.isError());
    }

    @Test
    public void getValueStillReportsProduceModelsNotEnabled() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        Solver_simplify solver = new Solver_simplify(config, "simplify");
        doCommand(config, solver, "(set-logic QF_UF)");
        doCommand(config, solver, "(declare-const x Bool)");

        IResponse r = doCommand(config, solver, "(get-value (x))");
        Assert.assertTrue(r.isError());
        Assert.assertTrue(((IResponse.IError) r).errorMsg().contains("produce-models"));
    }
}
