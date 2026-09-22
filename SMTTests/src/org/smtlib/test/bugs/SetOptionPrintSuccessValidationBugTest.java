package org.smtlib.test.bugs;

import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.IAttributeValue;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IParser;
import org.smtlib.IResponse;
import org.smtlib.ISource;
import org.smtlib.SMT;
import org.smtlib.solvers.Solver_bitwuzla;
import org.smtlib.solvers.Solver_test;

/**
 * Pins down issue #41's concrete, demonstrated gap: {@code C_set_option.checkOptionType()}
 * (parse-time) was the *only* place a bad {@code :print-success} value was ever rejected.
 * {@code smtConfig.commandFactory.set_option(key,value)} constructs a {@code C_set_option}
 * directly, bypassing that parse-time check -- and {@code AbstractSolver#set_option_impl()}
 * itself calls exactly that factory method -- yet both execute-time siblings had their own
 * validation either disabled or too loose to catch it:
 * <ul>
 * <li>{@code Solver_test.set_option()}'s own check was commented out, with a comment noting
 * it was "duplicated in the C_set_option constructor" -- assuming parse-time always ran
 * first, which isn't true for this path.
 * <li>{@code AbstractSolver#checkPrintSuccess()} (used by every real solver adapter that
 * doesn't override {@code set_option_impl()} with its own guard -- confirmed bitwuzla is
 * one; {@code Solver_z3_4_3} happens to have its own independent, already-correct check
 * ahead of it, so it was never actually vulnerable) did {@code smtConfig.nosuccess =
 * !value.toString().equals("true")}: no validation at all, silently treating anything that
 * isn't literally {@code "true"} as {@code false}.
 * </ul>
 * Fixed by giving both execute-time paths their own proper validation (matching
 * {@code C_set_option}'s own check), instead of assuming the other layer already ran.
 * Reproduced by calling {@code set_option()} directly, bypassing {@code C_set_option.parse()}
 * entirely -- exactly the path {@code smtConfig.commandFactory.set_option(...)} takes.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/41">issue #41</a>.
 * <p>
 * Stays a JUnit test: as the class doc already notes, {@code C_set_option.parse()} already
 * rejects a bad {@code :print-success} value eagerly for any text-driven script -- the bypass
 * path this pins down ({@code smtConfig.commandFactory.set_option(key,value)} called directly)
 * is only reachable via direct API use, never through parsed script text.
 */
public class SetOptionPrintSuccessValidationBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    private IKeyword printSuccessKeyword(SMT.Configuration config) throws Exception {
        ISource source = config.smtFactory.createSource(":print-success", null);
        IParser p = new org.smtlib.sexpr.Parser(config, source);
        return p.parseKeyword();
    }

    private IAttributeValue numeralValue(SMT.Configuration config) throws Exception {
        ISource source = config.smtFactory.createSource("5", null);
        IParser p = new org.smtlib.sexpr.Parser(config, source);
        return p.parseAttributeValue();
    }

    private IAttributeValue booleanValue(SMT.Configuration config, boolean b) throws Exception {
        ISource source = config.smtFactory.createSource(b ? "true" : "false", null);
        IParser p = new org.smtlib.sexpr.Parser(config, source);
        return p.parseAttributeValue();
    }

    @Test
    public void solverTestRejectsNonBooleanPrintSuccessBypassingParse() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        Solver_test solver = new Solver_test(config, "test");

        // Calling set_option() directly -- not through C_set_option.parse() -- matching
        // what smtConfig.commandFactory.set_option(key,value) does.
        IResponse r = solver.set_option(printSuccessKeyword(config), numeralValue(config));
        Assert.assertTrue("a non-boolean :print-success value must be rejected, not silently "
                + "ignored", r.isError());
    }

    @Test
    public void solverTestStillAcceptsValidPrintSuccessValues() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        Solver_test solver = new Solver_test(config, "test");

        Assert.assertFalse(solver.set_option(printSuccessKeyword(config), booleanValue(config, true)).isError());
        Assert.assertFalse(solver.set_option(printSuccessKeyword(config), booleanValue(config, false)).isError());
    }

    @Test
    public void realSolverAdapterRejectsNonBooleanPrintSuccessBypassingParse() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        // Solver_bitwuzla's own set_option_impl() calls checkPrintSuccess() directly with
        // no additional guard of its own (unlike e.g. Solver_z3_4_3, which happens to have
        // its own independent, already-correct check) -- so this genuinely exercises
        // AbstractSolver's default, exactly as every adapter without its own override does.
        // :print-success is handled entirely client-side, so this never touches a live
        // process.
        Solver_bitwuzla solver = new Solver_bitwuzla(config, "bitwuzla");

        IResponse r = solver.set_option(printSuccessKeyword(config), numeralValue(config));
        Assert.assertTrue("a non-boolean :print-success value must be rejected, not silently "
                + "treated as false", r.isError());
    }

    @Test
    public void realSolverAdapterStillAcceptsValidPrintSuccessValues() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        Solver_bitwuzla solver = new Solver_bitwuzla(config, "bitwuzla");

        Assert.assertFalse(solver.set_option(printSuccessKeyword(config), booleanValue(config, true)).isError());
        Assert.assertFalse(solver.set_option(printSuccessKeyword(config), booleanValue(config, false)).isError());
    }
}
