package org.smtlib.test.bugs;

import java.util.Collections;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.IExpr;
import org.smtlib.IParser;
import org.smtlib.ISource;
import org.smtlib.IVisitor;
import org.smtlib.SMT;
import org.smtlib.logic.QF_IDL;

/**
 * Pins down {@code QF_IDL.validExpression()}'s shape-restriction visitor (QF_IDL.java:22-71):
 * its {@code visit(IExpr.IFcnExpr)} override returned immediately for {@code and}/{@code or}/
 * {@code not}/{@code implies} without recursing into their arguments -- since {@code TypeChecker}
 * calls {@code validExpression()} exactly once on the whole top-level formula, and this override
 * completely replaces the default {@code IVisitor.TreeVisitor} traversal for {@code IFcnExpr}
 * (rather than delegating to it), matching the *outer* connective ended the check right there.
 * Nested atoms -- the normal case for any real IDL formula -- never got validated.
 * <p>
 * The repo's own {@code SMTTests/tests/logics/QF_IDL/err_QF_IDL_diffArgsSymbol.tst} already
 * establishes that {@code (>= (- x 1) y)} is an invalid IDL atom (a difference's arguments must
 * both be symbols, not a symbol and a numeral); this test nests that exact same invalid atom one
 * level inside an {@code and} and confirms it is still caught. {@code =}/{@code distinct} are
 * deliberately left alone here (and by the fix) -- they're already covered by their own,
 * separate FIXME in the same file, since naively recursing into their arguments would
 * mis-validate an arithmetic equality's non-Boolean operands.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/44">issue #44</a>.
 */
public class QF_IDLNestedAtomRecursionBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    private IExpr parse(SMT.Configuration config, String text) throws Exception {
        ISource source = config.smtFactory.createSource(text, null);
        IParser p = new org.smtlib.sexpr.Parser(config, source);
        return p.parseExpr();
    }

    @Test
    public void invalidAtomNestedInsideAndIsRejected() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        QF_IDL logic = new QF_IDL(config, config.exprFactory.symbol("QF_IDL"), Collections.emptyList());

        // Outer "and"'s first argument is a valid IDL atom; the second, (>= (- x 1) y), is
        // invalid (a difference's arguments must both be symbols) -- but only reachable by
        // recursing into the "and".
        IExpr expr = parse(config, "(and (>= x y) (>= (- x 1) y))");

        try {
            logic.validExpression(expr);
            Assert.fail("expected a VisitorException for the invalid atom nested inside \"and\"");
        } catch (IVisitor.VisitorException expected) {
            // OK
        }
    }
}
