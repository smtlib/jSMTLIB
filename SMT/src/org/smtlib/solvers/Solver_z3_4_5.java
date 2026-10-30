package org.smtlib.solvers;

import org.smtlib.IExpr;
import org.smtlib.IResponse;
import org.smtlib.SMT;

/** z3 4.5.0: as recent z3, except that it writes echo's text unquoted even with SMTLIB2_COMPLIANT
 *  (4.6 and later quote it), so where it ends cannot be found (#136); the response to echo is its
 *  argument */
public class Solver_z3_4_5 extends Solver_z3_recent {

    public Solver_z3_4_5(SMT.Configuration smtConfig, /*@NonNull*/ String executable) {
        super(smtConfig, executable);
    }

    public Solver_z3_4_5(SMT.Configuration smtConfig, /*@NonNull*/ String[] command) {
        super(smtConfig, command);
    }

    /** z3 4.5 reports the get- commands after a declare or define itself, except after declare-datatype(s)
     *  (probed 2026-10-29) */
    @Override
    protected java.util.Set<StackChange> answeredAfter() {
        return java.util.EnumSet.of(StackChange.DECLARE_DATATYPE);
    }

    @Override
    public IResponse echo(IExpr.IStringLiteral arg) {
        linesOffset--; // not sent (see linesOffset)
        return arg;
    }
}
