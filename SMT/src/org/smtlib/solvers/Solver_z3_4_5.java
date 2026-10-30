package org.smtlib.solvers;

import org.smtlib.ICommand;
import org.smtlib.IExpr;
import org.smtlib.INode;
import org.smtlib.IResponse;
import org.smtlib.IVisitor;
import org.smtlib.SMT;

/** z3 4.5.0: as recent z3, except that it writes echo's text unquoted even with SMTLIB2_COMPLIANT
 *  (4.6 and later quote it), so where it ends cannot be found (#136), the response to echo is its
 *  argument; and it rejects every check-sat-assuming (see translate) */
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

    /** z3 4.5 rejects every check-sat-assuming ("invalid check-sat-assuming command, '(', expected", a
     *  parser bug), so it is sent as z3's legacy (check-sat a1 ... an), which checks under the same
     *  assumptions. Its unsat core then includes the assumptions, which Solver_z3_recent drops. */
    @Override
    protected String translate(INode node) throws IVisitor.VisitorException {
        if (node instanceof ICommand.Icheck_sat_assuming c) {
            StringBuilder sb = new StringBuilder("(check-sat");
            for (IExpr e : c.terms()) sb.append(' ').append(super.translate(e));
            return sb.append(')').toString();
        }
        return super.translate(node);
    }

    @Override
    public IResponse echo(IExpr.IStringLiteral arg) {
        linesOffset--; // not sent (see linesOffset)
        return arg;
    }
}
