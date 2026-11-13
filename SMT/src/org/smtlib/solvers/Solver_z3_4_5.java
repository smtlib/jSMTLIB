package org.smtlib.solvers;

import java.io.IOException;

import org.smtlib.ICommand;
import org.smtlib.IExpr;
import org.smtlib.INode;
import org.smtlib.IResponse;
import org.smtlib.IVisitor;
import org.smtlib.SMT;

/** z3 4.5.0: as recent z3, except that it writes echo's text unquoted even with SMTLIB2_COMPLIANT
 *  (4.6 and later quote it), so where it ends cannot be found (#136), the response to echo is its
 *  argument; it rejects every check-sat-assuming (see translate); and it writes nothing for
 *  reset-assertions and a malformed reply for an invalid get-info :reason-unknown (#210) */
public class Solver_z3_4_5 extends Solver_z3_recent {

    public Solver_z3_4_5(SMT.Configuration smtConfig, /*@NonNull*/ String executable) {
        super(smtConfig, executable);
    }

    public Solver_z3_4_5(SMT.Configuration smtConfig, /*@NonNull*/ String[] command) {
        super(smtConfig, command);
    }

    /** As every z3 before 5.1.0 (#196) */
    @Override
    protected boolean columnsHigherAfterComment() {
        return true;
    }

    /** z3 4.5 reports the get- commands after a declare or define itself, except after declare-datatype(s)
     *  (probed 2026-10-29) */
    @Override
    protected java.util.Set<StackChange> answeredAfter() {
        return java.util.EnumSet.of(StackChange.DECLARE_DATATYPE);
    }

    /** z3 4.5 rejects every check-sat-assuming ("invalid check-sat-assuming command, '(', expected", a
     *  parser bug), so it is sent as z3's legacy (check-sat a1 ... an), which checks under the same
     *  assumptions, padded with spaces so z3's error columns match the check-sat-assuming text (see
     *  Solver_z3_recent.legacyCheckSat). Its unsat core then includes the assumptions, which
     *  Solver_z3_recent drops. */
    @Override
    protected String translate(INode node) throws IVisitor.VisitorException {
        String s = super.translate(node);
        return node instanceof ICommand.Icheck_sat_assuming ? legacyCheckSat(s) : s;
    }

    @Override
    public IResponse echo(IExpr.IStringLiteral arg) {
        return arg;
    }

    /** z3 4.5.0 performs reset-assertions but writes nothing for it, even with :print-success (#210), so
     *  the command is sent without waiting for a reply and answered success here; the next reply read is
     *  then the next command's */
    @Override
    public IResponse reset_assertions() {
        IResponse exited = exitedResponse();
        if (exited != null) return exited;
        try {
            sendScriptText(false, translate(smtConfig.commandFactory.reset_assertions()), "\n");
        } catch (IOException e) {
            return sendFailure("Error writing to Z3 solver:", e);
        } catch (IVisitor.VisitorException e) {
            return smtConfig.responseFactory.error(e.getMessage());
        }
        return recordChange(StackChange.RESET_ASSERTIONS, smtConfig.responseFactory.success());
    }

    /** z3 4.5.0 answers get-info :reason-unknown, when the most recent check-sat did not return unknown,
     *  with (:reason-unknown "(error "...")", whose quotes never balance, so reading it never ends (#210).
     *  That case is answered here with the error it carries; after an unknown, z3 answers properly. */
    @Override
    public IResponse get_info(IExpr.IKeyword key) {
        if (":reason-unknown".equals(key.value()) && !smtConfig.responseFactory.unknown().equals(checkStatus())) {
            return smtConfig.responseFactory.error("state of the most recent check-sat command is not known");
        }
        return super.get_info(key);
    }
}
