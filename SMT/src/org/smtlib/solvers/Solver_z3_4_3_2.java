/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.solvers;

import org.smtlib.IAttributeValue;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IResponse;
import org.smtlib.SMT;
import org.smtlib.SMT.Configuration;

/**
 *  This is a special handler for Z3 4.3.2, as opposed to other revisions of Z3 4.3.
 *  
 *  @see Solver_z3_4_3
 */
public class Solver_z3_4_3_2 extends Solver_z3_4_3 {

    @Override
    protected String name() { return "z3-4.3.2"; }

    public Solver_z3_4_3_2(Configuration smtConfig, String executable) {
        super(smtConfig, executable);
    }

    /** Launches the given command as is (a .command property, #147), without adding the flags
     *  the executable form adds */
    public Solver_z3_4_3_2(Configuration smtConfig, String[] command) {
        super(smtConfig, command);
    }

    /** z3 4.3.2 answers set-option of an option it does not know with an error ("unknown parameter", followed by
     *  the list of its parameters), where SMT-LIB (and z3 4.3.1) answers unsupported */
    @Override
    protected IResponse set_option_impl(IKeyword key, IAttributeValue value) {
        IResponse r = super.set_option_impl(key, value);
        if (r instanceof IResponse.IError e && e.errorMsg().matches("(?s)line \\d+ column \\d+: unknown parameter .*")) {
            return smtConfig.responseFactory.unsupported();
        }
        return r;
    }

    @Override
    public IResponse push(int number) {
        if (!logicSet) {
            return smtConfig.responseFactory.error("The logic must be set before a push command is issued");
        }
        if (number < 0) throw new SMT.InternalException("Internal bug: A push command called with a negative argument: " + number);
        if (number == 0) return recordChange(StackChange.PUSH, smtConfig.responseFactory.success());
        try {
            pushesDepth += number;
            // This odd invocation is to correct a bug in Z3 4.3.2, where (push) can print out more than one success message.
            solverProcess.sendNoListen("(push ",Integer.toString(number),")\n");
            solverProcess.sendNoListen("(echo \"<<DONE>>\")\n");
            // Accumulates every listen() call (not just the last one) so a genuine (error
            // ...) response to the push -- the process stays alive and still echoes the
            // marker normally -- is seen and reported, instead of being silently
            // overwritten by a later call and swallowed as success. A dead process is
            // already handled separately: SolverProcess.listen() throws
            // NoResponseException on a forced EOF with nothing on either stream, caught
            // below like any other exception here.
            StringBuilder drained = new StringBuilder();
            String s;
            do {
                s = solverProcess.listen();
                drained.append(s);
            } while (!drained.toString().contains("<<DONE>>"));
            String beforeMarker = drained.substring(0, drained.indexOf("<<DONE>>"));
            // the echo is a line z3 counts (see linesOffset), after the push's own
            IResponse r = beforeMarker.contains("(error") ? parseResponse(beforeMarker) : successOrEmpty(smtConfig);
            linesOffset++;
            return recordChange(StackChange.PUSH, r);
        } catch (Exception e) {
            return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
        }
    }
}
