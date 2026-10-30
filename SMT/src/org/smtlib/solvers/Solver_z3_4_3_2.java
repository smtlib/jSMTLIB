/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.solvers;

import java.io.IOException;
import java.util.regex.Pattern;

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

    /** Corrects a non-conformance of z3 4.3.2: set-option of an option it does not know answers an error,
     *  {@code (error "line L column C: unknown parameter 'foo'\nLegal parameters are:\n ...")}, which names the
     *  option and then lists every parameter of its module, one per line. SMT-LIB answers {@code unsupported}
     *  there, as z3 4.3.1 does. The error is parsable, but the z3-4.3 adapters aim to be as close to conforming
     *  as they can, so it is reported as {@code unsupported}. Only errors matching
     *  {@code (?s)line \d+ column \d+: unknown parameter .*} are converted; any other set-option error (a bad
     *  value, for example) passes through. */
    @Override
    protected IResponse set_option_impl(IKeyword key, IAttributeValue value) {
        IResponse r = super.set_option_impl(key, value);
        if (r instanceof IResponse.IError e && e.errorMsg().matches("(?s)line \\d+ column \\d+: unknown parameter .*")) {
            return smtConfig.responseFactory.unsupported();
        }
        return r;
    }

    /** Corrects a non-conformance of z3 4.3.2: run with smtlib2_compliant=true, as this adapter runs it, a
     *  check-sat of a problem with quantifiers, before any push, makes z3 parse its built-in pattern database
     *  (111 commands) with print-success on, so a "success" line per command precedes the result. Those lines
     *  are read and dropped here. They all come before the result, so none is left for a later command. (Not
     *  passing smtlib2_compliant=true would avoid them, but changes many other responses away from SMT-LIB.) */
    @Override
    protected /*@Nullable*/ String sendScriptText(boolean listen, String... text) throws IOException {
        String response = super.sendScriptText(listen, text);
        if (response != null && text[0].startsWith("(check-sat")) {
            response = SUCCESS_LINES.matcher(response).replaceFirst("");
            while (response.isEmpty()) {
                response = SUCCESS_LINES.matcher(solverProcess.listen()).replaceFirst("");
            }
        }
        return response;
    }

    /** Leading "success" lines of a response */
    private static final Pattern SUCCESS_LINES = Pattern.compile("^(success\\r?\\n?)+");

    @Override
    public IResponse push(int number) {
        if (!logicSet) {
            return smtConfig.responseFactory.error("The logic must be set before a push command is issued");
        }
        if (number < 0) throw new SMT.InternalException("Internal bug: A push command called with a negative argument: " + number);
        checkSatStatus = null;
        if (number == 0) return smtConfig.responseFactory.success();
        try {
            pushesDepth += number;
            // This odd invocation is to correct a bug in Z3 4.3.2, where (push) can print out more than one success message.
            sendScriptText(false, "(push ",Integer.toString(number),")\n");
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
            // the echo, sent without sendScriptText, needs no linesOffset adjustment
            return beforeMarker.contains("(error") ? parseResponse(beforeMarker) : successOrEmpty(smtConfig);
        } catch (Exception e) {
            return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
        }
    }
}
