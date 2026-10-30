/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.solvers;

// Items not implemented:
//   attributed expressions
//   get-values get-assignment get-proof get-unsat-core
//   some error detection and handling

import org.smtlib.*;
import org.smtlib.IExpr.IKeyword;

/** This class is an adapter that takes the SMT-LIB ASTs and translates them into yices2 commands */
public class Solver_yices2 extends Solver_smt implements ISolver {

    /** yices2 self-reports (get-info :error-behavior) as immediate-exit and its process
     *  does exit after some (not all) errors -- see AbstractSolver#sendCommand(ICommand,
     *  boolean), which uses this to pause briefly after any error response, giving a
     *  genuinely-exiting process time to finish dying before the next command's
     *  liveness check runs. */
    @Override
    protected boolean selfReportsImmediateExit() { return true; }

    /** Creates an instance of the yices2 solver */
    public Solver_yices2(SMT.Configuration smtConfig, /*@NonNull*/ String[] command) {
        super(smtConfig, command);
    }

    /** Creates an instance of the yices2 solver */
    public Solver_yices2(SMT.Configuration smtConfig, /*@NonNull*/ String command) {
        super(smtConfig, command);
    }

    public String[] cmd(String exec) {
        java.util.List<String> args = new java.util.ArrayList<String>(
                java.util.Arrays.asList(exec, "--incremental", "--interactive"));
        // yices2 has exactly one timeout flag, --timeout=<seconds>, applying per check-sat
        // call -- there is no whole-run option at all. If only the whole-run
        // smtConfig.timeoutTotal was requested, it is applied here per query as the closest
        // available approximation.
        double effective = smtConfig.timeout > 0 ? smtConfig.timeout : smtConfig.timeoutTotal;
        if (effective > 0) {
            if (smtConfig.timeout <= 0) {
                smtConfig.log.logDiag("#yices2 has no whole-run timeout option; approximating with a per-query --timeout of " + smtConfig.timeoutTotal + "s (the requested whole-run value)");
            } else if (smtConfig.timeoutTotal > 0) {
                smtConfig.log.logDiag("#yices2 has no whole-run timeout option; only the per-query --timeout (" + smtConfig.timeout + "s) is applied, the whole-run --timeout-total (" + smtConfig.timeoutTotal + "s) is ignored");
            }
            args.add("--timeout=" + (int)Math.ceil(effective));
        }
        return args.toArray(new String[args.size()]);
    }


    /** yices2 writes echo's text unquoted, so where it ends cannot be found (#136); the response
     *  to echo is its argument */
    @Override
    public IResponse echo(IExpr.IStringLiteral arg) {
        return arg;
    }

    @Override
    public IResponse start() {
        try {
            solverProcess.start(false);
            // FIXME - enable the following lines when the Z3 solver supports them
//            if (smtConfig.solverVerbosity > 0) solverProcess.sendNoListen("(set-option :verbosity ",Integer.toString(smtConfig.solverVerbosity),")");
//            if (!smtConfig.batch) solverProcess.sendNoListen("(set-option :interactive-mode true)"); // FIXME - not sure we can do this - we'll lose the feedback
            // Can't turn off printing success, or we get no feedback
//            solverProcess.sendAndListen("(set-option :print-success true)\n"); // Z3 4.4.0 needs this because it mistakenly has the default for :print-success as false
            //if (smtConfig.nosuccess) solverProcess.sendAndListen("(set-option :print-success false)");
            if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Started yices2 ");
            return smtConfig.responseFactory.success();
        } catch (Exception e) {
            return smtConfig.responseFactory.error("Failed to start process " + cmds[0] + " : " + e.getMessage());
        }
    }

    // parseResponse() used to be overridden here (pushed down from Solver_smt) for two
    // legacy-yices workarounds: converting old bvVALUE[WIDTH] bitvector literal syntax to
    // standard #bBITS, and a naive response.contains("error") check meant to catch
    // multi-fragment error text. Removed: current yices2 emits standard #b/#x bitvector
    // literals (the conversion was a no-op), and the "error" substring check was actively
    // wrong -- it misfired on any non-error response that merely contains "error" as a
    // substring, e.g. "(:error-behavior immediate-exit)" from get-info, which it wrapped
    // in a bogus error response. AbstractSolver's default (a real S-expression parse) is
    // correct for current yices2.
    //
    // get_option() used to be overridden here too, unwrapping a Response.Seq that current
    // yices2 apparently no longer produces: tried 13 different option keys (booleans,
    // strings, numerals, unsupported cases) against a real yices2 binary and never
    // triggered the wrapped shape the override was unwrapping. Removed rather than kept as
    // untested defensive code; AbstractSolver's default get_option() is correct for
    // current yices2. If a wrapped response resurfaces on some other yices2 build, fix it
    // then with a real repro rather than carrying an unverifiable workaround indefinitely.

    // check_sat() used to re-send a legacy native "(check)" command after the standard
    // "(check-sat)" and trust *that* response instead -- current yices2 rejects "(check)"
    // as a syntax error ("check is not a command"), so this unconditionally overwrote
    // every real sat/unsat result with "unknown". Removed; AbstractSolver's default
    // check_sat() (just "(check-sat)", trusted as-is) is correct. The timeout it used to
    // apply via a runtime "(set-timeout N)" command is now applied at startup instead,
    // via the --timeout=N CLI flag (see cmd()), matching how Solver_z3_recent applies
    // its timeout as a CLI flag rather than a runtime command.

    /** yices2 answers get-info :status with the last set-info :status value, but with
     *  (error "no info for :status") when none was set; SMT-LIB requires unsupported for a
     *  flag the solver does not support. Other flags are answered by yices2 itself. */
    @Override
    public IResponse get_info(IKeyword key) {
        IResponse r = super.get_info(key);
        if (Utils.STATUS.value().equals(key.value()) && r instanceof IResponse.IError e
                && e.errorMsg().contains("no info for :status")) {
            return smtConfig.responseFactory.unsupported();
        }
        return r;
    }

    // The checks below correct yices2 (2.6.5 and 2.7.0) answering get- commands that SMT-LIB makes
    // errors; it reports the other cases itself. yices2 answers get-model, get-value and
    // get-assignment with their enabling option off, though it reports the option as false. After
    // declare-* or define-* following a check, where SMT-LIB returns to assert mode, it still answers
    // from the earlier check (get-unsat-assumptions then names the new symbol for an assumption).

    /** The kinds of command after which yices2 still answers the get- commands about the last check
     *  (probed with 2.6.5 and 2.7.0, 2026-10-29; it has no datatypes or recursive definitions); after
     *  assert, push, pop and reset-assertions it reports the error itself */
    private static final java.util.Set<StackChange> ANSWERED_AFTER = java.util.EnumSet.of(
            StackChange.DECLARE_FUN, StackChange.DECLARE_SORT, StackChange.DEFINE_SORT, StackChange.DEFINE_FUN);

    /** yices2 answers get-model with :produce-models off, and in assert mode after a check */
    @Override
    public IResponse get_model() {
        IResponse err = inSatMode() ? requireOptionEnabled("get-model", Utils.PRODUCE_MODELS)
                : requireNoChangeSinceCheck("get-model", ANSWERED_AFTER);
        return err != null ? err : super.get_model();
    }

    /** yices2 answers get-value with :produce-models off, and in assert mode after a check */
    @Override
    public IResponse get_value(IExpr... terms) {
        IResponse err = inSatMode() ? requireOptionEnabled("get-value", Utils.PRODUCE_MODELS)
                : requireNoChangeSinceCheck("get-value", ANSWERED_AFTER);
        return err != null ? err : super.get_value(terms);
    }

    /** yices2 answers get-assignment with :produce-assignments off, and in assert mode after a check */
    @Override
    public IResponse get_assignment() {
        IResponse err = inSatMode() ? requireOptionEnabled("get-assignment", Utils.PRODUCE_ASSIGNMENTS)
                : requireNoChangeSinceCheck("get-assignment", ANSWERED_AFTER);
        return err != null ? err : super.get_assignment();
    }

    /** yices2 answers get-unsat-core in assert mode after a check */
    @Override
    public IResponse get_unsat_core() {
        IResponse err = requireNoChangeSinceCheck("get-unsat-core", ANSWERED_AFTER);
        return err != null ? err : super.get_unsat_core();
    }

    /** yices2 answers get-unsat-assumptions, wrongly, in assert mode after a check */
    @Override
    public IResponse get_unsat_assumptions() {
        IResponse err = requireNoChangeSinceCheck("get-unsat-assumptions", ANSWERED_AFTER);
        return err != null ? err : super.get_unsat_assumptions();
    }
}
