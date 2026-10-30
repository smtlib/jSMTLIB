/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.solvers;

import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.List;

import org.smtlib.*;
import org.smtlib.IExpr.IKeyword;

/** The adapter for Alt-Ergo (developed against 2.6.3 on Linux), run as {@code alt-ergo --input smtlib2
 *  --output smtlib2}, reading the script from standard input.
 *  <p>
 *  Alt-Ergo writes nothing for a successful command and answers {@code (set-option :print-success true)}
 *  with {@code unsupported}, so {@link #solverPrintsSuccess} is false: each command is followed by an
 *  echo that marks the end of its response (see AbstractSolver). Alt-Ergo ignores, writing nothing,
 *  get-option, get-value, get-assertions, get-unsat-core, get-unsat-assumptions, get-proof and
 *  reset-assertions; those are answered here. It is run with --continue-on-error (by default it exits
 *  after any error), and in its default mode answers check-sat with unsat or unknown, never sat.
 *  <p>
 *  Timeout: Alt-Ergo's {@code --timelimit=SECONDS} is one value, applied whole-run or, with
 *  {@code --timelimit-per-goal}, per goal; see the constructor for how jSMTLIB's two timeouts map
 *  onto it. */
public class Solver_altergo extends AbstractSolver implements ISolver {

    /** The command-line arguments for launching the solver. */
    protected String cmds[];

    /** Creates an instance of the solver */
    public Solver_altergo(SMT.Configuration smtConfig, /*@NonNull*/ String executable) {
        this.smtConfig = smtConfig;
        // --continue-on-error: by default Alt-Ergo exits after any error; with it, the failed command
        // leaves the state unchanged and Alt-Ergo reports :error-behavior continued-execution
        List<String> args = new java.util.ArrayList<String>(Arrays.asList(executable,"--input","smtlib2","--output","smtlib2",
                "--continue-on-error"));
        // Alt-Ergo's --timelimit=SECONDS is one shared value; --timelimit-per-goal makes it
        // apply per-goal (jSMTLIB's per-query smtConfig.timeout) instead of whole-run
        // (smtConfig.timeoutTotal). If a per-query value was requested, it wins (with the
        // modifier), since it's the more commonly useful of the two; a distinct whole-run
        // value given at the same time can't also be honored on this solver.
        if (smtConfig.timeout > 0) {
            args.add("--timelimit=" + (int)Math.ceil(smtConfig.timeout));
            args.add("--timelimit-per-goal");
            if (smtConfig.timeoutTotal > 0 && smtConfig.timeoutTotal != smtConfig.timeout) {
                smtConfig.log.logDiag("#alt-ergo has only one timeout value, shared between per-query and whole-run; only the per-query --timeout (" + smtConfig.timeout + "s) is applied, the whole-run --timeout-total (" + smtConfig.timeoutTotal + "s) is ignored");
            }
        } else if (smtConfig.timeoutTotal > 0) {
            args.add("--timelimit=" + (int)Math.ceil(smtConfig.timeoutTotal));
        }
        cmds = args.toArray(new String[args.size()]);
        solverProcess = newProcess(cmds);
    }

    /** Alt-Ergo's stderr holds only diagnostics: ; comment lines, which are ignored anyway, and, before an
     *  error's, a bare location line, whose line number counts the echoes sent after commands and which
     *  arrives at no fixed time relative to the error response; so it is discarded */
    private SolverProcess newProcess(String[] command) {
        SolverProcess p = new SolverProcess(command,"\n",smtConfig.logfile,StandardCharsets.UTF_8);
        p.discardErrorOutput = true;
        return p;
    }

    /** Launches the given command as is (a .command property, #147), without adding the flags
     *  the executable form adds */
    public Solver_altergo(SMT.Configuration smtConfig, /*@NonNull*/ String[] command) {
        this.smtConfig = smtConfig;
        cmds = command;
        solverProcess = newProcess(cmds);
    }

    @Override
    public IResponse start() {
        try {
            solverProcess.start(false);
            if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Started " + smtConfig.solvername);
            return smtConfig.responseFactory.success();
        } catch (Exception e) {
            return smtConfig.responseFactory.error("Failed to start process " + cmds[0] + " : " + e.getMessage());
        }
    }

    /** Alt-Ergo writes nothing for a successful command and answers {@code (set-option :print-success
     *  true)} with unsupported; its commands are therefore sent as when pipelining, each followed by an
     *  echo that marks the end of its response */
    @Override
    protected boolean solverPrintsSuccess() {
        return false;
    }

    /** How long (ms) exit waits for Alt-Ergo to end */
    private static final long EXIT_WAIT_MILLIS = 2000;

    /** Alt-Ergo is silent for exit, as for any successful command, but no echo can follow it, since the
     *  process ends; so success is answered once the process has ended. If it had already ended (its
     *  output was read to its end) or does not end in time, the answer is as the
     *  base class gives it, or an error. */
    @Override
    public IResponse exit() {
        boolean running = solverProcess != null && !solverProcess.outputEnded() && solverProcess.isRunning(true);
        IResponse r = sendExitCommand();
        if (running && smtConfig.responseFactory.empty().equals(r)) {
            r = solverProcess.waitForEnd(EXIT_WAIT_MILLIS) ? successOrEmpty(smtConfig)
                    : smtConfig.responseFactory.error("alt-ergo did not end after exit");
        }
        solverProcess.exit();
        if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Ended " + smtConfig.solvername);
        solverProcess = null;
        return r;
    }

    /** Sent to Alt-Ergo, and kept here for get_option when Alt-Ergo accepts it */
    @Override
    protected IResponse set_option_impl(IKeyword key, IAttributeValue value) {
        IResponse r = checkPrintSuccess(smtConfig, key, value);
        if (r != null) return r;
        r = sendCommand(smtConfig.commandFactory.set_option(key, value));
        if (!r.isError() && !smtConfig.responseFactory.unsupported().equals(r)) options.put(key.value(), value);
        return r;
    }

    /** Alt-Ergo ignores get-option, writing nothing; answered from the values set (see set_option_impl)
     *  and the SMT-LIB defaults */
    @Override
    public IResponse get_option(IKeyword key) {
        if (key.equals(printSuccess)) return smtConfig.nosuccess ? Utils.FALSE : Utils.TRUE;
        String opt = key.value();
        IAttributeValue value = options.get(opt);
        if (value == null) value = smtConfig.utils.defaults.get(opt);
        if (value == null) return smtConfig.responseFactory.unsupported();
        return value;
    }

    /** Alt-Ergo ignores reset-assertions, writing nothing and keeping the assertions; answered
     *  unsupported without sending it */
    @Override
    public IResponse reset_assertions() {
        return smtConfig.responseFactory.unsupported();
    }

    /** Alt-Ergo writes nothing for get-proof (it ignores it); answered unsupported without sending it */
    @Override
    public IResponse get_proof() {
        return smtConfig.responseFactory.unsupported();
    }

    /** Alt-Ergo ignores get-value, writing nothing; answered unsupported without sending it */
    @Override
    public IResponse get_value(IExpr... terms) {
        return smtConfig.responseFactory.unsupported();
    }

    /** Alt-Ergo ignores get-assertions, writing nothing; answered unsupported without sending it */
    @Override
    public IResponse get_assertions() {
        return smtConfig.responseFactory.unsupported();
    }

    /** Alt-Ergo ignores get-unsat-core, writing nothing (with --sat-solver Tableaux it writes a
     *  non-SMT-LIB core after check-sat instead); answered unsupported without sending it */
    @Override
    public IResponse get_unsat_core() {
        return smtConfig.responseFactory.unsupported();
    }

    /** Alt-Ergo ignores get-unsat-assumptions, writing nothing; answered unsupported without sending it */
    @Override
    public IResponse get_unsat_assumptions() {
        return smtConfig.responseFactory.unsupported();
    }

    /** The kinds of command after which Alt-Ergo still answers get-model and get-assignment about the
     *  last check (probed with 2.6.3, 2026-10-29); after push and pop it reports the error itself */
    private static final java.util.Set<StackChange> ANSWERED_AFTER = java.util.EnumSet.of(
            StackChange.DECLARE_FUN, StackChange.DECLARE_SORT, StackChange.DEFINE_SORT,
            StackChange.DECLARE_DATATYPE, StackChange.DEFINE_FUN, StackChange.DEFINE_FUN_REC, StackChange.ASSERT);

    /** Alt-Ergo answers get-model in assert mode after a check */
    @Override
    public IResponse get_model() {
        IResponse err = requireNoChangeSinceCheck("get-model", ANSWERED_AFTER);
        return err != null ? err : super.get_model();
    }

    /** Alt-Ergo answers get-assignment in assert mode after a check. Sent through sendCommand, which
     *  reads Alt-Ergo's reply up to the echo after it (the base class reads one line, which may be a
     *  blank line Alt-Ergo writes around replies) */
    @Override
    public IResponse get_assignment() {
        IResponse err = requireNoChangeSinceCheck("get-assignment", ANSWERED_AFTER);
        if (err != null) return err;
        IResponse r = sendCommand(smtConfig.commandFactory.get_assignment());
        if (!(r instanceof org.smtlib.sexpr.ISexpr.ISeq)) return r;
        String text = smtConfig.defaultPrinter.toString(r);
        try {
            return smtConfig.responseFactory.get_assignment_response(
                    new org.smtlib.sexpr.Parser(smtConfig, new org.smtlib.impl.Pos.Source(text, null)).parseAssignmentList());
        } catch (IParser.ParserException e) {
            return smtConfig.responseFactory.error("Unexpected output from the solver: " + text);
        }
    }

}
