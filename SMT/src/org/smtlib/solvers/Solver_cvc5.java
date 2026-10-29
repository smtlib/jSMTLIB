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

/** This class is an adapter for cvc5, on the assumption that it is (or should be) a
 *  fully SMT-LIB compliant solver: it is a concrete, silent inheritor of {@link
 *  AbstractSolver} — only the startup command line (cvc5 needs {@code --incremental}
 *  to accept push/pop at all, and {@code --quiet} to suppress informational stderr
 *  chatter that would otherwise fool {@link SolverProcess}'s stdout/stderr-preference
 *  heuristic) and {@link #start()} (process lifecycle) are overridden. Empirically
 *  (against cvc5 1.3.2), none of the CVC4-era workarounds a previous version of this
 *  class used to need still apply: cvc5 handles Bool-sorted quantifiers natively (no
 *  translate() workaround needed), get-value/
 *  get-option return clean standard-shaped responses (no Response.Seq workaround
 *  needed), and get-info/get-option round-trip through AbstractSolver's generic
 *  parseResponse without issue -- with one exception, {@link #get_option}, described
 *  below.
 *  <p>
 *  One confirmed, patchable compliance gap: cvc5 answers {@code (get-option
 *  :regular-output-channel)}/{@code (get-option :diagnostic-output-channel)} with a
 *  bare, unquoted symbol ({@code stdout}/{@code stderr}) rather than the SMT-LIB string
 *  literal ({@code "stdout"}/{@code "stderr"}) these two options are specified to hold --
 *  confirmed against a real cvc5 1.3.2 process. {@link #get_option} wraps a bare-symbol
 *  answer for either option into a proper string literal with the same text.
 *  <p>
 *  One confirmed, non-workaroundable compliance gap: cvc5 self-reports {@code
 *  (get-info :error-behavior)} as {@code immediate-exit} (not {@code
 *  continued-execution}) and its process actually exits after a top-level parse
 *  error. Neither {@code (set-option :error-behavior continued-execution)} (rejected
 *  as unsupported) nor {@code (set-info :error-behavior continued-execution)}
 *  (silently accepted but with no actual effect — get-info still reports
 *  immediate-exit and the process still dies) can change this, so there's no way to
 *  ask for the other mode. {@link #selfReportsImmediateExit()} tells {@link
 *  AbstractSolver#sendCommand(ICommand, boolean)} about this, so once cvc5 reports one
 *  real error, jSMTLIB pauses briefly before sending anything further, giving the
 *  process time to actually finish exiting (if it is going to) before the next
 *  command's liveness check runs. */
public class Solver_cvc5 extends AbstractSolver implements ISolver {

    @Override
    protected boolean selfReportsImmediateExit() { return true; }

    /** cvc5 reports 'cvc5 interrupted by timeout.' on stderr, with no answer, when its whole-run limit, --tlimit,
     *  ends it, and then aborts (checked with cvc5 1.3.2) */
    @Override
    protected boolean isTimeLimitResponse(String rawResponse) {
        return rawResponse.contains("interrupted by timeout");
    }

    /** cvc5 carries on after most errors (e.g. sort errors), but after a parse error it no longer
     *  processes input, and when run interactively it does not always exit either -- so it is
     *  stopped (see AbstractSolver.checkImmediateExit). */
    @Override
    protected boolean errorStopsSolver(IResponse error) {
        return error instanceof IResponse.IError && ((IResponse.IError)error).errorMsg().startsWith("Parse Error");
    }

    /** The command-line arguments for launching the solver. --print-success turns on
     *  success replies from the very first command onward (confirmed: --interactive does
     *  NOT imply it by itself -- without --print-success, the first command gets no
     *  reply at all), so no priming (set-option :print-success true) is needed in
     *  start(). */
    protected String cmds[];
    // --no-full-saturate-quant removed (issue #69): no rationale for this Windows-only
    // flag survived anywhere in the project's history (git archaeology found only an
    // unexplained WIP commit that first added it). Confirmed safe to remove via a full
    // CI run on Windows (run 35416506960): all 1454 cvc5-1.3.2 test executions passed
    // (or hit pre-existing, unrelated .skip.cvc5-1.3.2 cases) with the flag gone,
    // including every quantifier-touching test in the suite -- no hang, no timeout, no
    // behavior change observed.
    protected String cmds_win[] = new String[]{ "", "--lang","smt","--interactive","--incremental","--quiet","--print-success","--strict-parsing"};
    protected String cmds_mac[] = new String[]{ "", "--lang","smt","--interactive","--incremental","--quiet","--print-success","--strict-parsing"};
    protected String cmds_unix[] = new String[]{ "", "--lang","smt","--interactive","--incremental","--quiet","--print-success","--strict-parsing"};

    /** Creates an instance of the solver */
    public Solver_cvc5(SMT.Configuration smtConfig, /*@NonNull*/ String executable) {
        this.smtConfig = smtConfig;
        if (isWindows) {
            cmds = cmds_win;
        } else if (isMac) {
            cmds = cmds_mac;
        } else {
            cmds = cmds_unix;
        }
        if (smtConfig.seed != 0) {
            List<String> args = new java.util.ArrayList<String>(Arrays.asList(cmds));
            args.add("--seed");
            args.add("" + smtConfig.seed);
            cmds = args.toArray(new String[args.size()]);
        }
        double timeout = smtConfig.timeout;
        double timeoutTotal = smtConfig.timeoutTotal;
        if (timeout > 0 || timeoutTotal > 0) {
            // cvc5 has separate per-query and whole-run flags, both in milliseconds
            // (jSMTLIB's timeout/timeoutTotal are always in seconds -- see SMT.Configuration).
            List<String> args = new java.util.ArrayList<String>(Arrays.asList(cmds));
            if (timeout > 0) args.add("--tlimit-per=" + Long.toString(Math.round(1000*timeout+0.5)));
            if (timeoutTotal > 0) args.add("--tlimit=" + Long.toString(Math.round(1000*timeoutTotal+0.5)));
            cmds = args.toArray(new String[args.size()]);
        }
        cmds[0] = executable;
        // With --quiet, cvc5 never prints an interactive "cvc5> " prompt, so "\n" (like
        // Solver_smt) is the right end marker, not a prompt string.
        solverProcess = new SolverProcess(cmds,"\n",smtConfig.logfile,StandardCharsets.UTF_8);
    }

    /** Launches the given command as is (a .command property, #147), without adding the flags
     *  the executable form adds */
    public Solver_cvc5(SMT.Configuration smtConfig, /*@NonNull*/ String[] command) {
        this.smtConfig = smtConfig;
        cmds = command;
        solverProcess = new SolverProcess(cmds,"\n",smtConfig.logfile,StandardCharsets.UTF_8);
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

    /** See the class Javadoc: wraps a bare-symbol answer for a string-typed option
     *  (Utils.stringOptions -- currently just :regular-output-channel and
     *  :diagnostic-output-channel) into a proper SMT-LIB string literal with the same
     *  text, working around cvc5 answering those two with an unquoted symbol instead. */
    @Override
    public IResponse get_option(IExpr.IKeyword option) {
        IResponse response = super.get_option(option);
        if (response instanceof IExpr.ISymbol && smtConfig.utils.stringOptions.contains(option.value())) {
            return smtConfig.exprFactory.unquotedString(((IExpr.ISymbol)response).value());
        }
        return response;
    }

    // The checks below correct cvc5 1.3.2 answering get- commands that SMT-LIB makes errors; it
    // reports the other cases itself. After assert or define-* following a check, where SMT-LIB
    // returns to assert mode, cvc5 still answers from the earlier check (a model need not satisfy the
    // new assertion), and get-unsat-assumptions aborts the process.

    /** The value the script gave :produce-assertions (or its earlier name :interactive-mode): cvc5
     *  answers get-assertions whatever the option's value, and, run with --interactive, reports it
     *  as true from the start and again once the assertion stack is used, so get-option cannot tell */
    private boolean produceAssertions = false;

    @Override
    protected IResponse set_option_impl(IExpr.IKeyword key, IAttributeValue value) {
        IResponse r = super.set_option_impl(key, value);
        if ((Utils.PRODUCE_ASSERTIONS.equals(key.value()) || Utils.INTERACTIVE_MODE.equals(key.value())) && !r.isError()) {
            produceAssertions = Utils.TRUE.equals(value);
        }
        return r;
    }

    @Override
    public IResponse reset() {
        produceAssertions = false;
        return super.reset();
    }

    /** cvc5 answers get-assertions with :produce-assertions off */
    @Override
    public IResponse get_assertions() {
        if (!produceAssertions) {
            return smtConfig.responseFactory.error("The get-assertions command is only valid if "
                    + Utils.produceAssertionsKey(smtConfig) + " has been enabled");
        }
        return super.get_assertions();
    }

    /** cvc5 answers get-assignment with :produce-assignments off (if :produce-models is on), and in
     *  assert mode after a check */
    @Override
    public IResponse get_assignment() {
        IResponse err = inSatMode() ? requireOptionEnabled("get-assignment", Utils.PRODUCE_ASSIGNMENTS)
                : requireUnchangedSinceCheck("get-assignment");
        return err != null ? err : super.get_assignment();
    }

    /** cvc5 answers get-model in assert mode after a check */
    @Override
    public IResponse get_model() {
        IResponse err = requireUnchangedSinceCheck("get-model");
        return err != null ? err : super.get_model();
    }

    /** cvc5 answers get-value in assert mode after a check */
    @Override
    public IResponse get_value(IExpr... terms) {
        IResponse err = requireUnchangedSinceCheck("get-value");
        return err != null ? err : super.get_value(terms);
    }

    /** cvc5 answers get-proof in assert mode after a check */
    @Override
    public IResponse get_proof() {
        IResponse err = requireUnchangedSinceCheck("get-proof");
        return err != null ? err : super.get_proof();
    }

    /** cvc5 answers get-unsat-core in assert mode after a check */
    @Override
    public IResponse get_unsat_core() {
        IResponse err = requireUnchangedSinceCheck("get-unsat-core");
        return err != null ? err : super.get_unsat_core();
    }

    /** cvc5 aborts on get-unsat-assumptions in assert mode after a check */
    @Override
    public IResponse get_unsat_assumptions() {
        IResponse err = requireUnchangedSinceCheck("get-unsat-assumptions");
        return err != null ? err : super.get_unsat_assumptions();
    }

}
