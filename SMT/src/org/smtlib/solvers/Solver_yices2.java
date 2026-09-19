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
import org.smtlib.impl.Response;

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
		// yices2 has exactly one timeout flag, --timeout=<seconds>, applying to the whole
		// session -- there is no separate per-query option at all. smtConfig.timeoutTotal
		// maps onto it directly; if only the per-query smtConfig.timeout was requested, it
		// is applied here as the closest available approximation, since that's the only
		// lever yices2 offers.
		if (smtConfig.timeoutTotal > 0) {
			args.add("--timeout=" + (int)Math.ceil(smtConfig.timeoutTotal));
			if (smtConfig.timeout > 0) {
				smtConfig.log.logDiag("#yices2 has no per-query timeout option; only the whole-run --timeout-total (" + smtConfig.timeoutTotal + "s) is applied, the per-query --timeout (" + smtConfig.timeout + "s) is ignored");
			}
		} else if (smtConfig.timeout > 0) {
			smtConfig.log.logDiag("#yices2 has no per-query timeout option; approximating with a whole-run --timeout of " + smtConfig.timeout + "s (the requested per-query value)");
			args.add("--timeout=" + (int)Math.ceil(smtConfig.timeout));
		}
		return args.toArray(new String[args.size()]);
	}


	@Override
	public IResponse start() {
		try {
			solverProcess.start(false);
			// FIXME - enable the following lines when the Z3 solver supports them
//			if (smtConfig.solverVerbosity > 0) solverProcess.sendNoListen("(set-option :verbosity ",Integer.toString(smtConfig.solverVerbosity),")");
//			if (!smtConfig.batch) solverProcess.sendNoListen("(set-option :interactive-mode true)"); // FIXME - not sure we can do this - we'll lose the feedback
			// Can't turn off printing success, or we get no feedback
//			solverProcess.sendAndListen("(set-option :print-success true)\n"); // Z3 4.4.0 needs this because it mistakenly has the default for :print-success as false
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
	@Override
	public IResponse get_option(IKeyword key) {
		IResponse r = super.get_option(key);
		if (r instanceof Response.Seq) {
			// yices2 implements get-option incorrectly, hence this computation
			return ((Response.Seq)r).attributes().get(0).attrValue();
		}
		return r;
	}

	// check_sat() used to re-send a legacy native "(check)" command after the standard
	// "(check-sat)" and trust *that* response instead -- current yices2 rejects "(check)"
	// as a syntax error ("check is not a command"), so this unconditionally overwrote
	// every real sat/unsat result with "unknown". Removed; AbstractSolver's default
	// check_sat() (just "(check-sat)", trusted as-is) is correct. The timeout it used to
	// apply via a runtime "(set-timeout N)" command is now applied at startup instead,
	// via the --timeout=N CLI flag (see cmd()), matching how Solver_z3_recent applies
	// its timeout as a CLI flag rather than a runtime command.

	/** :status is the only real special case left here: yices2 has no native get-info
	 *  support for it ({@code (error "no info for :status")}), so it's answered from the
	 *  locally-tracked checkSatStatus instead. Everything else used to be hardcoded here
	 *  too (:error-behavior, :all-statistics, :reason-unknown, :authors, :version, :name,
	 *  and an "unsupported" catch-all for every other keyword) with stale values from a
	 *  much older yices2 that apparently didn't implement get-info -- current yices2
	 *  answers all of those correctly itself (confirmed :error-behavior is actually
	 *  "immediate-exit", not the hardcoded "continued-execution"; :all-statistics returns
	 *  a real statistics dump, not "unsupported"), so they're now left to
	 *  AbstractSolver's default (forward to the solver). */
	@Override
	public IResponse get_info(IKeyword key) {
		if (Utils.STATUS.toString().equals(key.value())) {
			return checkSatStatus==null ? smtConfig.responseFactory.unsupported() : checkSatStatus;
		}
		return super.get_info(key);
	}
}
