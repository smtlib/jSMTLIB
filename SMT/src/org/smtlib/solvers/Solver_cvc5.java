/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.solvers;

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
 *  parseResponse without issue.
 *  <p>
 *  One confirmed, non-workaroundable compliance gap: cvc5 self-reports {@code
 *  (get-info :error-behavior)} as {@code immediate-exit} (not {@code
 *  continued-execution}) and its process actually exits after a top-level parse
 *  error. Neither {@code (set-option :error-behavior continued-execution)} (rejected
 *  as unsupported) nor {@code (set-info :error-behavior continued-execution)}
 *  (silently accepted but with no actual effect — get-info still reports
 *  immediate-exit and the process still dies) can change this, so there's no way to
 *  ask for the other mode. Scripts that trigger a genuine parse error need a
 *  cvc5-specific golden reflecting that (or a skip marker), not a code change here. */
public class Solver_cvc5 extends AbstractSolver implements ISolver {

	/** The command-line arguments for launching the solver. --print-success turns on
	 *  success replies from the very first command onward (confirmed: --interactive does
	 *  NOT imply it by itself -- without --print-success, the first command gets no
	 *  reply at all), so no priming (set-option :print-success true) is needed in
	 *  start(). */
	protected String cmds[];
	protected String cmds_win[] = new String[]{ "", "--lang","smt","--interactive","--incremental","--quiet","--print-success","--strict-parsing","--no-full-saturate-quant"};
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
			cmds = Utils.cat(cmds,"--seed",""+smtConfig.seed);
		}
		double timeout = smtConfig.timeout;
		if (timeout > 0) {
			List<String> args = new java.util.ArrayList<String>(cmds.length+1);
			args.addAll(Arrays.asList(cmds));
			args.add("--tlimit-per=" + Long.toString(Math.round(1000*timeout+0.5)));
			cmds = args.toArray(new String[args.size()]);
		}
		cmds[0] = executable;
		// With --quiet, cvc5 never prints an interactive "cvc5> " prompt, so "\n" (like
		// Solver_smt) is the right end marker, not a prompt string.
		solverProcess = new SolverProcess(cmds,"\n",smtConfig.logfile);
	}

	@Override
	public IResponse start() {
		try {
			solverProcess.start(false);
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Started cvc5 ");
			return smtConfig.responseFactory.success();
		} catch (Exception e) {
			return smtConfig.responseFactory.error("Failed to start process " + cmds[0] + " : " + e.getMessage());
		}
	}

	@Override
	public IResponse exit() {
		IResponse response = sendCommand(smtConfig.commandFactory.exit());
		solverProcess.exit();
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Ended cvc5 ");
		solverProcess = null;
		return response;
	}

}
