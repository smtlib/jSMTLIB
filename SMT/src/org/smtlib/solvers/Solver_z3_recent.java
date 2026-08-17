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

/** This class is an adapter for recent z3 versions (empirically verified against 4.8.12 and
 *  4.10.2), on the assumption that they are (or should be) fully SMT-LIB compliant: it is a
 *  concrete, silent inheritor of {@link AbstractSolver} -- only the startup command line and
 *  {@link #start()}/{@link #exit()} (process lifecycle) are overridden. Empirically, none of
 *  the z3-4.3-era workarounds the old version-specific adapters needed (see the git history of
 *  the now-removed Solver_z3_4_5/4_6/4_7/4_8 classes) are needed any more: :print-success
 *  already defaults to true (no priming command, and so no line-number offset to correct for
 *  in error messages),
 *  bitvector literals print in standard #b/#x form (no bv5[8]-style regex conversion needed),
 *  and errors come back as clean, well-formed (error "...") s-expressions that
 *  AbstractSolver's generic parseResponse handles without any massaging.
 *  <p>
 *  One confirmed compliance gap, not caused by this adapter: z3 defaults
 *  {@code :produce-models} to {@code true} rather than the spec's {@code false}, with no
 *  known CLI flag or startup option to change that -- scripts checking that default need a
 *  z3-specific golden reflecting it. */
public class Solver_z3_recent extends AbstractSolver implements ISolver {

	/** The command-line arguments for launching the solver. */
	protected String cmds[];
	// WARNING=false suppresses z3's own diagnostic WARNING messages (e.g. "pattern does not
	// contain all quantified variables"): these print as a bare "WARNING" line with no
	// parens before the rest of the message follows on a later flush, which fools
	// SolverProcess's paren-balance response-completion heuristic into treating the
	// response as already complete and truncating it.
	protected String cmds_win[] = new String[]{ "", "-smt2","-in","SMTLIB2_COMPLIANT=true","WARNING=false"};
	protected String cmds_mac[] = new String[]{ "", "-smt2","-in","SMTLIB2_COMPLIANT=true","WARNING=false"};
	protected String cmds_unix[] = new String[]{ "", "-smt2","-in","WARNING=false"};

	/** Creates an instance of the solver */
	public Solver_z3_recent(SMT.Configuration smtConfig, /*@NonNull*/ String executable) {
		this.smtConfig = smtConfig;
		if (isWindows) {
			cmds = cmds_win;
		} else if (isMac) {
			cmds = cmds_mac;
		} else {
			cmds = cmds_unix;
		}
		double timeout = smtConfig.timeout;
		if (timeout > 0) {
			List<String> args = new java.util.ArrayList<String>(cmds.length+1);
			args.addAll(Arrays.asList(cmds));
			args.add("-T:" + Integer.toString((int)Math.ceil(timeout)));
			cmds = args.toArray(new String[args.size()]);
		}
		cmds[0] = executable;
		// z3 -in does not print an interactive prompt, so "\n" is the right end marker.
		solverProcess = new SolverProcess(cmds,"\n",smtConfig.logfile,StandardCharsets.UTF_8);
	}

	@Override
	public IResponse start() {
		try {
			solverProcess.start(false);
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Started z3 ");
			return smtConfig.responseFactory.success();
		} catch (Exception e) {
			return smtConfig.responseFactory.error("Failed to start process " + cmds[0] + " : " + e.getMessage());
		}
	}

	@Override
	public IResponse exit() {
		IResponse response = sendCommand(smtConfig.commandFactory.exit());
		solverProcess.exit();
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Ended z3 ");
		solverProcess = null;
		return response;
	}

}
