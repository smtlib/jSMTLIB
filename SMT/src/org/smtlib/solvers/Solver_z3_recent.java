/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.solvers;

import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.smtlib.*;

/** This class is an adapter for recent z3 versions (empirically verified against 4.8.12 and
 *  4.10.2), on the assumption that they are (or should be) fully SMT-LIB compliant: it is a
 *  concrete, silent inheritor of {@link AbstractSolver} -- only the startup command line and
 *  {@link #start()}/{@link #exit()} (process lifecycle) are overridden. Empirically, none of
 *  the z3-4.3-era workarounds the old version-specific adapters needed (see the git history of
 *  the now-removed Solver_z3_4_5/4_6/4_7/4_8 classes) are needed any more:
 *  bitvector literals print in standard #b/#x form (no bv5[8]-style regex conversion needed),
 *  and errors come back as clean, well-formed (error "...") s-expressions that
 *  AbstractSolver's generic parseResponse handles without any massaging.
 *  <p>
 *  {@code :print-success} needs an explicit priming command on Linux specifically, same
 *  idea as {@link Solver_z3_4_3}: jSMTLIB's own protocol expects a response to every
 *  command it sends, and print-success false (the SMT-LIB-compliant default) means most
 *  commands legitimately produce none on their own. Confirmed via gdb-attaching to a hung
 *  z3 process on Linux CI that the very first real command produced no response at all --
 *  z3 sitting in its own SMT2 scanner blocked reading stdin for more input, having
 *  silently consumed the command and moved on without acking it, which jSMTLIB has no way
 *  to distinguish from a solver that's simply slow, so it just waited forever. macOS/
 *  Windows don't hit this and already have goldens reflecting an un-primed first response,
 *  so the priming command below is Linux-only rather than unconditional -- doing it
 *  everywhere would shift every line-numbered error message on every platform by one, not
 *  just the platform that actually needs it.
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
	protected String cmds_unix[] = new String[]{ "", "-smt2","-in","SMTLIB2_COMPLIANT=true","WARNING=false"};

	/** True only on the platform where the print-success priming command below is needed
	 *  (see the class javadoc) -- also gates the linesOffset compensation in
	 *  parseResponse(), since the two must always travel together. */
	protected final boolean needsPrintSuccessPriming = !isWindows && !isMac;

	/** Incremented by the priming command in start() (never more than once -- start() is
	 *  only ever called once per instance): every "line N" a Linux z3 process reports needs
	 *  N-linesOffset to stay consistent with the user's own script, since z3 counts input
	 *  lines from the very start of the stream it receives, including the priming line
	 *  jSMTLIB adds before the user's script begins. Stays 0 (a no-op in parseResponse()) on
	 *  every platform that doesn't need the priming command at all. */
	protected int linesOffset = 0;

	private static final Pattern LINE_NUMBER = Pattern.compile("line (\\d+)");

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
			if (needsPrintSuccessPriming) {
				solverProcess.sendAndListen("(set-option :print-success true)\n");
				linesOffset++;
			}
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Started " + smtConfig.solvername);
			return smtConfig.responseFactory.success();
		} catch (Exception e) {
			return smtConfig.responseFactory.error("Failed to start process " + cmds[0] + " : " + e.getMessage());
		}
	}

	@Override
	protected IResponse parseResponse(String response) {
		if (linesOffset != 0) {
			Matcher m = LINE_NUMBER.matcher(response);
			StringBuilder sb = new StringBuilder();
			while (m.find()) {
				m.appendReplacement(sb, "line " + (Integer.parseInt(m.group(1)) - linesOffset));
			}
			m.appendTail(sb);
			response = sb.toString();
		}
		return super.parseResponse(response);
	}

}
