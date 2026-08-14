/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.solvers;

import org.smtlib.*;

/** This class is an adapter for SMTInterpol (a Java SMT solver launched as
 *  {@code java -jar smtinterpol-VERSION.jar}, not a native executable): it is a concrete,
 *  silent inheritor of {@link AbstractSolver} -- only the startup command line and
 *  {@link #start()}/{@link #exit()} (process lifecycle) are overridden. Empirically
 *  fully SMT-LIB compliant: :print-success already defaults to true (no priming
 *  command needed), errors come back as clean (error "...") s-expressions, and
 *  bitvector values print via the equally-valid {@code (_ bvN W)} indexed-literal
 *  form (not #b/#x, but standard concrete syntax that the generic parser handles
 *  without any massaging).
 *  <p>
 *  The {@code -q} flag is required, not cosmetic: without it, SMTInterpol writes a
 *  large volume of "INFO - ..." solver-internal logging to its own stderr for every
 *  check-sat (statistics, per-clause traces, model dumps). That's a separate stream
 *  from the stdout responses SolverProcess parses, but SolverProcess's listen() has a
 *  heuristic (see its "some cases (yices2) the prompt is on the error stream" comment)
 *  that can prefer non-empty stderr content over stdout -- so unsilenced INFO noise
 *  risks being returned as the response instead of the real one. -q suppresses it at
 *  the source rather than relying on that heuristic guessing right. */
public class Solver_smtinterpol extends AbstractSolver implements ISolver {

	/** The command-line arguments for launching the solver. */
	protected String cmds[];

	/** Creates an instance of the solver */
	public Solver_smtinterpol(SMT.Configuration smtConfig, /*@NonNull*/ String executable) {
		this.smtConfig = smtConfig;
		java.util.List<String> args = new java.util.ArrayList<String>();
		args.add("java");
		args.add("-jar");
		args.add(executable);
		args.add("-q");
		if (smtConfig.timeout > 0) {
			// -t sets a per-check-sat timeout in milliseconds.
			args.add("-t");
			args.add(Integer.toString((int)Math.ceil(smtConfig.timeout * 1000)));
		}
		cmds = args.toArray(new String[args.size()]);
		// SMTInterpol prints no interactive prompt, so "\n" is the right end marker.
		solverProcess = new SolverProcess(cmds,"\n",smtConfig.logfile);
	}

	@Override
	public IResponse start() {
		try {
			solverProcess.start(false);
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Started SMTInterpol ");
			return smtConfig.responseFactory.success();
		} catch (Exception e) {
			return smtConfig.responseFactory.error("Failed to start process " + cmds[0] + " : " + e.getMessage());
		}
	}

	@Override
	public IResponse exit() {
		IResponse response = sendCommand(smtConfig.commandFactory.exit());
		solverProcess.exit();
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Ended SMTInterpol ");
		solverProcess = null;
		return response;
	}

}
