/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.solvers;

import java.nio.charset.StandardCharsets;

import org.smtlib.*;

/** This class is an adapter for SMTInterpol (a Java SMT solver launched as
 *  {@code java -jar smtinterpol-VERSION.jar}, not a native executable): it is a concrete,
 *  silent inheritor of {@link AbstractSolver} -- the base launch command is declared in
 *  jsmtlib.properties via {@code org.smtlib.solver_smtinterpol-2.5.command} (see SMT.startSolver's
 *  {@code %exec%} placeholder substitution), so only the conditional timeout flag and
 *  {@link #start()}/{@link #exit()} (process lifecycle) are handled here. Empirically
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

	/** Creates an instance of the solver. The base launch command ("java -jar
	 *  &lt;jar&gt; -q") comes from the org.smtlib.solver_smtinterpol-2.5.command
	 *  property; only the timeout flag, which is conditional on smtConfig and so
	 *  can't be expressed in that static property, is still added here. */
	public Solver_smtinterpol(SMT.Configuration smtConfig, /*@NonNull*/ String[] command) {
		this.smtConfig = smtConfig;
		if (smtConfig.timeout > 0) {
			// -t sets a per-check-sat timeout in milliseconds.
			java.util.List<String> args = new java.util.ArrayList<String>(java.util.Arrays.asList(command));
			args.add("-t");
			args.add(Integer.toString((int)Math.ceil(smtConfig.timeout * 1000)));
			cmds = args.toArray(new String[args.size()]);
		} else {
			cmds = command;
		}
		// SMTInterpol prints no interactive prompt, so "\n" is the right end marker.
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

}
