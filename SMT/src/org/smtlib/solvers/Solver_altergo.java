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

/** This class is a FIRST-PASS, CI-UNVERIFIED adapter for Alt-Ergo (2.6.3). Unlike every
 *  other adapter in this package, it could not be developed against a local binary --
 *  no macOS-Intel build exists in the Solvers repo, and there is no Homebrew formula --
 *  so its design is based entirely on Alt-Ergo's published documentation (man page,
 *  official docs, changelog), not empirical testing, and should be treated as a
 *  hypothesis to be corrected once real CI runs against it surface actual behavior.
 *  <p>
 *  Known unknowns going in:
 *  <ul>
 *  <li>Alt-Ergo's own documentation describes it as a whole-file batch prover ({@code
 *  alt-ergo [options] file.smt2}); no stdin/REPL convention is documented anywhere
 *  found. This adapter assumes (unverified) that omitting the file argument makes it
 *  read from stdin, the common Unix convention -- if that assumption is wrong, every
 *  test will likely just hang until runtest's 30s per-test timeout. The fact that
 *  Alt-Ergo's own changelog advertises push/pop/check-sat-assuming incremental support
 *  is what makes stdin streaming seem plausible at all (a purely single-shot batch
 *  prover would have no reason to support those).
 *  <li>{@code --input smtlib2} / {@code --output smtlib2} are confirmed real flags (from
 *  the man page) -- {@code --output smtlib2} in particular is important since Alt-Ergo's
 *  native result format is not sat/unsat/unknown but Valid/Invalid/I don't know.
 *  <li>get-info/get-option/get-model/error-behavior support is entirely unverified --
 *  deliberately NOT overridden here (unlike e.g. Solver_bitwuzla, which overrides based
 *  on confirmed empirical gaps) since guessing wrong would likely introduce incorrect
 *  behavior rather than fix a real one. Left to AbstractSolver's default (forward to
 *  the solver) until CI shows what's actually needed.
 *  <li>Timeout support (--timelimit=SECONDS, per Alt-Ergo's documented options, unverified
 *  against a real binary like the rest of this adapter): Alt-Ergo has only one underlying
 *  numeric limit, applied whole-run by default or per-goal with the --timelimit-per-goal
 *  modifier -- it cannot honor a distinct per-query and whole-run value at the same time,
 *  unlike solvers with two independent flags. See the constructor for how the two
 *  jSMTLIB-level timeout values are reconciled onto this single flag.
 *  </ul> */
public class Solver_altergo extends AbstractSolver implements ISolver {

	/** The command-line arguments for launching the solver. */
	protected String cmds[];

	/** Creates an instance of the solver */
	public Solver_altergo(SMT.Configuration smtConfig, /*@NonNull*/ String executable) {
		this.smtConfig = smtConfig;
		List<String> args = new java.util.ArrayList<String>(Arrays.asList(executable,"--input","smtlib2","--output","smtlib2"));
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
		solverProcess = new SolverProcess(cmds,"\n",smtConfig.logfile,StandardCharsets.UTF_8);
	}

	@Override
	public IResponse start() {
		try {
			solverProcess.start(false);
			// Priming :print-success (see Solver_bitwuzla for why this matters for any
			// solver whose own default might be false): if Alt-Ergo doesn't understand
			// set-option at all, this itself is the first, cheapest signal from CI.
			solverProcess.sendAndListen("(set-option :print-success true)\n");
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Started " + smtConfig.solvername);
			return smtConfig.responseFactory.success();
		} catch (Exception e) {
			return smtConfig.responseFactory.error("Failed to start process " + cmds[0] + " : " + e.getMessage());
		}
	}

}
