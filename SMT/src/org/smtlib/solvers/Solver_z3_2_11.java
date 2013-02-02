package org.smtlib.solvers;

import org.smtlib.IResponse;
import org.smtlib.SMT;

public class Solver_z3_2_11 extends Solver_z3_4_3 {

	/** Creates an instance of the Z3 solver */
	public Solver_z3_2_11(SMT.Configuration smtConfig, /*@NonNull*/ String executable) {
		super(smtConfig,executable);
		cmds = new String[]{ "", "/smt2","/in","/m"}; 
		NAME_VALUE = "z3-2.11";
		VERSION_VALUE = "2.11";
	}

	@Override
	public IResponse start() {
		try {
			solverProcess.start(false);
			// FIXME - enable the following lines when the Z3 solver supports them
//			if (smtConfig.solverVerbosity > 0) solverProcess.sendNoListen("(set-option :verbosity ",Integer.toString(smtConfig.solverVerbosity),")");
//			if (!smtConfig.batch) solverProcess.sendNoListen("(set-option :interactive-mode true)"); // FIXME - not sure we can do this - we'll lose the feedback
			// Can't turn off printing success, or we get no feedback
			//solverProcess.sendAndListen("(set-option :print-success true)\n"); // Z3 4.3.0 needs this because it mistakenly has the default for :print-success as false
			//if (smtConfig.nosuccess) solverProcess.sendAndListen("(set-option :print-success false)");
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("Started Z3-2.11 ");
			return smtConfig.responseFactory.success();
		} catch (Exception e) {
			return smtConfig.responseFactory.error("Failed to start process " + cmds[0] + " : " + e.getMessage());
		}
	}

}
