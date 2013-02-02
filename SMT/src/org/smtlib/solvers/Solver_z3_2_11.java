package org.smtlib.solvers;

import org.smtlib.IAccept;
import org.smtlib.IResponse;
import org.smtlib.IVisitor;
import org.smtlib.SMT;
import org.smtlib.IExpr.IBinaryLiteral;
import org.smtlib.IExpr.IHexLiteral;
import org.smtlib.solvers.Solver_z3_4_3.Translator;

public class Solver_z3_2_11 extends Solver_z3_4_3 {

	/** Creates an instance of the Z3 solver */
	public Solver_z3_2_11(SMT.Configuration smtConfig, /*@NonNull*/ String executable) {
		super(smtConfig,executable);
		cmds = new String[]{ executable, "/smt2","/in","/m"}; 
		solverProcess.setCmd(cmds);
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

	/** Translates an S-expression into Z3 syntax */
	@Override
	protected String translate(IAccept sexpr) throws IVisitor.VisitorException {
		// The z3 solver uses the standard S-expression concrete syntax, but not quite
		// so we have to use our own translator
		return sexpr.accept(new Translator());
	}
	
	public class Translator extends Solver_z3_4_3.Translator {
		
		@Override
		public String visit(IBinaryLiteral e) throws IVisitor.VisitorException {
			return "bv" + e.intValue() + "[" + e.length() + "]";
		}

		@Override
		public String visit(IHexLiteral e) throws IVisitor.VisitorException {
			return "bv" + e.intValue() + "[" + (4*e.length()) + "]";
		}

	}

}
