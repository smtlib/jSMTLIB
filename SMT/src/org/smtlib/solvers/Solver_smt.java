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

import java.io.IOException;
import java.io.StringWriter;
import java.util.LinkedList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.smtlib.*;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IParser.ParserException;
import org.smtlib.impl.Pos;

/** This class is an adapter that takes the SMT-LIB ASTs and translates them into SMT
 *  commands over a solver process speaking plain SMT-LIB. It is otherwise a concrete
 *  instance of {@link AbstractSolver}: only {@link #translate(INode)} and {@link
 *  #parseResponse(String)} are overridden (real, solver-specific deviations from strict
 *  compliance), plus {@link #start()}/{@link #exit()} (process lifecycle, which
 *  AbstractSolver deliberately leaves unimplemented) and the handful of commands whose
 *  structured response AbstractSolver has no generic way to build. */
public class Solver_smt extends AbstractSolver implements ISolver {

	/** The command-line arguments for launching the solver */
	String cmds[];

	/** The parser that parses responses from the solver */
	protected org.smtlib.sexpr.Parser responseParser;

	/** Creates an instance of the adapter */
	public Solver_smt(SMT.Configuration smtConfig, /*@NonNull*/ String executable) {
		this.smtConfig = smtConfig;
		cmds = cmd(executable);
		solverProcess = new SolverProcess(cmds,prompt(),smtConfig.logfile); // FIXME - what prompt?
		responseParser = new org.smtlib.sexpr.Parser(smt(),new Pos.Source("",null));
	}

	public Solver_smt(SMT.Configuration smtConfig, /*@NonNull*/ String[] args) {
		this.smtConfig = smtConfig;
		cmds = args;
		solverProcess = new SolverProcess(cmds,prompt(),smtConfig.logfile); // FIXME - what prompt?
		responseParser = new org.smtlib.sexpr.Parser(smt(),new Pos.Source("",null));
	}

	public String[] cmd(String exec) {
		return new String[] { exec };
	}

	public String prompt() {
		return "\n";
	}

	@Override
	public IResponse start() {
		try {
			solverProcess.start(true);
			if (smtConfig.solverVerbosity > 0) solverProcess.sendNoListen("(set-option :verbosity ",Integer.toString(smtConfig.solverVerbosity),")");
			//if (!smtConfig.batch) solverProcess.sendNoListen("(set-option :interactive-mode true)"); // FIXME - not sure we can do this - we'll lose the feedback
			// Can't turn off printing success, or we get no feedback
			//if (smtConfig.nosuccess) solverProcess.sendAndListen("(set-option :print-success false)");
			solverProcess.sendAndListen("(set-option :print-success true)");
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Started SMT ");
			return smtConfig.responseFactory.success();
		} catch (Exception e) {
			return smtConfig.responseFactory.error("Failed to start process " + cmds[0] + " : " + e.getMessage());
		}
	}

	/** Translates an S-expression into SMT syntax; this solver uses the standard
	 *  S-expression concrete syntax except for a Bool-quantifier workaround (see
	 *  {@link org.smtlib.solvers.Printer}). */
	@Override
	protected String translate(INode sexpr) throws IVisitor.VisitorException {
		StringWriter sw = new StringWriter();
		org.smtlib.solvers.Printer.write(sw,sexpr);
		return sw.toString();
	}

	@Override
	protected IResponse parseResponse(String response) {
		try {
			//FIXME
			Pattern oldbv = Pattern.compile("bv([0-9]+)\\[([0-9]+)\\]");
			Matcher mm = oldbv.matcher(response);
			while (mm.find()) {
				long val = Long.parseLong(mm.group(1));
				int base = Integer.parseInt(mm.group(2));
				String bits = "";
				for (int i=0; i<base; i++) { bits = ((val&1)==0 ? "0" : "1") + bits; val = val >>> 1; }
				response = response.substring(0,mm.start()) + "#b" + bits + response.substring(mm.end(),response.length());
				mm = oldbv.matcher(response);
			}
			if (response.contains("error")) {
				// returns an s-expr (always?)
				// FIXME - (1) the {Print} also needs {Space}; (2) err_getValueTypes.tst returns a non-error s-expr and then an error s-expr - this fails for that case
				//Pattern p = Pattern.compile("\\p{Space}*\\(\\p{Blank}*error\\p{Blank}+\"(([\\p{Space}\\p{Print}^[\\\"\\\\]]|\\\\\")*)\"\\p{Blank}*\\)\\p{Space}*");
				Pattern p = Pattern.compile("\\p{Space}*\\(\\p{Blank}*error\\p{Blank}+\"(([\\p{Print}\\p{Space}&&[^\"\\\\]]|\\\\\")*)\"\\p{Blank}*\\)");
				Matcher m = p.matcher(response);
				String concat = "";
				while (m.lookingAt()) {
					if (!concat.isEmpty()) concat = concat + "; ";
					String matched = m.group(1);
					concat = concat + matched;
					m.region(m.end(0),m.regionEnd());
				}
				if (!concat.isEmpty()) response = concat;
				return smtConfig.responseFactory.error(response);
			}
			responseParser = new org.smtlib.sexpr.Parser(smt(),new Pos.Source(response,null));
			return responseParser.parseResponse(response);
		} catch (ParserException e) {
			return smtConfig.responseFactory.error("ParserException while parsing response: " + response + " " + e);
		}
	}

	@Override
	public IResponse exit() {
		IResponse response = sendCommand(smtConfig.commandFactory.exit());
		solverProcess.exit();
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Ended SMT ");
		solverProcess = null;
		return response;
	}

	@Override
	public IResponse get_assertions() {
		// FIXME - do we really want to call get-option here? it involves going to the solver?
		try {
			StringBuilder sb = new StringBuilder();
			String s;
			int parens = 0;
			do {
				s = solverProcess.sendAndListen("(get-assertions)\n");
				int p = -1;
				while (( p = s.indexOf('(',p+1)) != -1) parens++;
				p = -1;
				while (( p = s.indexOf(')',p+1)) != -1) parens--;
				sb.append(s.replace('\n',' ').replace("\r",""));
			} while (parens > 0);
			s = sb.toString();
			org.smtlib.sexpr.Parser p = new org.smtlib.sexpr.Parser(smtConfig,new org.smtlib.impl.Pos.Source(s,null));
			List<IExpr> exprs = new LinkedList<IExpr>();
			try {
				if (p.isLP()) {
					p.parseLP();
					while (!p.isRP() && !p.isEOD()) {
						IExpr e = p.parseExpr();
						exprs.add(e);
					}
					if (p.isRP()) {
						p.parseRP();
						if (p.isEOD()) return smtConfig.responseFactory.get_assertions_response(exprs);
					}
				}
			} catch (Exception e ) {
				// continue - fall through
			}
			return smtConfig.responseFactory.error("Unexpected output from the solver: " + s);
		} catch (IOException e) {
			return smtConfig.responseFactory.error("IOException while reading solver's reponse");
		}
	}

	@Override
	protected IResponse set_option_impl(IKeyword key, IAttributeValue value) {
		String option = key.value();
		if (Utils.PRINT_SUCCESS.equals(option)) {
			if (!(Utils.TRUE.equals(value) || Utils.FALSE.equals(value))) {
				return smtConfig.responseFactory.error("The value of the " + option + " option must be 'true' or 'false'");
			}
			// Already sent during start(); don't re-send.
			return smtConfig.responseFactory.success();
		}
		if (Utils.VERBOSITY.equals(option)) {
			smtConfig.verbose = (value instanceof INumeral) ? ((INumeral)value).intValue() : 0;
		}
		return sendCommand(smtConfig.commandFactory.set_option(key, value));
	}

	@Override
	public IResponse get_proof() {
		return sendCommand(smtConfig.commandFactory.get_proof());
	}

	@Override
	public IResponse get_unsat_core() {
		return sendCommand(smtConfig.commandFactory.get_unsat_core());
	}

	@Override
	public IResponse get_assignment() {
		return sendCommand(smtConfig.commandFactory.get_assignment());
	}

	@Override
	public IResponse get_value(IExpr... terms) {
		return sendCommand(smtConfig.commandFactory.get_value(java.util.Arrays.asList(terms)));
	}

}
