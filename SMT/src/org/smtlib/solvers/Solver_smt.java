/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.solvers;

import java.io.StringWriter;
import java.nio.charset.StandardCharsets;

import org.smtlib.*;
import org.smtlib.impl.Pos;

/** This class is an adapter that takes the SMT-LIB ASTs and translates them into SMT
 *  commands over a solver process speaking plain SMT-LIB, for a solver assumed to be
 *  fully SMT-LIB compliant. It is otherwise a concrete, silent inheritor of {@link
 *  AbstractSolver}: only {@link #translate(INode)} is overridden (a real, solver-
 *  specific deviation — a Bool-quantifier workaround, see {@link
 *  org.smtlib.solvers.Printer}), plus {@link #start()}/{@link #exit()} (process
 *  lifecycle, which AbstractSolver deliberately leaves unimplemented). :verbosity is
 *  just forwarded to the solver like any other option (via AbstractSolver's default
 *  set_option_impl) -- an earlier version of this class instead used a script's
 *  :verbosity value to toggle jSMTLIB's own internal --verbose debug tracing
 *  (smtConfig.verbose), which leaked "#Command to execute: ..." trace lines into the
 *  solver's own response stream. Every other ISolver command — including get_assertions/get_value/
 *  get_assignment/get_unsat_core/get_unsat_assumptions, whose precondition checks and
 *  structured-response parsing now live in AbstractSolver — is inherited unchanged.
 *  <p>
 *  Subclasses of a genuinely non-compliant solver should override {@link
 *  #parseResponse(String)} for their own quirks rather than assuming this class's
 *  behavior; see {@link Solver_yices2#parseResponse(String)} for an example (legacy
 *  bitvector literal syntax, multi-fragment error text) that used to live here as a
 *  blanket default for every Solver_smt subclass, which was more defensive than this
 *  fully-compliant-by-default adapter should assume. */
public class Solver_smt extends AbstractSolver implements ISolver {

	/** The command-line arguments for launching the solver */
	String cmds[];

	/** The parser that parses responses from the solver; also used by subclasses that
	 *  override {@link #parseResponse(String)}. */
	protected org.smtlib.sexpr.Parser responseParser;

	/** Creates an instance of the adapter */
	public Solver_smt(SMT.Configuration smtConfig, /*@NonNull*/ String executable) {
		this.smtConfig = smtConfig;
		cmds = cmd(executable);
		solverProcess = new SolverProcess(cmds,prompt(),smtConfig.logfile,StandardCharsets.UTF_8); // FIXME - what prompt?
		responseParser = new org.smtlib.sexpr.Parser(smt(),new Pos.Source("",null));
	}

	public Solver_smt(SMT.Configuration smtConfig, /*@NonNull*/ String[] args) {
		this.smtConfig = smtConfig;
		cmds = args;
		solverProcess = new SolverProcess(cmds,prompt(),smtConfig.logfile,StandardCharsets.UTF_8); // FIXME - what prompt?
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
			solverProcess.start(false);
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
	public IResponse exit() {
		IResponse response = sendCommand(smtConfig.commandFactory.exit());
		solverProcess.exit();
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Ended SMT ");
		solverProcess = null;
		return response;
	}

}
