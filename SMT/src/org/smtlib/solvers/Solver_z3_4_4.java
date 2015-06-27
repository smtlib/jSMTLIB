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

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.io.StringWriter;
import java.io.Writer;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.smtlib.*;
import org.smtlib.ICommand.Ideclare_fun;
import org.smtlib.ICommand.Ideclare_sort;
import org.smtlib.ICommand.Idefine_fun;
import org.smtlib.ICommand.Idefine_sort;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IAttributeValue;
import org.smtlib.IExpr.IFcnExpr;
import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.IQualifiedIdentifier;
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.IParser.ParserException;
import org.smtlib.impl.Pos;
import org.smtlib.sexpr.Printer;

/** This class is an adapter that takes the SMT-LIB ASTs and translates them into Z3 commands */
public class Solver_z3_4_4 extends Solver_smt implements ISolver {
	
//	protected String NAME_VALUE = "z3-4.3";
//	protected String AUTHORS_VALUE = "Leonardo de Moura and Nikolaj Bjorner";
//	protected String VERSION_VALUE = "4.3";
//	
//
//	/** A reference to the SMT configuration */
//	protected SMT.Configuration smtConfig;
//
//	/** A reference to the SMT configuration */
//	public SMT.Configuration smt() { return smtConfig; }
//	
//	/** The command-line arguments for launching the Z3 solver */
//	protected String cmds[];
//	protected String cmds_win[] = new String[]{ "", "/smt2","/in","SMTLIB2_COMPLIANT=true"}; 
//	protected String cmds_mac[] = new String[]{ "", "-smt2","-in","SMTLIB2_COMPLIANT=true"}; 
//	protected String cmds_unix[] = new String[]{ "", "-smt2","-in"}; 
//
//	/** The object that interacts with external processes */
//	protected SolverProcess solverProcess;
//	
//	/** The parser that parses responses from the solver */
//	protected org.smtlib.sexpr.Parser responseParser;
//	
//	/** Set to true once a set-logic command has been executed */
//	private boolean logicSet = false;
//	
//	/** The checkSatStatus returned by check-sat, if sufficiently recent, otherwise null */
//	protected /*@Nullable*/ IResponse checkSatStatus = null;
//	
//	@Override
//	public /*@Nullable*/IResponse checkSatStatus() { return checkSatStatus; }
//
//	/** The number of pushes less the number of pops so far */
//	private int pushesDepth = 0;
//	
//	/** Map that keeps current values of options */
//	protected Map<String,IAttributeValue> options = new HashMap<String,IAttributeValue>();
//	{ 
//		options.putAll(Utils.defaults);
//	}
	
	/** Creates an instance of the Z3 solver */
	public Solver_z3_4_4(SMT.Configuration smtConfig, /*@NonNull*/ String[] command) {
		super(smtConfig, command);
	}

	@Override
	public IResponse start() {
		try {
			solverProcess.start(false);
			// FIXME - enable the following lines when the Z3 solver supports them
//			if (smtConfig.solverVerbosity > 0) solverProcess.sendNoListen("(set-option :verbosity ",Integer.toString(smtConfig.solverVerbosity),")");
//			if (!smtConfig.batch) solverProcess.sendNoListen("(set-option :interactive-mode true)"); // FIXME - not sure we can do this - we'll lose the feedback
			// Can't turn off printing success, or we get no feedback
//			solverProcess.sendAndListen("(set-option :print-success true)\n"); // Z3 4.4.0 needs this because it mistakenly has the default for :print-success as false
			//if (smtConfig.nosuccess) solverProcess.sendAndListen("(set-option :print-success false)");
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("Started Z3-4.4 ");
			return smtConfig.responseFactory.success();
		} catch (Exception e) {
			return smtConfig.responseFactory.error("Failed to start process " + cmds[0] + " : " + e.getMessage());
		}
	}
	
}
