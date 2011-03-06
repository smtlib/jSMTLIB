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
import java.util.*;

import org.smtlib.*;
import org.smtlib.ICommand.Ideclare_fun;
import org.smtlib.ICommand.Ideclare_sort;
import org.smtlib.ICommand.Idefine_fun;
import org.smtlib.ICommand.Idefine_sort;
import org.smtlib.IExpr.IAsIdentifier;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IAttributeValue;
import org.smtlib.IExpr.IAttributedExpr;
import org.smtlib.IExpr.IBinaryLiteral;
import org.smtlib.IExpr.IBinding;
import org.smtlib.IExpr.IDecimal;
import org.smtlib.IExpr.IDeclaration;
import org.smtlib.IExpr.IError;
import org.smtlib.IExpr.IExists;
import org.smtlib.IExpr.IFcnExpr;
import org.smtlib.IExpr.IForall;
import org.smtlib.IExpr.IHexLiteral;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IExpr.ILet;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.IParameterizedIdentifier;
import org.smtlib.IExpr.IQualifiedIdentifier;
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IParser.ParserException;
import org.smtlib.impl.Pos;

/** This class is an adapter that takes the SMT-LIB ASTs and translates them into Z3 commands */
public class Solver_z3 extends AbstractSolver implements ISolver {
	
	protected String NAME_VALUE = "z3";
	protected String AUTHORS_VALUE = "Leonardo de Moura and Nikolaj Bjorner";
	protected String VERSION_VALUE = "2.11-0.0";
	
	/** A reference to the SMT configuration */
	protected SMT.Configuration smtConfig;

	/** A reference to the SMT configuration */
	public SMT.Configuration smt() { return smtConfig; }
	
	/** The command-line arguments for launching the Z3 solver */
	String cmds[] = new String[]{ "", "/smt2","/in","MODEL=true"}; 

	/** The object that interacts with external processes */
	private SolverProcess solverProcess;
	
	/** The parser that parses responses from the solver */
	protected org.smtlib.sexpr.Parser responseParser;
	
	/** Set to true once a set-logic command has been executed */
	private boolean logicSet = false;
	
	/** The checkSatStatus returned by check-sat, if sufficiently recent, otherwise null */
	private /*@Nullable*/ IResponse checkSatStatus = null;
	
	@Override
	public /*@Nullable*/IResponse checkSatStatus() { return checkSatStatus; }

	/** The number of assertions on the top assertion stack */
	private int pushes = 0; // FIXME - not needed
	
	/** A stack storing the numbers of assertions in previous assertion sets */
	private List<Integer> pushesStack = new LinkedList<Integer>();
	{
		pushesStack.add(0);
	}
	
	/** Map that keeps current values of options */
	protected Map<String,IAttributeValue> options = new HashMap<String,IAttributeValue>();
	{ 
		options.putAll(Utils.defaults);
	}
	
	/** Creates an instance of the Z3 solver */
	public Solver_z3(SMT.Configuration smtConfig, /*@NonNull*/ String executable) {
		this.smtConfig = smtConfig;
		cmds[0] = executable;
		solverProcess = new SolverProcess(cmds,"\n","solver.out.z3"); // FIXME - what prompt?
		responseParser = new org.smtlib.sexpr.Parser(smt(),new Pos.Source("",null));
	}
	
	@Override
	public IResponse start() {
		try {
			solverProcess.startNoListen();
			// FIXME - enable the following lines when the Z3 solver supports them
//			if (smtConfig.solverVerbosity > 0) solverProcess.sendNoListen("(set-option :verbosity ",Integer.toString(smtConfig.solverVerbosity),")");
//			if (!smtConfig.batch) solverProcess.sendNoListen("(set-option :interactive-mode true)"); // FIXME - not sure we can do this - we'll lose the feedback
			// Can't turn off printing success, or we get no feedback
			//if (smtConfig.nosuccess) solverProcess.sendAndListen("(set-option :print-success false)");
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("Started Z3 ");
			return smtConfig.responseFactory.success();
		} catch (Exception e) {
			return smtConfig.responseFactory.error("Failed to start process " + cmds[0] + " : " + e.getMessage());
		}
	}
	
	@Override
	public IResponse exit() {
		try {
			solverProcess.sendAndListen("(exit)\n");
			solverProcess.exit();
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("Ended Z3 ");
			//process = null;
			return smtConfig.responseFactory.success_exit();
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	/** Translates an S-expression into Z3 syntax */
	protected String translate(IAccept sexpr) throws IVisitor.VisitorException {
		// The z3 solver uses the standard S-expression concrete syntax, but not quite
		// so we have to use our own translator
		return sexpr.accept(new Translator());
	}
	
	/** Translates an S-expression into standard SMT syntax */
	protected String translateSMT(IAccept sexpr) throws IVisitor.VisitorException {
		// The z3 solver uses the standard S-expression concrete syntax, but not quite
		StringWriter sw = new StringWriter();
		org.smtlib.sexpr.Printer.write(sw,sexpr);
		return sw.toString();
	}
	
	protected IResponse parseResponse(String response) {
		try {
			return responseParser.parseResponse(response);
		} catch (ParserException e) {
			return smtConfig.responseFactory.error("ParserException while parsing response: " + response + " " + e);
		}
	}

	@Override
	public IResponse assertExpr(IExpr sexpr) {
		if (pushesStack.size() == 0) {
			return smtConfig.responseFactory.error("All assertion sets have been popped from the stack");
		}
		if (!logicSet) {
			return smtConfig.responseFactory.error("The logic must be set before an assert command is issued");
		}
		try {
			String s = solverProcess.sendAndListen("(assert ",translate(sexpr),")\n");
			if (s.contains("error")) return smtConfig.responseFactory.error(s);  // FIXME - doubly nested error
			pushes++; // FIXME
			checkSatStatus = null;
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Failed to assert expression: " + e + " " + sexpr);
		} catch (Exception e) {
			return smtConfig.responseFactory.error("Failed to assert expression: " + e + " " + sexpr);
		}
		return smtConfig.responseFactory.success();
	}
	
	@Override
	public IResponse get_assertions() {
		if (!logicSet) {
			return smtConfig.responseFactory.error("The logic must be set before a get-assertions command is issued");
		}
		// FIXME - do we really want to call get-option here? it involves going to the solver?
		if (!smtConfig.relax && !Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.INTERACTIVE_MODE,null)))) {
			return smtConfig.responseFactory.error("The get-assertions command is only valid if :interactive-mode has been enabled");
		}
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
			return smtConfig.responseFactory.error("Unexpected output from the Z3 solver: " + s);
		} catch (IOException e) {
			return smtConfig.responseFactory.error("IOException while reading Z3 reponse");
		}
	}
	


	@Override
	public IResponse check_sat() {
		IResponse res;
		try {
			if (!logicSet) {
				return smtConfig.responseFactory.error("The logic must be set before a check-sat command is issued");
			}
			String s = solverProcess.sendAndListen("(check-sat)\n");
			//smtConfig.log.logDiag("HEARD: " + s);  // FIXME - detect errors - parseResponse?
			
			if (s.contains("unsat")) res = smtConfig.responseFactory.unsat();
			else if (s.contains("sat")) res = smtConfig.responseFactory.sat();
			else res = smtConfig.responseFactory.unknown();
			checkSatStatus = res;
		} catch (IOException e) {
			res = smtConfig.responseFactory.error("Failed to check-sat");
		}
		return res;
	}

	@Override
	public IResponse pop(int number) {
		if (!logicSet) {
			return smtConfig.responseFactory.error("The logic must be set before a pop command is issued");
		}
		if (number < 0) throw new SMT.InternalException("Internal bug: A pop command called with a negative argument: " + number);
		if (number >= pushesStack.size()) return smtConfig.responseFactory.error("The argument to a pop command is too large: " + number + " vs. a maximum of " + (pushesStack.size()-1));
		if (number == 0) return smtConfig.responseFactory.success();
		try {
			checkSatStatus = null;
			while (number-- > 0) {
				pushes = pushesStack.remove(0);
			}
			return parseResponse(solverProcess.sendAndListen("(pop ",new Integer(number).toString(),")\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	@Override
	public IResponse push(int number) {
		if (!logicSet) {
			return smtConfig.responseFactory.error("The logic must be set before a push command is issued");
		}
		if (number < 0) throw new SMT.InternalException("Internal bug: A push command called with a negative argument: " + number);
		checkSatStatus = null;
		if (number == 0) return smtConfig.responseFactory.success();
		try {
			pushesStack.add(pushes);
			while (--number > 0) {
				pushesStack.add(0);
			}
			pushes = 0;
			return parseResponse(solverProcess.sendAndListen("(push ",new Integer(number).toString(),")\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	@Override
	public IResponse set_logic(String logicName, /*@Nullable*/ IPos pos) {
		// FIXME - discrimninate among logics
		
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#set-logic " + logicName);
		if (logicSet) {
			if (!smtConfig.relax) return smtConfig.responseFactory.error("Logic is already set");
			pop(pushesStack.size());
			push(1);
		}
		logicSet = true;
		try {
			return parseResponse(solverProcess.sendAndListen("(set-logic ",logicName,")\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e,pos);
		}
	}

	@Override
	public IResponse set_option(IKeyword key, IAttributeValue value) {
		String option = key.value();
		if (Utils.PRINT_SUCCESS.equals(option)) {
			if (!(Utils.TRUE.equals(value) || Utils.FALSE.equals(value))) {
				return smtConfig.responseFactory.error("The value of the " + option + " option must be 'true' or 'false'");
			}
		}
		if (logicSet && Utils.INTERACTIVE_MODE.equals(option)) {
			return smtConfig.responseFactory.error("The value of the " + option + " option must be set before the set-logic command");
		}
		if (Utils.PRODUCE_ASSIGNMENTS.equals(option) || 
				Utils.PRODUCE_MODELS.equals(option) || 
				Utils.PRODUCE_PROOFS.equals(option) ||
				Utils.PRODUCE_UNSAT_CORES.equals(option)) {
			if (logicSet) return smtConfig.responseFactory.error("The value of the " + option + " option must be set before the set-logic command");
			return smtConfig.responseFactory.unsupported();
		}
		if (Utils.VERBOSITY.equals(option)) {
			IAttributeValue v = options.get(option);
			smtConfig.verbose = (v instanceof INumeral) ? ((INumeral)v).intValue() : 0;
		} else if (Utils.DIAGNOSTIC_OUTPUT_CHANNEL.equals(option)) {
			// Actually, v should never be anything but IStringLiteral - that should
			// be checked during parsing
			String name = (value instanceof IStringLiteral)? ((IStringLiteral)value).value() : "stderr";
			if (name.equals("stdout")) {
				smtConfig.log.diag = System.out;
			} else if (name.equals("stderr")) {
				smtConfig.log.diag = System.err;
			} else {
				try {
					FileOutputStream f = new FileOutputStream(name,true); // true -> append
					smtConfig.log.diag = new PrintStream(f);
				} catch (java.io.IOException e) {
					return smtConfig.responseFactory.error("Failed to open or write to the diagnostic output " + e.getMessage(),value.pos());
				}
			}
		} else if (Utils.REGULAR_OUTPUT_CHANNEL.equals(option)) {
			// Actually, v should never be anything but IStringLiteral - that should
			// be checked during parsing
			String name = (value instanceof IStringLiteral)?((IStringLiteral)value).value() : "stdout";
			if (name.equals("stdout")) {
				smtConfig.log.out = System.out;
			} else if (name.equals("stderr")) {
				smtConfig.log.out = System.err;
			} else {
				try {
					FileOutputStream f = new FileOutputStream(name,true); // append
					smtConfig.log.out = new PrintStream(f);
				} catch (java.io.IOException e) {
					return smtConfig.responseFactory.error("Failed to open or write to the regular output " + e.getMessage(),value.pos());
				}
			}
		}
		if (!Utils.PRINT_SUCCESS.equals(option)) {
			try {
				solverProcess.sendAndListen("(set-option ",option," ",value.toString(),")\n");// FIXME - detect errors
			} catch (IOException e) {
				return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
			}
		}
		

		// Save the options on our side as well
		options.put(option,value);
		return smtConfig.responseFactory.success();
	}

	@Override
	public IResponse get_option(IKeyword key) { // FIXME - use the solver? what types of results?
		String option = key.value();
		IAttributeValue value = options.get(option);
		if (value == null) return smtConfig.responseFactory.unsupported();
		return value;
	}

	@Override
	public IResponse get_info(IKeyword key) { // FIXME - use the solver? what types of results?
		String option = key.value();
		IAttributeValue lit;
		if (Utils.ERROR_BEHAVIOR.equals(option)) {
			lit = smtConfig.exprFactory.symbol(Utils.CONTINUED_EXECUTION,null);
		} else if (Utils.NAME.equals(option)) {
			lit = smtConfig.exprFactory.unquotedString(NAME_VALUE,null);
		} else if (Utils.AUTHORS.equals(option)) {
			lit = smtConfig.exprFactory.unquotedString(AUTHORS_VALUE,null);
		} else if (Utils.VERSION.equals(option)) {
			lit = smtConfig.exprFactory.unquotedString(VERSION_VALUE,null);
			
		} else if (Utils.REASON_UNKNOWN.equals(option)) {
			return smtConfig.responseFactory.unsupported();
		} else if (Utils.ALL_STATISTICS.equals(option)) {
			return smtConfig.responseFactory.unsupported();
		} else {
			return smtConfig.responseFactory.unsupported();
		}
		IAttribute<?> attr = smtConfig.exprFactory.attribute(key,lit,null);
		return smtConfig.responseFactory.get_info_response(attr);
//		try {
//			String s = solverProcess.sendAndListen("(get-info ",option,")\n");// FIXME - detect errors
//			return smtConfig.responseFactory.stringLiteral(s);
//		} catch (IOException e) {
//			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
//		}

//		if (":error-behavior".equals(option)) {
//			return IResponse.CONTINUED_EXECUTION; // FIXME - is this true?
//		} else if (":checkSatStatus".equals(option)) {
//			return checkSatStatus; 
//		} else if (":all-statistics".equals(option)) {
//			return smtConfig.responseFactory.unsupported(); // FIXME
//		} else if (":reason-unknown".equals(option)) {
//			return smtConfig.responseFactory.unsupported(); // FIXME
//		} else if (":authors".equals(option)) {
//			return smtConfig.responseFactory.stringLiteral()("David R. Cok");
//		} else if (":version".equals(option)) {
//			return smtConfig.responseFactory.stringLiteral()("0.0");
//		} else if (":name".equals(option)) {
//			return smtConfig.responseFactory.stringLiteral()("z3");
//		} else {
//			return smtConfig.responseFactory.unsupported();
//		}
	}
	
	@Override
	public IResponse set_info(IKeyword key, IAttributeValue value) {
		String option = key.value();
		if (Utils.infoKeywords.contains(option)) {
			return smtConfig.responseFactory.error("Setting the value of a pre-defined keyword is not permitted: "+ 
					smtConfig.defaultPrinter.toString(key),key.pos());
		}
		options.put(option,value);
		return smtConfig.responseFactory.success();
	}


	@Override
	public IResponse declare_fun(Ideclare_fun cmd) {
		if (!logicSet) {
			return smtConfig.responseFactory.error("The logic must be set before a declare-fun command is issued");
		}
		try {
			checkSatStatus = null;
			return parseResponse(solverProcess.sendAndListen(translate(cmd),"\n"));
			
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	@Override
	public IResponse define_fun(Idefine_fun cmd) {
		if (!logicSet) {
			return smtConfig.responseFactory.error("The logic must be set before a define-fun command is issued");
		}
		try {
			checkSatStatus = null;
			return parseResponse(solverProcess.sendAndListen(translate(cmd),"\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	@Override
	public IResponse declare_sort(Ideclare_sort cmd) {
		if (!logicSet) {
			return smtConfig.responseFactory.error("The logic must be set before a declare-sort command is issued");
		}
		try {
			checkSatStatus = null;
			return parseResponse(solverProcess.sendAndListen(translate(cmd),"\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	@Override
	public IResponse define_sort(Idefine_sort cmd) {
		if (!logicSet) {
			return smtConfig.responseFactory.error("The logic must be set before a define-sort command is issued");
		}
		try {
			checkSatStatus = null;
			return parseResponse(solverProcess.sendAndListen(translate(cmd),"\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}
	
	@Override 
	public IResponse get_proof() {
		if (!Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_PROOFS,null)))) {
			return smtConfig.responseFactory.error("The get-proof command is only valid if :produce-proofs has been enabled");
		}
		if (checkSatStatus != smtConfig.responseFactory.unsat()) {
			return smtConfig.responseFactory.error("The get-proof command is only valid immediately after check-sat returned unsat");
		}
		try {
			return parseResponse(solverProcess.sendAndListen("(get-proof)\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	@Override 
	public IResponse get_unsat_core() {
		if (!Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_UNSAT_CORES,null)))) {
			return smtConfig.responseFactory.error("The get-unsat-core command is only valid if :produce-unsat-cores has been enabled");
		}
		if (checkSatStatus != smtConfig.responseFactory.unsat()) {
			return smtConfig.responseFactory.error("The get-unsat-core command is only valid immediately after check-sat returned unsat");
		}
		try {
			return parseResponse(solverProcess.sendAndListen("(get-unsat-core)\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	@Override 
	public IResponse get_assignment() {
		// FIXME - do we really want to call get-option here? it involves going to the solver?
		if (!Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_ASSIGNMENTS,null)))) {
			return smtConfig.responseFactory.error("The get-assignment command is only valid if :produce-assignments has been enabled");
		}
		if (checkSatStatus != smtConfig.responseFactory.sat() && checkSatStatus != smtConfig.responseFactory.unknown()) {
			return smtConfig.responseFactory.error("The get-assignment command is only valid immediately after check-sat returned sat or unknown");
		}
		try {
			return parseResponse(solverProcess.sendAndListen("(get-assignment)\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	@Override 
	public IResponse get_value(IExpr... terms) {
		// FIXME - do we really want to call get-option here? it involves going to the solver?
		if (!Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_MODELS,null)))) {
			return smtConfig.responseFactory.error("The get-value command is only valid if :produce-models has been enabled");
		}
		if (checkSatStatus != smtConfig.responseFactory.sat() && checkSatStatus != smtConfig.responseFactory.unknown()) {
			return smtConfig.responseFactory.error("The get-value command is only valid immediately after check-sat returned sat or unknown");
		}
		if (!smtConfig.responseFactory.sat().equals(checkSatStatus) || smtConfig.responseFactory.unknown().equals(checkSatStatus)) {
			return smtConfig.responseFactory.error("The checkSatStatus must be sat or unknown for a get-value command");
		}
		try {
			solverProcess.sendNoListen("(get-value (");
			for (IExpr e: terms) {
				solverProcess.sendNoListen("("); // FIXME - too many parentheses?
				solverProcess.sendNoListen(" ",translate(e));
				solverProcess.sendNoListen(")");
			}
			return parseResponse(solverProcess.sendAndListen("))\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	public class Translator extends IVisitor.NullVisitor<String> {
		
		public Translator() {}

		@Override
		public String visit(IDecimal e) throws IVisitor.VisitorException {
			return translateSMT(e);
		}

		@Override
		public String visit(IStringLiteral e) throws IVisitor.VisitorException {
			throw new VisitorException("The Z3 solver cannot handle string literals",e.pos());
		}

		@Override
		public String visit(INumeral e) throws IVisitor.VisitorException {
			return e.value().toString();
		}

		@Override
		public String visit(IBinaryLiteral e) throws IVisitor.VisitorException {
			return "#b" + e.value();
		}

		@Override
		public String visit(IHexLiteral e) throws IVisitor.VisitorException {
			return "#x" + e.value();
		}

		@Override
		public String visit(IFcnExpr e) throws IVisitor.VisitorException {
			Iterator<IExpr> iter = e.args().iterator();
			if (!iter.hasNext()) throw new VisitorException("Did not expect an empty argument list",e.pos());
			IQualifiedIdentifier fcn = e.head();
			String fcnname = fcn.accept(this);
			StringBuilder sb = new StringBuilder();
			int length = e.args().size();
			if (fcnname.equals("=") || fcnname.equals("<") || fcnname.equals(">") || fcnname.equals("<=") || fcnname.equals(">=")) {
				// chainable
				return chainable(fcnname,iter);
			} else if (fcnname.equals("xor")) {
				// left-associative operators that need grouping
				return leftassoc(fcnname,length,iter);
			} else if (length > 1 && fcnname.equals("-")) {
				// left-associative operators that need grouping
				return leftassoc(fcnname,length,iter);
			} else if (fcnname.equals("=>")) {
				// right-associative operators that need grouping
				if (!iter.hasNext()) {
					throw new VisitorException("=> operation without arguments",e.pos());
				}
				return rightassoc(fcnname,iter);
			} else {
				// no associativity 
				sb.append("( ");
				sb.append(fcnname);
				while (iter.hasNext()) {
					sb.append(" ");
					sb.append(iter.next().accept(this));
				}
				sb.append(" )");
				return sb.toString();
			}
		}
			
		//@ requires iter.hasNext();
		private <T extends IExpr> String rightassoc(String fcnname, Iterator<T> iter ) throws IVisitor.VisitorException {
			T n = iter.next();
			if (!iter.hasNext()) {
				return n.accept(this);
			} else {
				StringBuilder sb = new StringBuilder();
				sb.append("(");
				sb.append(fcnname);
				sb.append(" ");
				sb.append(n.accept(this));
				sb.append(" ");
				sb.append(rightassoc(fcnname,iter));
				sb.append(")");
				return sb.toString();
			}
		}

		//@ requires iter.hasNext();
		//@ requires length > 0;
		private <T extends IExpr> String leftassoc(String fcnname, int length, Iterator<T> iter ) throws IVisitor.VisitorException {
			if (length == 1) {
				return iter.next().accept(this);
			} else {
				StringBuilder sb = new StringBuilder();
				sb.append("(");
				sb.append(fcnname);
				sb.append(" ");
				sb.append(leftassoc(fcnname,length-1,iter));
				sb.append(" ");
				sb.append(iter.next().accept(this));
				sb.append(")");
				return sb.toString();
			}
		}
		
		//@ requires iter.hasNext();
		//@ requires length > 0;
		private <T extends IAccept> String chainable(String fcnname, Iterator<T> iter ) throws IVisitor.VisitorException {
			StringBuilder sb = new StringBuilder();
			sb.append("(and ");
			T left = iter.next();
			while (iter.hasNext()) {
				sb.append("(");
				sb.append(fcnname);
				sb.append(" ");
				sb.append(left.accept(this));
				sb.append(" ");
				sb.append((left=iter.next()).accept(this));
				sb.append(")");
			}
			sb.append(")");
			return sb.toString();
		}

		@Override
		public String visit(ISymbol e) throws IVisitor.VisitorException {
			return translateSMT(e);
		}

		@Override
		public String visit(IKeyword e) throws IVisitor.VisitorException {
			throw new VisitorException("Did not expect a Keyword in an expression to be translated",e.pos());
		}

		@Override
		public String visit(IError e) throws IVisitor.VisitorException {
			throw new VisitorException("Did not expect a Error token in an expression to be translated", e.pos());
		}

		@Override
		public String visit(IParameterizedIdentifier e) throws IVisitor.VisitorException {
			return translateSMT(e);
		}

		@Override
		public String visit(IAsIdentifier e) throws IVisitor.VisitorException {
			return translateSMT(e);
		}

		@Override
		public String visit(IForall e) throws IVisitor.VisitorException {
			StringBuffer sb = new StringBuffer();
			sb.append("(forall (");
			for (IDeclaration d: e.parameters()) {
				sb.append("(");
				sb.append(d.parameter().accept(this));
				sb.append(" ");
				sb.append(d.sort().accept(this));
				sb.append(")");
			}
			sb.append(") ");
			sb.append(e.expr().accept(this));
			sb.append(")");
			return sb.toString();
		}

		@Override
		public String visit(IExists e) throws IVisitor.VisitorException {
			StringBuffer sb = new StringBuffer();
			sb.append("(exists (");
			for (IDeclaration d: e.parameters()) {
				sb.append("(");
				sb.append(d.parameter().accept(this));
				sb.append(" ");
				sb.append(d.sort().accept(this));
				sb.append(")");
			}
			sb.append(") ");
			sb.append(e.expr().accept(this));
			sb.append(")");
			return sb.toString();
		}

		@Override
		public String visit(ILet e) throws IVisitor.VisitorException {
			StringBuffer sb = new StringBuffer();
			sb.append("(let (");
			for (IBinding d: e.bindings()) {
				sb.append("(");
				sb.append(d.parameter().accept(this));
				sb.append(" ");
				sb.append(d.expr().accept(this));
				sb.append(")");
			}
			sb.append(") ");
			sb.append(e.expr().accept(this));
			sb.append(")");
			return sb.toString();
		}

		@Override
		public String visit(IAttribute<?> e) throws IVisitor.VisitorException {
			throw new UnsupportedOperationException("visit-IAttribute");
		}

		@Override
		public String visit(IAttributedExpr e) throws IVisitor.VisitorException {
			return e.expr().accept(this); // FIXME - not doing anything with names
		}

		@Override
		public String visit(IDeclaration e) throws IVisitor.VisitorException {
			throw new UnsupportedOperationException("visit-IDeclaration");
		}

		public String visit(ISort.IFamily s) throws IVisitor.VisitorException {
			return s.identifier().accept(this);
		}
		
		public String visit(ISort.IAbbreviation s) throws IVisitor.VisitorException {
			throw new UnsupportedOperationException("visit-ISort.IAbbreviation");
		}
		
		public String visit(ISort.IExpression s) throws IVisitor.VisitorException {
			return translateSMT(s);
		}
		
		public String visit(ISort.IFcnSort s) throws IVisitor.VisitorException {
			throw new UnsupportedOperationException("visit-ISort.IFcnSort");
		}
		public String visit(ISort.IParameter s) throws IVisitor.VisitorException {
			throw new UnsupportedOperationException("visit-ISort.IParameter");
		}
		
		public String visit(ICommand command) throws IVisitor.VisitorException {
			if (command instanceof ICommand.Iassert) {
				return "(assert " + ((ICommand.Iassert)command).expr().accept(this) + ")";
			} else {
				return translateSMT(command);
			}
		}
	}
}