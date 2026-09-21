/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.solvers;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.smtlib.ICommand.IScript;
import org.smtlib.ICommand.Ideclare_const;
import org.smtlib.ICommand.Ideclare_fun;
import org.smtlib.ICommand.Ideclare_datatype;
import org.smtlib.ICommand.Ideclare_datatypes;
import org.smtlib.ICommand.Ideclare_sort;
import org.smtlib.ICommand.Ideclare_sort_parameter;
import org.smtlib.ICommand.Idefine_const;
import org.smtlib.ICommand.Idefine_fun_rec;
import org.smtlib.ICommand.Idefine_funs_rec;
import org.smtlib.ICommand.Idefine_sort;
import org.smtlib.*;
import org.smtlib.ICommand.Idefine_fun;
import org.smtlib.IPos.IPosable;
import org.smtlib.IResponse.IAssertionsResponse;
import org.smtlib.IResponse.IAssignmentResponse;
import org.smtlib.IResponse.IAttributeList;
import org.smtlib.IResponse.IProofResponse;
import org.smtlib.IResponse.IUnsatCoreResponse;
import org.smtlib.IResponse.IValueResponse;
import org.smtlib.ISort.IAbbreviation;
import org.smtlib.ISort.IApplication;
import org.smtlib.sexpr.ISexpr;
import org.smtlib.ISort.IFamily;
import org.smtlib.ISort.IFcnSort;
import org.smtlib.ISort.IParameter;
import org.smtlib.IExpr.*;
import org.smtlib.IVisitor.VisitorException;
import org.smtlib.SMT.Configuration.SMTLIB;

// Note - simplify appears to have problems if the set of assertions pushed
// via BG_PUSH are not consistent.  At least, it does not produce counterexample
// information in that case.

/** The adapter that drives the Simplify solver.
 * <P>
 * Note on implementation.  Simplify allows only either pushing an assertion to
 * the background or checking that it is valid.  Assertions that are pushed (via BG_PUSH)
 * appear to be filtered out of counterexamples.  Thus for now we will only use
 * BG_PUSH for background theory axioms; for the rest we will accumulate all assertions
 * into one giant AND (in the conjunction field) and then assert them all at once to Simplify
 * when check-sat is called.  The usual push and pop will not be sent to Simplify - rather
 * we save the state of 'conjunction' ourselves.  This implements the letter if not the
 * spirit of push and pop, and it may have performance implications.  If it does, we'll
 * optimize the implementation then.
 * <p>
 * Several methods (declare_fun, define_fun, pop, push) send an auxiliary command
 * (DEFPRED/BG_PUSH/BG_POP) to the Simplify process and don't inspect its raw response:
 * unlike the main protocol commands (assert, check-sat, ...), nothing in this project's
 * test suite or documentation records what Simplify's failure response for one of these
 * auxiliary commands actually looks like, so there's no format to parse against without
 * guessing (see issue #68).
 * <p>
 * Extends {@link AbstractSolver} (for its real-process plumbing: the shared {@code
 * solverProcess} field, {@code options}/{@code checkSatStatus}), not {@link Solver_test}
 * (issue #97): Simplify's real process speaks its own bespoke, non-SMT-LIB Lisp-like
 * protocol (BG_PUSH/DEFPRED/an accumulated conjunction sent with check-sat -- see above),
 * so {@code AbstractSolver}'s generic defaults (which translate a command to standard
 * SMT-LIB concrete syntax and send that directly) are not usable for Simplify at all --
 * every operation below is either genuinely Simplify-specific (talks to the real process
 * in its own protocol) or a client-side simulation transplanted directly from {@link
 * Solver_test} (the operations Simplify's real process cannot itself be asked about at
 * all: get-model/get-proof/get-unsat-core/etc., reset/reset-assertions, and the
 * declare/define-sort family, none of which the real BG_PUSH-based protocol below has any
 * way to express). {@code symTable}/{@code assertionSetStack}/{@code logicSet} are this
 * class's own copies of exactly what {@code Solver_test} tracks, for exactly the same
 * reason: this class has no real process to ask instead. */
public class Solver_simplify extends AbstractSolver implements ISolver {

	/** The symbol table used for this class's own local type-checking simulation (see the
	 *  class Javadoc) -- a straight copy of {@link Solver_test}'s own field of the same
	 *  name and visibility (public for {@link org.smtlib.ext.C_what}'s sake, though that
	 *  extension command no longer recognizes this class as a symbol-table-bearing solver
	 *  now that it isn't a {@code Solver_test} -- see this session's own restructuring
	 *  notes; no test exercises "what" against Simplify). */
	public SymbolTable symTable;

	/** The data structure that maintains this class's own local simulation of the
	 *  solver's assertion set stack -- see {@link Solver_test#assertionSetStack}. */
	protected List<List<IExpr>> assertionSetStack = new LinkedList<List<IExpr>>();

	/** Internal state variable - set non-null once the logic is set -- see
	 *  {@link Solver_test#logicSet}. */
	protected String logicSet = null;

	/** Just to hold the command line to launch Simplify */
	String cmds[] = new String[1];

	/** Accumulates the translated expressions from various asserts, in order
	 * to send them all at once with a check-sat command.
	 */
	private String conjunction = "";

	/** The stack on which to save instances of 'conjunction' */
	private List<String> pushesStack = new LinkedList<String>();
	{
		pushesStack.add("");
	}

	/** Constructor with standard signature for invocation through reflection */
	public Solver_simplify(SMT.Configuration smtConfig, String executable) {
		this.smtConfig = smtConfig;
		options.putAll(smt().utils.defaults);
		this.symTable = new SymbolTable(smtConfig);
		cmds[0] = executable;
		solverProcess = new SolverProcess(cmds,">\t",smtConfig.logfile,StandardCharsets.UTF_8);
	}

	@Override
	public IResponse start() {
		assertionSetStack.add(0,new LinkedList<IExpr>());
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#start " + solverName());
		solverProcess.start(true);
		try {
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Started simplify");
			solverProcess.sendAndListen("(BG_PUSH (FORALL (B X Y) (IMPLIES (EQ B |@true|) (EQ (" + ite_term + " B X Y) X))))\n");
			solverProcess.sendAndListen("(BG_PUSH (FORALL (B X Y) (IMPLIES (NEQ B |@true|) (EQ (" + ite_term + " B X Y) Y))))\n");
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Failed to assert background formulae at start");
		}
		return smtConfig.responseFactory.success();
	}

	@Override
	public IResponse exit() {
		solverProcess.exit();
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Ended simplify ");
		//process = null;
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#exit " + solverName());
		return smtConfig.responseFactory.success(); // FIXME - should forbid any actions after exited
	}

	// Simplify has no SMT-LIB syntax at all (its own protocol is translated command-by-command
	// elsewhere in this class), so AbstractSolver's generic echo() -- which sends the actual
	// SMT-LIB "(echo ...)" text to the real process -- can't work here; it just gets Simplify's
	// own "Bad" parse-failure response back. echo doesn't need the solver's involvement anyway
	// (it just reports the string back), so answer it locally instead, same as Solver_z3_4_3.
	@Override
	public IResponse echo(IStringLiteral arg) {
		return arg;
	}

	@Override
	public IResponse assertExpr(IExpr expr) {
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#assert " + expr);
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before an assert command is issued");
		}
		List<IResponse> errs = TypeChecker.checkAssertion(this.symTable,expr);
		if (errs != null && !errs.isEmpty()) {
			return errs.get(0);
		}
		if (assertionSetStack.isEmpty()) {
			return smtConfig.responseFactory.error("All assertion sets have been popped from the stack");
		}
		assertionSetStack.get(0).add(expr);
		checkSatStatus = null;
		try {
			String translatedSexpr = translate(expr);
			if (translatedSexpr == null) {
				return smtConfig.responseFactory.error("Failure in translating expression: " + smtConfig.defaultPrinter.toString(expr), expr.pos());
			}
			conjunction = conjunction + " \n" + translatedSexpr;
			//String s = solverProcess.sendAndListen("(BG_PUSH ",translatedSexpr," )\r\n");
			//System.out.println("HEARD: " + s);
		} catch (VisitorException e) {
			return smtConfig.responseFactory.error(e.getMessage(),e.pos);
		}
		return smtConfig.responseFactory.success();
	}

	/** True if :global-declarations has been set. */
	private boolean isGlobal() {
		return Utils.TRUE.equals(options.get(Utils.GLOBAL_DECLARATIONS));
	}

	/** See {@link Solver_test#encode}. */
	protected String encode(IIdentifier id) {
		return id.toString();
	}

	/** Transplanted from {@link Solver_test#reset()}: this class has no real process
	 *  operation to ask for a reset (Simplify's protocol has no such concept), so this
	 *  remains an entirely local, client-side reset exactly as it was as an inherited
	 *  Solver_test method -- it does not, and did not before this restructuring, reset any
	 *  BG_PUSH state already accumulated in the real Simplify process itself. */
	@Override
	public IResponse reset() {
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#reset " + solverName());
		assertionSetStack.clear();
		assertionSetStack.add(0,new LinkedList<IExpr>());
		symTable.clear(false);
		logicSet = null;
		options.putAll(smt().utils.defaults);
		((org.smtlib.impl.Response.Factory)smtConfig.responseFactory).printSuccess = true;
		smtConfig.verbose = 0;
		smtConfig.log.setChannels(smtConfig.stdout, smtConfig.stderr);
		checkSatStatus = null;
		return smtConfig.responseFactory.success();
	}

	/** Transplanted from {@link Solver_test#reset_assertions()}. */
	@Override
	public IResponse reset_assertions() {
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#reset-assertions");
		IResponse r = pop(assertionSetStack.size()-1);
		try {
			for (IExpr e: assertionSetStack.get(0)) TypeChecker.clearSorts(e);
		} catch (IVisitor.VisitorException e) {
			// ignore - clearing sorts is best-effort hygiene, not correctness-critical
		}
		assertionSetStack.get(0).clear();
		if (!isGlobal()) {
			symTable.clear(true);
		}
		return r;
	}

	/** check-sat-assuming postdates Simplify by well over a decade (added in SMT-LIB
	 *  2.6; Simplify's protocol has no concept of it), and this class has no override
	 *  for it -- without one, it silently inherits {@link Solver_test}'s stub (this
	 *  class's superclass, the type-check-only pseudo-solver), which never talks to the
	 *  real Simplify process at all and just echoes back whatever :status a script
	 *  happened to declare (or "unknown" if none), regardless of whether the assumed
	 *  literals are actually satisfiable. That's not a graceful "can't do this," it's a
	 *  wrong answer that looks like a real one. Report it as unsupported instead, matching
	 *  how every other genuinely-unavailable feature in this class (produce-models,
	 *  produce-proofs, etc., in {@link #set_option}) is already handled.
	 *  <p>
	 *  The validation below (logic-set check, then type-checking each assumed literal)
	 *  duplicates {@link Solver_test#check_sat_assuming}'s own precondition checks
	 *  rather than calling {@code super.check_sat_assuming(exprs)} and inspecting the
	 *  result -- that method's only non-error path sets checkSatStatus to the misleading
	 *  status this override exists to avoid, as a side effect that would happen before
	 *  this method ever got a chance to override the *return value*. Real, structural
	 *  errors (bad sorts, undeclared symbols, logic not yet set) should still be
	 *  reported precisely, matching what a real solver would catch before ever getting
	 *  to "I don't support this" -- only well-formed input falls through to unsupported. */
	@Override
	public IResponse check_sat_assuming(IExpr... exprs) {
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a check-sat-assuming command is issued");
		}
		for (IExpr e: exprs) {
			List<IResponse> responses = TypeChecker.check(symTable, e);
			if (!responses.isEmpty()) return responses.get(0);
		}
		checkSatStatus = null;
		return smtConfig.responseFactory.unsupported();
	}

	/** Recursive function definitions postdate Simplify (added in SMT-LIB 2.6) and its
	 *  BG_PUSH-based DEFPRED translation (see {@link #define_fun}/{@link #declare_fun})
	 *  has no way to express recursion. Without an override, {@link Solver_test}'s
	 *  version would register it in the local type-checking symbol table and report
	 *  success without the real Simplify process ever learning about it -- misleading,
	 *  same as {@link #check_sat_assuming}. Validation logic duplicated from {@link
	 *  Solver_test#define_fun_rec} for the same reason given there: real structural
	 *  errors (e.g. an undeclared parameter/result sort) must still be reported
	 *  precisely, not masked behind "unsupported". */
	@Override
	public IResponse define_fun_rec(Idefine_fun_rec cmd) {
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a define-fun-rec command is issued");
		}
		List<IResponse> list = TypeChecker.checkFcnRec(symTable, isGlobal(), cmd.symbol(),
				cmd.parameters(), cmd.resultSort(), cmd.expression());
		if (!list.isEmpty()) return list.get(0);
		return smtConfig.responseFactory.unsupported();
	}

	/** See {@link #define_fun_rec}. */
	@Override
	public IResponse define_funs_rec(Idefine_funs_rec cmd) {
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a define-funs-rec command is issued");
		}
		List<IResponse> list = TypeChecker.checkFcnsRec(symTable, isGlobal(),
				cmd.declarations(), cmd.bodies());
		if (!list.isEmpty()) return list.get(0);
		return smtConfig.responseFactory.unsupported();
	}

	/** Datatypes postdate Simplify (added in SMT-LIB 2.6) and its untyped translation
	 *  (see the class javadoc: "Simplify has no type definitions") has no way to express
	 *  a datatype's constructors/selectors. See {@link #define_fun_rec} for why this
	 *  needs an explicit override rather than falling through to {@link Solver_test}'s
	 *  local-symbol-table-only version. Only name-clash validation is duplicated here
	 *  (via the public, static {@link TypeChecker#validateDatatypeNames}) -- {@link
	 *  Solver_test}'s deeper per-constructor/selector validation and symbol-table
	 *  registration lives in a private method this class cannot reach, and isn't worth
	 *  reimplementing here: nothing declared inside an unsupported datatype could ever
	 *  usefully resolve against Simplify's real (untyped) process anyway. */
	@Override
	public IResponse declare_datatype(Ideclare_datatype cmd) {
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a declare-datatype command is issued");
		}
		List<IResponse> nameErrors = TypeChecker.validateDatatypeNames(symTable, smtConfig,
				Collections.singletonList(cmd.sortDeclaration()),
				Collections.singletonList(cmd.datatype()));
		if (!nameErrors.isEmpty()) return nameErrors.get(0);
		return smtConfig.responseFactory.unsupported();
	}

	/** See {@link #declare_datatype}. */
	@Override
	public IResponse declare_datatypes(Ideclare_datatypes cmd) {
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a declare-datatypes command is issued");
		}
		List<IResponse> nameErrors = TypeChecker.validateDatatypeNames(symTable, smtConfig,
				cmd.sortDeclarations(), cmd.datatypes());
		if (!nameErrors.isEmpty()) return nameErrors.get(0);
		return smtConfig.responseFactory.unsupported();
	}

	@Override
	public IResponse check_sat() {
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#check-sat");
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a check-sat command is issued");
		}
		IResponse res;
		try {
//			String s = solverProcess.sendAndListen("(BG_PUSH (EQ 0 0))\r\n");
//			s = solverProcess.sendAndListen("(EQ 0 1)\r\n");
//			if (s.contains("Valid.")) res = smtConfig.responseFactory.unsat();
//			else if (s.contains("Invalid.")) res = smtConfig.responseFactory.sat();
//			else res = smtConfig.responseFactory.unknown();
			
			String msg = "(NOT (AND TRUE " + conjunction + "\n))\n";
			String s = solverProcess.sendAndListen(msg);
			// Simplify's two real error shapes, confirmed empirically against a live
			// binary (issues #56/#58): "Bad input: <reason>." for a semantic/protocol
			// error (e.g. "Bad input: Unknown predicate symbol: fp.eq." -- this actually
			// happens today, for every current floating-point test, since Simplify has no
			// FP support at all) and "Sx.ReadError in file." for a syntax error Simplify's
			// own reader can't parse (e.g. unbalanced parentheses). Neither ever contains
			// "Valid."/"Invalid.", so checking for them first is unambiguous. Anything
			// else -- genuinely no recognized shape at all -- still falls through to
			// unknown(), rather than guessing at further error shapes with no binary to
			// confirm them against.
			if (s.contains("Valid.")) res = smtConfig.responseFactory.unsat();
			else if (s.contains("Invalid.")) res = smtConfig.responseFactory.sat();
			else if (s.contains("Bad input:") || s.contains("Sx.ReadError")) res = smtConfig.responseFactory.error(s.trim());
			else res = smtConfig.responseFactory.unknown();
			checkSatStatus = res;
//			s = solverProcess.sendAndListen("(BG_POP)\r\n");
			
		} catch (IOException e) {
			res = smtConfig.responseFactory.error("Failed to check-sat");
		}
		return res;
	}

	@Override
	public IResponse declare_fun(Ideclare_fun cmd) {
		IResponse res = declareFunLocal(cmd);
		if (res.isError()) return res;
		try {
			if (cmd.resultSort().isBool() && cmd.argSorts().size() > 0) {
				StringBuilder sb = new StringBuilder();
				sb.append("(DEFPRED (");
				sb.append(translate(cmd.symbol()));
				int n = cmd.argSorts().size();
				for (int i = 0; i<n; i++) {
					sb.append(" X");  // FIXME - fix this
					sb.append(i);
				}
				sb.append("))\n");
				String s = solverProcess.sendAndListen(sb.toString());
				// s (the raw response) intentionally not inspected -- see class doc.
				res = smtConfig.responseFactory.success();
			} else {
				res = smtConfig.responseFactory.success();
			}
		} catch (IOException e) {
			res = smtConfig.responseFactory.error("Failed to declare-fun: " + e.getMessage(),null); // FIXME - position?
		} catch (IVisitor.VisitorException e) {
			res = smtConfig.responseFactory.error("Failed to declare-fun: " + e.getMessage(),null);
		}
		return res;
	}

	@Override
	public IResponse define_fun(Idefine_fun cmd) {
		IResponse res = defineFunLocal(cmd);
		if (res.isError()) return res;
		try {
			if (cmd.resultSort().isBool() && cmd.parameters().size() > 0) {
				StringBuilder sb = new StringBuilder();
				sb.append("(DEFPRED (");
				sb.append(translate(cmd.symbol()));
				int n = cmd.parameters().size();
				for (int i = 0; i<n; i++) {
					sb.append(" X");
					sb.append(i);
				}
				sb.append("))\n");
				String s = solverProcess.sendAndListen(sb.toString());
				// s (the raw response) intentionally not inspected -- see class doc.
				res = smtConfig.responseFactory.success();
			} else {
				res = smtConfig.responseFactory.success();
			}
			IExpr.IFactory f = smtConfig.exprFactory;
			IResponse assertRes = assertExpr(f.fcn(f.symbol("="),cmd.symbol(),cmd.expression()));
			if (!assertRes.isOK()) res = assertRes;

		} catch (IOException e) {
			res = smtConfig.responseFactory.error("Failed to define-fun: " + e.getMessage(),null); // FIXME - position?
		} catch (IVisitor.VisitorException e) {
			res = smtConfig.responseFactory.error("Failed to define-fun: " + e.getMessage(),null);
		}
		return res;
	}

	//@ requires number >= 0;
	@Override
	public IResponse pop(int number) {
		IResponse status = popLocal(number);
		if (!status.isOK()) return status;
		try {
			while (--number >= 0) { 
				conjunction = pushesStack.remove(0);
				String s = solverProcess.sendAndListen("(BG_POP)");
				// s (the raw response) intentionally not inspected -- see class doc.
			}
			return smtConfig.responseFactory.success();
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Failed to push");
		}
	}

	//@ requires number >= 0;
	@Override
	public IResponse push(int number) {
		IResponse status = pushLocal(number);
		if (!status.isOK()) return status;
		try {
			while (--number >= 0) { 
				pushesStack.add(0,conjunction);
				String s = solverProcess.sendAndListen("(BG_PUSH (EQ 0 0))");
				// s (the raw response) intentionally not inspected -- see class doc.
			}
			return smtConfig.responseFactory.success();
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Failed to push");
		}
	}

	@Override
	public IResponse set_logic(String logicName, /*@Nullable*/ IPos pos) {
		// FIXME - discrimninate among logics
		if (logicName.contains("BV")) {
			return smtConfig.responseFactory.error("The simplify solver does not yet support the bit-vector theory",pos);
		}
		boolean lSet = logicSet != null;
		IResponse status = setLogicLocal(logicName,pos);
		if (!status.isOK()) return status;
		if (lSet) {
			pushesStack.clear();
			push(1);
		}
		return smtConfig.responseFactory.success();

	}

	@Override
	public IResponse set_option(IKeyword option, IAttributeValue value) {
		if (option.value().equals(Utils.PRODUCE_ASSIGNMENTS)) return smtConfig.responseFactory.unsupported();
		if (option.value().equals(Utils.PRODUCE_MODELS)) return smtConfig.responseFactory.unsupported();
		if (option.value().equals(Utils.PRODUCE_PROOFS)) return smtConfig.responseFactory.unsupported();
		if (option.value().equals(Utils.PRODUCE_UNSAT_CORES)) return smtConfig.responseFactory.unsupported();
//		if (option.value().equals(":expand-definitions") && smtConfig.atLeastVersion(SMTLIB.V25)) return smtConfig.responseFactory.unsupported();

		return setOptionLocal(option,value);
	}

	@Override
	public IResponse get_option(IKeyword key) {
		String option = key.value();
		if (Utils.INTERACTIVE_MODE.equals(option) && !smtConfig.isVersion(SMTLIB.V20)) option = Utils.PRODUCE_ASSERTIONS;
		IAttributeValue value = options.get(option);
		if (value == null) return smtConfig.responseFactory.unsupported();
		return value;
	}

	@Override
	public IResponse get_info(IKeyword key) {
		IKeyword option = key;
		IAttributeValue lit;
		if (Utils.ERROR_BEHAVIOR.equals(option)) {
			lit = smtConfig.exprFactory.symbol(Utils.CONTINUED_EXECUTION);
		} else if (Utils.AUTHORS.equals(option)) {
			lit = smtConfig.exprFactory.unquotedString("David Detlefs and Greg Nelson and James B. Saxe");
		} else if (Utils.VERSION.equals(option)) {
			lit = smtConfig.exprFactory.unquotedString("1.5.4");
		} else if (Utils.NAME.equals(option)) {
			lit = smtConfig.exprFactory.unquotedString("simplify");
		} else if (Utils.REASON_UNKNOWN.equals(option)) {
			return smtConfig.responseFactory.unsupported();
		} else if (Utils.ALL_STATISTICS.equals(option)) {
			return smtConfig.responseFactory.unsupported();
		} else {
			return smtConfig.responseFactory.unsupported();
		}
		IAttribute<?> attr = smtConfig.exprFactory.attribute(key,lit);
		return smtConfig.responseFactory.get_info_response(attr);
	}

	// ---------------------------------------------------------------------------------
	// Everything below this point is transplanted, unmodified logic from Solver_test's
	// local, client-side type-checking simulation -- see the class Javadoc. Simplify's
	// real process has no way to be usefully asked about any of it (get-model and friends
	// postdate Simplify's own protocol entirely; the declare/define-sort family has no
	// counterpart in Simplify's untyped translation), so this class answers all of it
	// exactly as Solver_test always did, without ever touching solverProcess.
	// ---------------------------------------------------------------------------------

	/** See {@link Solver_test#get_assertions()}. */
	@Override
	public IResponse get_assertions(){
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a get-assertions command is issued");
		}
		if (!smtConfig.relax && !Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_ASSERTIONS)))) {
			return smtConfig.responseFactory.error("The get-assertions command is only valid if " + Utils.produceAssertionsKey(smtConfig) + " has been enabled");
		}
		List<IExpr> combined = new LinkedList<IExpr>();
		Iterator<List<IExpr>> iter = assertionSetStack.listIterator();
		addAssertions(combined,iter);
		return smtConfig.responseFactory.get_assertions_response(combined);
	}

	/** See {@link Solver_test#addAssertions}. */
	private void addAssertions(List<IExpr> combined, Iterator<List<IExpr>> iter) {
		if (iter.hasNext()) {
			List<IExpr> list = iter.next();
			addAssertions(combined,iter);
			combined.addAll(list);
		}
	}

	/** See {@link Solver_test#get_value(IExpr...)}. */
	@Override
	public IResponse get_value(IExpr... terms) {
		TypeChecker tc = new TypeChecker(symTable);
		try {
			for (IExpr term: terms) {
				term.accept(tc);
			}
		} catch (IVisitor.VisitorException e) {
			tc.result.add(smtConfig.responseFactory.error(e.getMessage()));
		} finally {
			if (!tc.result.isEmpty()) return tc.result.get(0);
		}
		if (!Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_MODELS)))) {
			return smtConfig.responseFactory.error("The get-value command is only valid if :produce-models has been enabled");
		}
		if (!smtConfig.responseFactory.sat().equals(checkSatStatus) && !smtConfig.responseFactory.unknown().equals(checkSatStatus)) {
			return smtConfig.responseFactory.error("A get-value command is valid only after check-sat has returned sat or unknown");
		}
		return smtConfig.responseFactory.unsupported();
	}

	/** See {@link Solver_test#get_assignment()}. */
	@Override
	public IResponse get_assignment() {
		if (!Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_ASSIGNMENTS)))) {
			return smtConfig.responseFactory.error("The get-assignment command is only valid if :produce-assignments has been enabled");
		}
		if (!smtConfig.responseFactory.sat().equals(checkSatStatus) && !smtConfig.responseFactory.unknown().equals(checkSatStatus)) {
			return smtConfig.responseFactory.error("The get-assignment command is only valid immediately after check-sat returned sat or unknown");
		}
		return smtConfig.responseFactory.unsupported();
	}

	/** See {@link Solver_test#get_proof()}. */
	@Override
	public IResponse get_proof() {
		if (!Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_PROOFS)))) {
			return smtConfig.responseFactory.error("The get-proof command is only valid if :produce-proofs has been enabled");
		}
		if (!smtConfig.responseFactory.unsat().equals(checkSatStatus)) {
			return smtConfig.responseFactory.error("The get-proof command is only valid immediately after check-sat returned unsat");
		}
		return smtConfig.responseFactory.unsupported();
	}

	/** See {@link Solver_test#get_model()}. */
	@Override
	public IResponse get_model() {
		if (!Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_MODELS)))) {
			return smtConfig.responseFactory.error("The get-model command is only valid if :produce-models has been enabled");
		}
		if (!smtConfig.responseFactory.sat().equals(checkSatStatus) && !smtConfig.responseFactory.unknown().equals(checkSatStatus)) {
			return smtConfig.responseFactory.error("The get-model command is only valid immediately after check-sat returned sat or unknown");
		}
		return smtConfig.responseFactory.unsupported();
	}

	/** See {@link Solver_test#get_unsat_assumptions()}. */
	@Override
	public IResponse get_unsat_assumptions() {
		if (!Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_UNSAT_ASSUMPTIONS)))) {
			return smtConfig.responseFactory.error("The get-unsat-assumptions command is only valid if :produce-unsat-assumptions has been enabled");
		}
		if (!smtConfig.responseFactory.unsat().equals(checkSatStatus)) {
			return smtConfig.responseFactory.error("The get-unsat-assumptions command is only valid immediately after check-sat-assumptions returned unsat");
		}
		return smtConfig.responseFactory.unsupported();
	}

	/** See {@link Solver_test#get_unsat_core()}. */
	@Override
	public IResponse get_unsat_core() {
		if (!Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_UNSAT_CORES)))) {
			return smtConfig.responseFactory.error("The get-unsat-core command is only valid if :produce-unsat-cores has been enabled");
		}
		if (!smtConfig.responseFactory.unsat().equals(checkSatStatus)) {
			return smtConfig.responseFactory.error("The get-unsat-core command is only valid immediately after check-sat returned unsat");
		}
		return smtConfig.responseFactory.unsupported();
	}

	/** See {@link Solver_test#declare_const(ICommand.Ideclare_const)}. */
	@Override
	public IResponse declare_const(Ideclare_const cmd) {
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a declare-const command is issued");
		}
		String encodedName = encode(cmd.symbol());
		List<IResponse> list = TypeChecker.checkFcn(symTable, cmd.symbol(), new LinkedList<ISort>(), cmd.resultSort(),cmd instanceof IPosable ? ((IPosable)cmd).pos(): null);
		if (list.isEmpty()) {
			ISort.IFcnSort fcnSort = smtConfig.sortFactory.createFcnSort(new ISort[0],cmd.resultSort());
			SymbolTable.Entry entry = new SymbolTable.Entry(cmd.symbol(),fcnSort,null,null);
			if (symTable.add(entry, isGlobal(), smtConfig.relax)) {
				checkSatStatus = null;
				return smtConfig.responseFactory.success();
			} else {
				return smtConfig.responseFactory.error("Symbol " + encodedName + " is already defined",cmd.symbol().pos());
			}
		} else {
			return list.get(0);
		}
	}

	/** See {@link Solver_test#declare_fun(ICommand.Ideclare_fun)}: this class's own
	 *  local type-check/registration step, extracted to a helper so {@link #declare_fun}
	 *  can still layer its real-process DEFPRED handling on top, the same way it always
	 *  called {@code super.declare_fun(cmd)} for this half of the work before this
	 *  restructuring. */
	private IResponse declareFunLocal(Ideclare_fun cmd) {
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a declare-fun command is issued");
		}
		if (cmd.parameters() != null && !smtConfig.relax) {
			return smtConfig.responseFactory.error("A par-polymorphic function declaration requires --relax", cmd.symbol().pos());
		}
		if (!cmd.attributes().isEmpty() && !smtConfig.relax) {
			return smtConfig.responseFactory.error("Function attributes on declare-fun require --relax", cmd.symbol().pos());
		}
		String encodedName = encode(cmd.symbol());
		List<IResponse> list = TypeChecker.checkFcn(symTable, cmd.symbol(), cmd.argSorts(),cmd.resultSort(),cmd instanceof IPosable ? ((IPosable)cmd).pos(): null);
		if (list.isEmpty()) {
			ISort.IFcnSort fcnSort = smtConfig.sortFactory.createFcnSort(cmd.argSorts().toArray(new ISort[cmd.argSorts().size()]),cmd.resultSort());
			SymbolTable.Entry entry = new SymbolTable.Entry(cmd.symbol(),fcnSort,cmd.attributes(),cmd.parameters());
			if (symTable.add(entry, isGlobal(), cmd.parameters() != null || smtConfig.relax)) {
				checkSatStatus = null;
				return smtConfig.responseFactory.success();
			} else {
				return smtConfig.responseFactory.error("Symbol " + encodedName + " is already defined",cmd.symbol().pos());
			}
		} else {
			return list.get(0);
		}
	}

	/** See {@link Solver_test#define_const(ICommand.Idefine_const)}. */
	@Override
	public IResponse define_const(Idefine_const cmd) {
		return define_fun(cmd);
	}

	/** See {@link Solver_test#define_fun(ICommand.Idefine_fun)}: extracted the same way
	 *  as {@link #declareFunLocal}, for the same reason. */
	private IResponse defineFunLocal(Idefine_fun cmd) {
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a define-fun command is issued");
		}
		String encodedName = encode(cmd.symbol());
		List<IResponse> list = TypeChecker.checkFcn(symTable, cmd.symbol(), cmd.parameters(),cmd.resultSort(),cmd.expression());
		if (list.isEmpty()) {
			ISort args[] = new ISort[cmd.parameters().size()];
			int i = 0;
			for (IExpr.IDeclaration d: cmd.parameters()) {
				args[i++] = d.sort();
			}
			ISort.IFcnSort fcnSort = smtConfig.sortFactory.createFcnSort(args,cmd.resultSort());
			SymbolTable.Entry entry = new SymbolTable.Entry(cmd.symbol(),fcnSort,null,null);
			entry.definition = cmd.expression();
			if (symTable.add(entry, isGlobal(), false)) {
				checkSatStatus = null;
				return smtConfig.responseFactory.success();
			} else {
				return smtConfig.responseFactory.error("Symbol " + encodedName + " is already defined",cmd.symbol().pos());
			}
		} else {
			return list.get(0);
		}
	}

	/** See {@link Solver_test#declare_sort(ICommand.Ideclare_sort)}. */
	@Override
	public IResponse declare_sort(Ideclare_sort cmd) {
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a declare-sort command is issued");
		}
		List<IResponse> list = TypeChecker.checkSortAbbreviation(symTable,cmd.sortSymbol(),null,null);
		boolean b = list.isEmpty();
		if (b) {
			INumeral sortArity = cmd.arity();
			b = symTable.addSortDefinition(cmd.sortSymbol(), sortArity, null, isGlobal());
			if (!b) return smtConfig.responseFactory.error("The identifier is already declared to be a sort: " +
					smtConfig.defaultPrinter.toString(cmd.sortSymbol()), cmd.sortSymbol().pos());
			checkSatStatus = null;
			return smtConfig.responseFactory.success();
		} else {
			return list.get(0);
		}
	}

	/** See {@link Solver_test#declare_sort_parameter(ICommand.Ideclare_sort_parameter)}. */
	@Override
	public IResponse declare_sort_parameter(Ideclare_sort_parameter cmd) {
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a declare-sort-parameter command is issued");
		}
		List<IResponse> list = TypeChecker.checkSortAbbreviation(symTable, cmd.sortSymbol(), null, null);
		if (!list.isEmpty()) return list.get(0);
		boolean b = symTable.lookupSort(cmd.sortSymbol()) != null;
		if (b) return smtConfig.responseFactory.error("The identifier is already declared to be a sort: " +
								smtConfig.defaultPrinter.toString(cmd.sortSymbol()), cmd.sortSymbol().pos());
		symTable.addSortParameter(cmd.sortSymbol(), isGlobal());
		checkSatStatus = null;
		return smtConfig.responseFactory.success();
	}

	/** See {@link Solver_test#define_sort(ICommand.Idefine_sort)}. */
	@Override
	public IResponse define_sort(Idefine_sort cmd) {
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a define-sort command is issued");
		}
		List<IResponse> list = TypeChecker.checkSortAbbreviation(symTable,cmd.sortSymbol(),cmd.parameters(),cmd.expression());
		boolean b = list.isEmpty();
		if (b) {
			b = symTable.addSortDefinition(cmd.sortSymbol(), cmd.parameters(), cmd.expression(), isGlobal());
			if (!b) return smtConfig.responseFactory.error("The identifier is already declared to be a sort: " +
				smtConfig.defaultPrinter.toString(cmd.sortSymbol()), cmd.sortSymbol().pos());
			else {
				checkSatStatus = null;
				return smtConfig.responseFactory.success();
			}
		} else {
			return list.get(0);
		}
	}

	/** See {@link Solver_test#pop(int)}: extracted the same way as {@link
	 *  #declareFunLocal}, so {@link #pop} can still layer BG_POP handling on top. */
	private IResponse popLocal(int number) {
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#pop " + number);
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a pop command is issued");
		}
		if (number < 0) throw new SMT.InternalException("Internal bug: A pop command called with a negative argument: " + number);
		if (assertionSetStack.size() <= number) {
			return smtConfig.responseFactory.error("The argument to a pop command is too large: " + number + " vs. a maximum of " + (assertionSetStack.size()-1));
		} else {
			int n = number;
			while (--n >= 0) {
				List<IExpr> popped = assertionSetStack.remove(0);
				try {
					for (IExpr e: popped) TypeChecker.clearSorts(e);
				} catch (IVisitor.VisitorException e) {
					// ignore - clearing sorts is best-effort hygiene, not correctness-critical
				}
				symTable.pop();
			}
		}
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("###stack size " + assertionSetStack.size());
		checkSatStatus = null;
		return smtConfig.responseFactory.success();
	}

	/** See {@link Solver_test#push(int)}. */
	private IResponse pushLocal(int number) {
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#push " + number);
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a push command is issued");
		}
		if (number < 0) throw new SMT.InternalException("Internal bug: A push command called with a negative argument: " + number);
		int n = number;
		while (--n >= 0) {
			assertionSetStack.add(0,new LinkedList<IExpr>());
			symTable.push();
		}
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("###stack size " + assertionSetStack.size());
		checkSatStatus = null;
		return smtConfig.responseFactory.success();
	}

	/** See {@link Solver_test#set_logic(String,IPos)}. */
	private IResponse setLogicLocal(String logicName, /*@Nullable*/ IPos pos) {
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#set-logic " + logicName);
		if (logicSet != null) {
			if (!smtConfig.relax) return smtConfig.responseFactory.error("Logic is already set");
			symTable.clear(false);
			assertionSetStack.clear();
			assertionSetStack.add(0,new LinkedList<IExpr>());
			checkSatStatus = null;
		}
		IResponse res = smtConfig.utils.loadLogic(logicName,symTable,pos);
		if (res != null) return res;
		logicSet = logicName;
		return smtConfig.responseFactory.success();
	}

	/** See {@link Solver_test#set_option(IKeyword,IAttributeValue)}. */
	private IResponse setOptionLocal(IKeyword key, IAttributeValue value) {
		String option = key.value();
		if (Utils.PRINT_SUCCESS.equals(option)) {
			if (!(Utils.TRUE.equals(value) || Utils.FALSE.equals(value))) {
				return smtConfig.responseFactory.error("The value of the " + option + " option must be 'true' or 'false'", value.pos());
			} else {
				((org.smtlib.impl.Response.Factory)smtConfig.responseFactory).printSuccess = !Utils.FALSE.equals(value);
			}
		}
		if (logicSet != null && (Utils.GLOBAL_DECLARATIONS.equals(option)||Utils.INTERACTIVE_MODE.equals(option)||Utils.PRODUCE_ASSERTIONS.equals(option))) {
			return smtConfig.responseFactory.error("The value of the " + option + " option must be set before the set-logic command");
		}
		if (Utils.VERBOSITY.equals(option)) {
			IAttributeValue v = options.get(option);
			smtConfig.verbose = (v instanceof INumeral) ? ((INumeral)v).intValue() : 0;
		} else if (Utils.DIAGNOSTIC_OUTPUT_CHANNEL.equals(option)) {
			String name = (value instanceof IStringLiteral)? ((IStringLiteral)value).value() : Utils.STDERR;
			try {
				smtConfig.log.setDiagnosticOutputChannel(name);
			} catch (java.io.IOException e) {
				return smtConfig.responseFactory.error("Failed to open or write to the diagnostic output " + e.getMessage(),value.pos());
			}
		} else if (Utils.REGULAR_OUTPUT_CHANNEL.equals(option)) {
			String name = (value instanceof IStringLiteral)?((IStringLiteral)value).value() : Utils.STDOUT;
			try {
				smtConfig.log.setRegularOutputChannel(name);
			} catch (java.io.IOException e) {
				return smtConfig.responseFactory.error("Failed to open or write to the regular output " + e.getMessage(),value.pos());
			}
		}
		if (Utils.INTERACTIVE_MODE.equals(option) && !smtConfig.isVersion(SMTLIB.V20)) option = Utils.PRODUCE_ASSERTIONS;
		options.put(option,value);
		return smtConfig.responseFactory.success();
	}

	/** See {@link Solver_test#set_info(IKeyword,IAttributeValue)}. */
	@Override
	public IResponse set_info(IKeyword key, IAttributeValue value) {
		if (Utils.infoKeywords.contains(key)) {
			return smtConfig.responseFactory.error("Setting the value of a pre-defined keyword is not permitted: "+
					smtConfig.defaultPrinter.toString(key),key.pos());
		}
		options.put(key.value(),value);
		return smtConfig.responseFactory.success();
	}

	public /*@Nullable*/String translate(IExpr expr) throws IVisitor.VisitorException {
		Translator t = new Translator(smtConfig);
		String r = expr.accept(t);
		if (t.conjuncts.isEmpty()) return r;
		String and = "(AND ";
		for (String c: t.conjuncts) {
			and = and + c + " ";
		}
		and = and + r + " )";
		return and;
	}
	/* Translating simplify:
	 *  Simplify has no type definitions
	 *  It does not require declaring symbols before use - it presumes
	 *  a symbol is a term or a predicate constant or a function when it
	 *  first sees one.  
	 *  New predicates are defined with DEFPRED
	 *  It has a strict distinction between terms and formulas, so
	 *  	- there are different symbols for equality (EQ and IFF)
	 *  	- there are different symbols for inequality (NEQ and (IFF p (NOT q)))
	 *  	- DISTINCT operates only on terms (and the result is a formula)
	 *  
	 *  
	 *  QUESTIONS: what about overloaded functions
	 */
	/*    SMTLIB			SIMPLIFY
	 * FORMULAE:
	 * (or p q r ...)	(OR p q r ...)
	 * (and p q r ...)	(AND p q r ...)
	 * (not p)			(NOT p)
	 * (=> p q r ...)	(IMPLIES p (IMPLIES q r...))
	 * (xor p q r ...)	(NOT ( IFF ( NOT (IFF p q)) r )) ...
	 * (= p q r ...)	(IFF (IFF p q) r)  -- formulas
	 * (= p q r ...)	(AND (EQ p q ) ( EQ q r) ...)  -- terms
	 * (distinct p q r)	-- does not make sense for more than 2 arguments if the arguments are boolean 
	 * (distinct x y z)	(DISTINCT x y z)  -- x,y,z are terms, result is a formula
	 * true				TRUE - when used as a formula
	 * false			FALSE - when used as a formula
	 * (ite b p q)		_ITEB for formula arguments; _ITET for term arguments
	 * 
	 * < <= > >=		< <= > >= - arguments are terms, result is a formula
	 *
	 * TERMS
	 * + - *			+ - *
	 * 	    			select store  - for arrays
	 * 
	 * In simplify EQ NEQ < <= > >= DISTINCT take terms as arguments, produce formulas
	 * how to handle boolean terms???
	 */

	/* Simplify ids:
	 * 		a) sequence of alpha, digits, underscore, beginning with alpha
	 *      b) sequence of ! # $ % & * + - , / : < = > ? @ [ ] ^ _ { } ~
	 *               excludes | ( ) ` \ ; " ' , 
	 * 		c) printable characters and space except \ |, surrounded by |
	 *           - also allows undocumented 'escape sequences'
	 *  To translate from SMT-LIB use form (c), but have to remove
	 *  explicit tabs, newlines, crs; also any \-escape sequences
	 */
	

	/** Name of an if-then-else construct on term arguments */ 
	static private final String ite_term = "_ITE";
	
	static final Map<String,String> fcnNames;
	static final Set<String> logicNames;
	static final Set<String> reservedWords;
	static final Set<String> nonchainables;
	static {
		// FIXME - this builds in the theories - we should abstract both the naming and the mappings for arbitrary arguments
		// Translations of SMT-LIB standard concrete names to Simplify names
		// Anything not here is considered to be uninterpreted and the
		// SMT-LIB name will be encoded into a unique Simplify name
		Map<String,String> fcn = new HashMap<String,String>();
		fcn.put("or","OR");  // >2 arguments OK for simplify (left-assoc)
		fcn.put("not","NOT");
		fcn.put("and","AND");  // >2 arguments OK for simplify (left-assoc)
		fcn.put("=","EQ");		  // >2 arguments NOT OK for simplify (chainable)
		fcn.put("=>","IMPLIES"); // >2 arguments NOT OK for simplify (right-assoc)
		fcn.put("distinct","DISTINCT"); // >2 arguments OK for simplify (pairwise)
		fcn.put("xor","NEQ");			// >2 arguments NOT OK for simplify (left-assoc)
		fcn.put("+","+");				// >2 arguments  OK for simplify (left-assoc)
		fcn.put("-","-");				// >2 arguments NOT OK for simplify (left-assoc)
		fcn.put("*","*");				// >2 arguments  OK for simplify (left-assoc)
		fcn.put(">",">");				// >2 arguments NOT OK for simplify (left-assoc)
		fcn.put(">=",">=");			// >2 arguments NOT OK for simplify (chainable)
		fcn.put("<","<");				// >2 arguments NOT OK for simplify (chainable)
		fcn.put("<=","<=");			// >2 arguments NOT OK for simplify (chainable)
		fcn.put("true","TRUE");
		fcn.put("false","FALSE");
		fcn.put("ite",ite_term);
		fcn.put("select","select");
		fcn.put("store","store");
		fcnNames = Collections.unmodifiableMap(fcn);

		Set<String> nc = new HashSet<String>(Arrays.asList("EQ", ">", "<", ">=", "<=", "IFF"));
		nonchainables = Collections.unmodifiableSet(nc);

		Set<String> rw = new HashSet<String>(Arrays.asList(
			"FORALL","EXISTS","LET",
			"OR","AND","IMPLIES","EXPLIES","XOR","DISTINCT","IFF","NOT","TRUE","FALSE",
			"EQ","NEQ","DISTINCT","PATS",
			"+","-","*",">",">=","<","<=","store","select","@true",
			"LBLPOS","LBLNEG","LBL","ORDER",
			"BG_PUSH","BG_POP","DEFPRED","DEFPREDMAP",
			ite_term
		));
		reservedWords = Collections.unmodifiableSet(rw);

		// These are formulas and take formulas as arguments
		Set<String> logic = new HashSet<String>(Arrays.asList(
			"OR","AND","IMPLIES","EXPLIES","XOR","IFF","NOT","FORALL","EXISTS"));
		logicNames = Collections.unmodifiableSet(logic);
	}
	
	static public class Translator implements IVisitor<String> {
		boolean isFormula = true;
		final private SMT.Configuration smtConfig;
		private List<String> conjuncts = new LinkedList<String>();

		public Translator(SMT.Configuration smtConfig) {
			this.smtConfig = smtConfig;
		}

		@Override
		public String visit(IDecimal e) throws IVisitor.VisitorException {
			throw new VisitorException("The simplify solver cannot handle decimal literals",e.pos());
		}

		@Override
		public String visit(IStringLiteral e) throws IVisitor.VisitorException {
			throw new VisitorException("The simplify solver cannot handle string literals",e.pos());
		}

		@Override
		public String visit(INumeral e) throws IVisitor.VisitorException {
			return e.value().toString();
		}

		@Override
		public String visit(IBinaryLiteral e) throws IVisitor.VisitorException {
			throw new VisitorException("Did not expect a Binary literal in an expression to be translated",e.pos());
		}

		@Override
		public String visit(IHexLiteral e) throws IVisitor.VisitorException {
			throw new VisitorException("Did not expect a Hex literal in an expression to be translated",e.pos());
		}

		@Override
		public String visit(IFcnExpr e) throws IVisitor.VisitorException {
			boolean resultIsFormula = this.isFormula;
			StringBuilder sb = new StringBuilder();
			try {
				Iterator<IExpr> iter = e.args().iterator();
				if (!iter.hasNext()) throw new VisitorException("Did not expect an empty argument list",e.pos());
				if (!(e.head() instanceof ISymbol)) {
					throw new VisitorException("Have not yet implemented parameterized bit-vector functions",e.pos());
				}
				ISymbol fcn = (ISymbol)e.head();
				String newName = fcn.accept(this);
				
				// Determine if the arguments are formulas or terms
				if (resultIsFormula) {
					if (newName != null && logicNames.contains(newName)) {
						// Propositional boolean item
						this.isFormula = true;
					} else if (e.args().size() <= 1) {
						this.isFormula = false;
					} else {
						IExpr arg = e.args().get(1); // Use argument 1 for ite's sake
						ISort sort = arg.sort();
						if (sort == null) {
							throw new VisitorException("INTERNAL ERROR: Encountered an un-sorted expression node: " + smtConfig.defaultPrinter.toString(arg),arg.pos());
						}
						if (sort.isBool()) {
							// Some functions can take both bool and non-bool arguments:
							//   EQ NEQ DISTINCT ite
							this.isFormula = resultIsFormula;
							if ("EQ".equals(newName)) newName = "IFF";
						} else {
							// Arguments must be terms
							this.isFormula = false;
						}
					}
				} else {
					this.isFormula = false;
				}

				ISort s = e.sort();
				if (s == null) {
					throw new VisitorException("INTERNAL ERROR: Encountered an un-sorted expression node: " + smtConfig.defaultPrinter.toString(e),e.pos());
				}
				if (s.isBool() && !resultIsFormula) {
					throw new VisitorException("Use of boolean in a term position is not yet implemented in the Simplify adapter",e.pos()); // FIXME - booleans as terms
				}

				if (isFormula && newName.equals("NEQ")) {
					// for formulas, NEQ is (NOT (IFF p q ...))
					// In simplify, IFF is not implicitly chainable
					int length = e.args().size();
					if ((length&1)==0) sb.append("(NOT ");
					sb.append(leftassoc("IFF",length,iter));
					if ((length&1)==0) sb.append(")");
											
				} else if (newName.equals("IMPLIES")) {
					// right-associative operators that need grouping
					if (!iter.hasNext()) {
						throw new VisitorException("implies (=>) operation without arguments",e.pos());
					}
					sb.append(rightassoc(newName,iter));

				} else if (newName.equals("DISTINCT")) {
					// in simplify, DISTINCT is just for term arguments but the result is a formula
					if (isFormula) {
						// arguments are formulas, result is formula
						if (e.args().size() > 2) {
							// More than two distinct boolean values?
							sb.append("FALSE");
						} else {
							sb.append("(NOT (IFF");
							while (iter.hasNext()) {
								sb.append(" ");
								sb.append(iter.next().accept(this));
							}
							sb.append(" ))");
						}
					} else if (resultIsFormula) {
						// arguments are terms, result is formula - standard use in Simplify
						sb.append("(DISTINCT");
						while (iter.hasNext()) {
							sb.append(" ");
							sb.append(iter.next().accept(this));
						}
						sb.append(")");
					} else {
						// used in a term position
						throw new VisitorException("Use of DISTINCT in a term position is not yet implemented in the Simplify adapter",e.pos()); // FIXME - distinact as a term
					}
				} else if (ite_term.equals(newName)) {
					if (isFormula) {
						sb.append("(AND (IMPLIES ");
						sb.append(e.args().get(0).accept(this));
						sb.append(" ");
						sb.append(e.args().get(1).accept(this));
						sb.append(")");
						sb.append("(IMPLIES (NOT ");
						sb.append(e.args().get(0).accept(this));
						sb.append(") ");
						sb.append(e.args().get(2).accept(this));
						sb.append("))");
					}
				}
				if (e.args().size() > 2 && nonchainables.contains(newName)) {
					Iterator<IExpr> iter2 = e.args().iterator();
					sb.append("(AND ");

					IExpr left = iter2.next();
					while (iter2.hasNext()) {
						IExpr right = iter2.next();
						sb.append("(" + newName + " ");
						sb.append(left.accept(this));
						sb.append(" ");
						sb.append(right.accept(this));
						sb.append(")");
						left = right;
					}
					sb.append(")");
				}
				if (e.args().size() > 2 && (newName.equals("-") || newName.equals("/"))) {
					Iterator<IExpr> iter2 = e.args().iterator();
					sb.append(leftassoc(newName,e.args().size(),iter2));
				}
				
				if (sb.length() == 0) {
					sb.append("( ");
					sb.append(newName);
					while (iter.hasNext()) {
						sb.append(" ");
						sb.append(iter.next().accept(this));
					}
					sb.append(" )");
				}
			} finally {
				this.isFormula = resultIsFormula;
			}
			return sb.toString();
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

		@Override
		public String visit(ISymbol e) throws IVisitor.VisitorException {
			// Symbols do not necessarily have sorts - e.g. if they are function names
			ISort sort = e.sort();
			if (!isFormula && sort != null && sort.isBool()) {
				throw new VisitorException("Use of boolean in a term position is not yet implemented in the Simplify adapter",e.pos()); // FIXME - booleans as terms
			}
			// Simplify does not allow tab, newline, cr in identifiers;
			// these are allowed by SMTLIB.
			// Note that neither simplify nor SMTLIB allows \ or |
			// All other printable characters are allowed in both.
			String oldName = e.value();
			String newName = fcnNames.get(oldName);
			if (newName != null) {
				// There is a direct translation of a pre-defined SMT-LIB name
				// into a simplify equivalent - use it.
			} else {
				// Use the ? character as an escape
				newName = oldName.replace("?","??").replace("\n","?n").replace("\r","?r").replace("\t","?t");
				if (reservedWords.contains(newName)) {
					newName = newName + "?!";
				}
				newName = "|" + newName + "|";
			}
			return newName;
		}

		@Override
		public String visit(IKeyword e) throws IVisitor.VisitorException {
			throw new VisitorException("Did not expect a Keyword in an expression to be translated",e.pos());
		}

		@Override
		public String visit(IError e) throws IVisitor.VisitorException {
			throw new VisitorException("Did not expect a Error token in an expression to be translated",e.pos());
		}

		@Override
		public String visit(IParameterizedIdentifier e) throws IVisitor.VisitorException {
			if (!isFormula && e.sort().isBool()) {
				throw new VisitorException("Use of boolean in a term position is not yet implemented in the Simplify adapter",e.pos()); // FIXME - booleans as terms
			}
			// Since there is no overloading, the head will be a new symbol
			// and we don't need to worry that it collides with a pre- or user-defined
			// function name
			String v = e.headSymbol().accept(this); // This will come back with bars
			if (v.charAt(0) != '|') {
				throw new VisitorException("INTERNAL ERROR: Do not expect to ever have a pre-defined name within a parameterized identifier",e.headSymbol().pos());
			}
			v = v.substring(0,v.length()-1);
			for (IExpr.IIndex n: e.indices()) {
				v = v + "?" + n.toString();
			}
			return v + "|";
		}

		@Override
		public String visit(IForall e) throws IVisitor.VisitorException {
			if (!isFormula) {
				throw new VisitorException("Use of forall in a term position is not yet implemented in the Simplify adapter",e.pos()); // FIXME - booleans as terms
			}
			StringBuilder sb = new StringBuilder();
			sb.append("(FORALL (");
			for (IDeclaration d: e.parameters()) {
				if (d.sort().isBool()) {
					throw new VisitorException("Boolean quantifiers are not implemented in the Simplify adapter",e.pos()); // FIXME - booleans as terms
				}
				sb.append(d.parameter().accept(this));
				sb.append(" ");
			}
			sb.append(") ");
			sb.append(e.expr().accept(this));
			sb.append(")");
			return sb.toString();
		}

		@Override
		public String visit(IExists e) throws IVisitor.VisitorException {
			if (!isFormula) {
				throw new VisitorException("Use of exists in a term position is not yet implemented in the Simplify adapter",e.pos()); // FIXME - booleans as terms
			}
			StringBuilder sb = new StringBuilder();
			sb.append("(EXISTS (");
			for (IDeclaration d: e.parameters()) {
				if (d.sort().isBool()) {
					throw new VisitorException("Boolean quantifiers are not implemented in the Simplify adapter",e.pos()); // FIXME - booleans as terms
				}
				sb.append(d.accept(this));
				sb.append(" ");
			}
			sb.append(") ");
			sb.append(e.expr().accept(this));
			sb.append(")");
			return sb.toString();
		}
		
		@Override 
		public String visit(IDeclaration e) throws IVisitor.VisitorException {
			StringBuilder sb = new StringBuilder();
			sb.append(e.parameter().accept(this));
			return sb.toString();
		}

		@Override
		public String visit(IExpr.IFunctionDeclaration e) throws IVisitor.VisitorException {
			// FIXME
			return null;
		}

		@Override
		public String visit(IExpr.ISortDeclaration e) throws IVisitor.VisitorException {
			// FIXME
			return null;
		}

		@Override
		public String visit(IExpr.ISelector e) throws IVisitor.VisitorException {
			// FIXME
			return null;
		}

		@Override
		public String visit(IExpr.IConstructor e) throws IVisitor.VisitorException {
			// FIXME
			return null;
		}

		@Override
		public String visit(ILet e) throws IVisitor.VisitorException {
			// Simplify does not have let
			// We can create a new temp variable (or function of any quantified parameters)
			// and then use that.
			for (IBinding b : e.bindings()) {
				String r = b.expr().accept(this);
				ISort s = b.expr().sort();
				// FIXME - don't use toString - also need to map to a unique new temporary
				r = (s.isBool()? "(IFF " : "(EQ ") + b.parameter().accept(this) + " " + r + " )";
				conjuncts.add(r);
			}
			return e.expr().accept(this);
			//throw new VisitorException("Use of let is not yet implemented in the Simplify adapter",e.pos()); // FIXME - let in Simplify
		}

		@Override 
		public String visit(IBinding e) throws IVisitor.VisitorException {
//			StringBuilder sb = new StringBuilder();
//			sb.append(e.parameter().accept(this));
//			return sb.toString();
			throw new VisitorException("Use of bindings is not yet implemented in the Simplify adapter",e.pos()); // FIXME - let in Simplify
		}

		@Override
		public String visit(IAttribute<?> e) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IAttributedExpr e) throws VisitorException {
			// FIXME - ignoring the name - should use a LBL expression
			StringBuilder sb = new StringBuilder();
			sb.append("(LBL ");
			sb.append(e.attributes().get(0).attrValue().toString()); // Use the standard printer FIXME
			sb.append(" ");
			sb.append(e.expr().accept(this));
			sb.append(")");
			return sb.toString();
		}

		@Override
		public String visit(org.smtlib.IResponse.IError e)
				throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IAsIdentifier e) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IScript e) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(ICommand e) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IFamily s) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IAbbreviation s) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IApplication s) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IFcnSort s) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IParameter s) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(ILogic s) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(ITheory s) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IResponse e) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IAssertionsResponse e) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IAssignmentResponse e) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IProofResponse e) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IValueResponse e) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IUnsatCoreResponse e) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IResponse.IUnsatAssumptionsResponse e) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IAttributeList e) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(ISexpr.ISeq e) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(ISexpr.IToken<?> e) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

        @Override
        public String visit(ISort.IDatatype e) throws VisitorException {
            // TODO Auto-generated method stub
            return null;
        }

        @Override
        public String visit(IExpr.IMatch e) throws VisitorException {
            return null;
        }

        @Override
        public String visit(IExpr.IMatchCase e) throws VisitorException {
            return null;
        }

        @Override
        public String visit(IExpr.IPattern e) throws VisitorException {
            return null;
        }


//		@Override
//		public String visit(IScript e) throws IVisitor.VisitorException {
//			throw new VisitorException(e,"Did not expect a Script in an expression to be translated");
//		}

//		@Override
//		public String visit(IResponse e) throws IVisitor.VisitorException {
//			throw new VisitorException(e,"Did not expect a IResponse in an expression to be translated");
//		}
//		
	}


}
