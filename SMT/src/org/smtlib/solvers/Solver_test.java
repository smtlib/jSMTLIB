/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.solvers;

import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.*;

import org.smtlib.*;
import org.smtlib.ICommand.*;
import org.smtlib.IExpr.*;
import org.smtlib.IPos.IPosable;
import org.smtlib.SMT.Configuration.SMTLIB;
import org.smtlib.impl.Response;

/** This class is a Solver implementation that simply type-checks formulae and checks that
 * commands are used correctly; it does not do any proving.
 */
public class Solver_test implements ISolver {
    
    @Override
    public String solverName() { return "test"; }

	/** A reference to the configuration used by this SMT instance. */
	protected SMT.Configuration smtConfig;

	/** Returns the reference to the configuration currently in use. */
	@Override
	public SMT.Configuration smt() { return smtConfig; }

	/** The symbol table used by this solver */
	public SymbolTable symTable; // TODO - public for the sake of C_what - change to protected
	
	/** The data structure that maintains the solver's assertion set stack */
	protected List<List<IExpr>> assertionSetStack = new LinkedList<List<IExpr>>();
	
	/** Internal state variable - set non-null once the logic is set. */
	protected String logicSet = null;
	
	/** Internal state variable - set to sat, unsat, unknown when check-sat is run
	 * and then to null whenever an additional push, pop, assert, declare- or define-
	 * command is executed.  This is used in checking those commands that depend on the
	 * above set of conditions.
	 */
	protected /*@Nullable*/IResponse checkSatStatus = null;
	
	@Override
	public /*@Nullable*/IResponse checkSatStatus() { return checkSatStatus; }

	/** The data structure that maintains the current values of options and info items for this solver. */
	protected Map<String,IAttributeValue> options = new HashMap<String,IAttributeValue>();
	
	
	
	/** Constructor for an instance of this test solver class; the second argument is ignored - it is 
	 * present just for uniformity with other solvers, for which that argument is a path to the relevant
	 * executable.  This constructor is called by reflection, upon knowing the name of the solver ("test").
	 * @param smtConfig a reference to the configuration instance in use
	 * @param exec the executable for the solver, ignored for the case of this test solver
	 */
	public Solver_test(SMT.Configuration smtConfig, String exec) {
		this.smtConfig = smtConfig;
		options.putAll(smt().utils.defaults);
		this.symTable = new SymbolTable(smtConfig);
	}

	private boolean isGlobal() {
		return Utils.TRUE.equals(options.get(Utils.GLOBAL_DECLARATIONS));
	}
	
	@Override
	public IResponse start() {
		assertionSetStack.add(0,new LinkedList<IExpr>());
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#start " + solverName());
		return smtConfig.responseFactory.success();
	}
	
	@Override
	public IResponse reset() {
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#reset " + solverName());
		assertionSetStack.clear();
		assertionSetStack.add(0,new LinkedList<IExpr>());
		symTable.clear(false);
		logicSet = null;
		// Set all options and info to default values
		options.putAll(smt().utils.defaults);
		((Response.Factory)smtConfig.responseFactory).printSuccess = true;
		smtConfig.verbose = 0;
		smtConfig.log.out = smtConfig.stdout;
		smtConfig.log.diag = smtConfig.stderr;
		checkSatStatus = null;

		return smtConfig.responseFactory.success();
	}

	@Override public void comment(String comment) {
		// No action
	}
	
	@Override
	public IResponse reset_assertions() {
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#reset-assertions");
		// Remove all pushed frames
		IResponse r = pop(assertionSetStack.size()-1);
		// Remove assertions, but not necessarily global declarations
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

	@Override
	public IResponse exit() {
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#exit " + solverName());
		return smtConfig.responseFactory.success(); // FIXME - should forbid any actions after exited
	}
	
	@Override
	public void forceExit() {
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#forceexit " + solverName());
	} // FIXME - should forbid any actions after exited
	
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
			// The SMT-LIB response protocol accommodates only one response per command --
			// (error <string>) is a single object, not a list -- so at most one error message
			// can ever be returned here regardless of how many TypeChecker actually found.
			// Real solvers (z3, cvc5, yices2, SMTInterpol -- confirmed directly against each)
			// appear to fail-fast: they stop at the first problem encountered while
			// elaborating an asserted expression and never discover, let alone report, any
			// later ones in the same command. TypeChecker.checkAssertion(), by contrast,
			// does a full pass and can return multiple errors when several are present;
			// returning only errs.get(0) here matches that real-solver fail-fast behavior
			// rather than being a shortcut that should eventually return the rest -- there is
			// no wire format for "the rest" to be returned in.
			return errs.get(0);
		}
		if (assertionSetStack.isEmpty()) {
			return smtConfig.responseFactory.error("All assertion sets have been popped from the stack");
		}
		assertionSetStack.get(0).add(expr);
		checkSatStatus = null;
		return smtConfig.responseFactory.success();
	}
	
	@Override
	public IResponse get_assertions() {
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a get-assertions command is issued");
		}
		// FIXME - do we really want to call get-option here? it involves going to the solver?
		if (!smtConfig.relax && !Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_ASSERTIONS)))) {
			String key;
			if (smtConfig.atLeastVersion(SMTLIB.V25)) key = ":produce-assertions";
			else key = ":interactive-mode";
			return smtConfig.responseFactory.error("The get-assertions command is only valid if " + key + " has been enabled");
		}
		List<IExpr> combined = new LinkedList<IExpr>();
		Iterator<List<IExpr>> iter = assertionSetStack.listIterator();
		addAssertions(combined,iter);
		return smtConfig.responseFactory.get_assertions_response(combined);
	}
	
	/** This method adds all the IExpr items in the lists produced from the iter argument into
	 * the list referenced by the combined argument; the resulting order is to have the items on the
	 * end of the iter sequence added first into the combined list.
	 * @param combined the resulting combined, in-order, sequence of 
	 * @param iter an iterator producing a sequence of Lists of IExpr
	 */
	private void addAssertions(List<IExpr> combined, Iterator<List<IExpr>> iter) {
		if (iter.hasNext()) {
			List<IExpr> list = iter.next();
			addAssertions(combined,iter);
			combined.addAll(list);
		}
	}

	@Override
	public IResponse check_sat() {
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#check-sat");
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a check-sat command is issued");
		}
		checkSatStatus = statusResult();
		return checkSatStatus;
	}

	/** Since this solver never actually proves anything, check-sat/check-sat-assuming never
	 * error out on a status mismatch the way a real solver is expected to; instead, if :status
	 * has been declared via set-info, they adopt that value (sat/unsat/unknown) as their own
	 * result, otherwise returning unknown. This lets tests exercise the get-model/get-value/
	 * get-proof/get-unsat-core/get-unsat-assumptions/get-assignment preconditions (which all
	 * depend on the check-sat result) without a real proving solver. */
	private IResponse statusResult() {
		IAttributeValue status = options.get(Utils.STATUS.value());
		if (smtConfig.responseFactory.sat().equals(status)) return smtConfig.responseFactory.sat();
		if (smtConfig.responseFactory.unsat().equals(status)) return smtConfig.responseFactory.unsat();
		return smtConfig.responseFactory.unknown();
	}
	
	@Override
	public IResponse check_sat_assuming(IExpr ... exprs) {
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#check-sat-assuming");
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a check-sat-assuming command is issued");
		}
		for (IExpr e: exprs) {
			List<IResponse> responses = TypeChecker.check(symTable, e);
			if (!responses.isEmpty()) return responses.get(0); // FIXME - return all?
		}
		
		checkSatStatus = statusResult();
		return checkSatStatus;
	}

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
			if (!tc.result.isEmpty()) return tc.result.get(0); // FIXME - report all errors?
		}
		if (!Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_MODELS)))) {
			return smtConfig.responseFactory.error("The get-value command is only valid if :produce-models has been enabled");
		}
		if (!smtConfig.responseFactory.sat().equals(checkSatStatus) && !smtConfig.responseFactory.unknown().equals(checkSatStatus)) {
			return smtConfig.responseFactory.error("A get-value command is valid only after check-sat has returned sat or unknown");
		}
		return smtConfig.responseFactory.unsupported();
	}

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

	@Override
	public IResponse pop(int number) {
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#pop " + number);
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a pop command is issued");
		}
		if (number < 0) throw new SMT.InternalException("Internal bug: A pop command called with a negative argument: " + number);
		if (assertionSetStack.size() <= number) {
			return smtConfig.responseFactory.error("The argument to a pop command is too large: " + number + " vs. a maximum of " + (assertionSetStack.size()-1));
		} else {
			while (--number >= 0) {
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

	@Override
	public IResponse push(int number) {
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#push " + number);
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a push command is issued");
		}
		if (number < 0) throw new SMT.InternalException("Internal bug: A push command called with a negative argument: " + number);
		while (--number >= 0) { 
			assertionSetStack.add(0,new LinkedList<IExpr>()); 
			symTable.push(); 
		}
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("###stack size " + assertionSetStack.size());
		checkSatStatus = null;
		return smtConfig.responseFactory.success();
	}

	@Override
	public IResponse set_logic(String logicName, /*@Nullable*/ IPos pos) {
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
	
	@Override
	public IResponse set_option(IKeyword key, IAttributeValue value) { // FIXME - only strictlyl supported options
		String option = key.value();
		if (Utils.PRINT_SUCCESS.equals(option)) {
			if (!(Utils.TRUE.equals(value) || Utils.FALSE.equals(value))) {
				// This message is duplicated in the C_set_option constructor
//				return smtConfig.responseFactory.error("The value of the " + option + " option must be 'true' or 'false'");
			} else {
				// FIXME - make this more abstract
				((Response.Factory)smtConfig.responseFactory).printSuccess = !Utils.FALSE.equals(value);
			}
		}
		if (logicSet != null && (Utils.GLOBAL_DECLARATIONS.equals(option)||Utils.INTERACTIVE_MODE.equals(option)||Utils.PRODUCE_ASSERTIONS.equals(option))) {
			return smtConfig.responseFactory.error("The value of the " + option + " option must be set before the set-logic command");
		}
//		if (Utils.PRODUCE_ASSIGNMENTS.equals(option) || 
//				//Utils.PRODUCE_MODELS.equals(option) || 
//				Utils.PRODUCE_PROOFS.equals(option) ||
//				Utils.PRODUCE_UNSAT_CORES.equals(option)) {
//			if (logicSet) return smtConfig.responseFactory.error("The value of the " + option + " option must be set before the set-logic command");
//			return smtConfig.responseFactory.unsupported();
//		}
		if (Utils.VERBOSITY.equals(option)) {
			IAttributeValue v = options.get(option);
			smtConfig.verbose = (v instanceof INumeral) ? ((INumeral)v).intValue() : 0;
		} else if (Utils.DIAGNOSTIC_OUTPUT_CHANNEL.equals(option)) {
			// Actually, v should never be anything but IStringLiteral - that should
			// be checked during parsing
			String name = (value instanceof IStringLiteral)? ((IStringLiteral)value).value() : Utils.STDERR;
			if (name.equals(Utils.STDOUT)) {
				smtConfig.log.diag = smtConfig.stdout;
			} else if (name.equals(Utils.STDERR)) {
				smtConfig.log.diag = smtConfig.stderr;
			} else {
				try {
					FileOutputStream f = new FileOutputStream(name,true); // append
					smtConfig.log.diag = new PrintStream(f);
				} catch (java.io.IOException e) {
					return smtConfig.responseFactory.error("Failed to open or write to the diagnostic output " + e.getMessage(),value.pos());
				}
			}
		} else if (Utils.REGULAR_OUTPUT_CHANNEL.equals(option)) {
			// Actually, v should never be anything but IStringLiteral - that should
			// be checked during parsing
			String name = (value instanceof IStringLiteral)?((IStringLiteral)value).value() : Utils.STDOUT;
			if (name.equals(Utils.STDOUT)) {
				smtConfig.log.out = smtConfig.stdout;
			} else if (name.equals(Utils.STDERR)) {
				smtConfig.log.out = smtConfig.stderr;
			} else {
				try {
					FileOutputStream f = new FileOutputStream(name,true); // append
					smtConfig.log.out = new PrintStream(f);
				} catch (java.io.IOException e) {
					return smtConfig.responseFactory.error("Failed to open or write to the regular output " + e.getMessage(),value.pos());
				}
			}
		}
		if (Utils.INTERACTIVE_MODE.equals(option) && !smtConfig.isVersion(SMTLIB.V20)) option = Utils.PRODUCE_ASSERTIONS;
		options.put(option,value);
		return smtConfig.responseFactory.success();
	}

	@Override
	public IResponse get_option(IKeyword key) {
		String v = key.value();
		if (Utils.INTERACTIVE_MODE.equals(v) && !smtConfig.isVersion(SMTLIB.V20)) v = Utils.PRODUCE_ASSERTIONS;
		IAttributeValue value = options.get(v);
		//if (smtConfig.isVersion(SMTLIB.V20))
		if (value == null) return smtConfig.responseFactory.unsupported();
		return value;
	}
	
	@Override
	public IResponse set_info(IKeyword key, IAttributeValue value) {
		if (Utils.infoKeywords.contains(key)) {
			return smtConfig.responseFactory.error("Setting the value of a pre-defined keyword is not permitted: "+ 
					smtConfig.defaultPrinter.toString(key),key.pos());
		}
		options.put(key.value(),value);
		return smtConfig.responseFactory.success();
	}

	@Override
	public IResponse get_info(IKeyword key) { // FIXME - only strictly supported infoflags
		IKeyword option = key;
		IAttributeValue lit;
		if (Utils.ERROR_BEHAVIOR.equals(option)) {
			lit = smtConfig.exprFactory.symbol(Utils.CONTINUED_EXECUTION);
		} else if (Utils.NAME.equals(option)) {
			lit = smtConfig.exprFactory.unquotedString(org.smtlib.Utils.TEST_SOLVER);
		} else if (Utils.AUTHORS.equals(option)) {
			lit = smtConfig.exprFactory.unquotedString(Utils.AUTHORS_VALUE);
		} else if (Utils.VERSION.equals(option)) {
			lit = smtConfig.exprFactory.unquotedString(Utils.VERSION_VALUE);
			
		} else if (Utils.REASON_UNKNOWN.equals(option)) {
			return smtConfig.responseFactory.unsupported();
		} else if (Utils.ALL_STATISTICS.equals(option)) {
			return smtConfig.responseFactory.unsupported();
		} else if (Utils.ASSERTION_STACK_LEVELS.equals(option)) {
			// assertionSetStack always has one base frame (added by start()/reset()), plus
			// one additional frame per unmatched push -- so size-1 is the push depth.
			lit = smtConfig.exprFactory.numeral(assertionSetStack.size() - 1);
			
//		} else if ((value = Utils.stringInfo.get(option)) != null) {
//			lit = smtConfig.exprFactory.unquotedString(value);
		} else {
			return smtConfig.responseFactory.unsupported();
		}
		IAttribute<?> attr = smtConfig.exprFactory.attribute(key,lit);
		return smtConfig.responseFactory.get_info_response(attr);
	}
	
	protected String encode(IIdentifier id) {
		return id.toString(); // FIXME composite definitions; encode the String?
	}

	@Override 
	public IResponse declare_const(Ideclare_const cmd) {
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a declare-const command is issued");// FIXME - position and on other similar statements
		}
		String encodedName = encode(cmd.symbol());
		List<IResponse> list = TypeChecker.checkFcn(symTable, cmd.symbol(), new LinkedList<ISort>(), cmd.resultSort(),cmd instanceof IPosable ? ((IPosable)cmd).pos(): null);
		if (list.isEmpty()) {
			ISort.IFcnSort fcnSort = smtConfig.sortFactory.createFcnSort(new ISort[0],cmd.resultSort());
			SymbolTable.Entry entry = new SymbolTable.Entry(cmd.symbol(),fcnSort,null);
			if (symTable.add(entry, isGlobal(), false)) {
				checkSatStatus = null;
				return smtConfig.responseFactory.success();
			} else {
				return smtConfig.responseFactory.error("Symbol " + encodedName + " is already defined",cmd.symbol().pos());
			}
		} else {
			return list.get(0); // FIXME - return all?
		}
	}

	@Override
	public IResponse declare_fun(Ideclare_fun cmd) {
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a declare-fun command is issued");// FIXME - position and on other similar statements
		}
		String encodedName = encode(cmd.symbol());
		List<IResponse> list = TypeChecker.checkFcn(symTable, cmd.symbol(), cmd.argSorts(),cmd.resultSort(),cmd instanceof IPosable ? ((IPosable)cmd).pos(): null);
		if (list.isEmpty()) {
			ISort.IFcnSort fcnSort = smtConfig.sortFactory.createFcnSort(cmd.argSorts().toArray(new ISort[cmd.argSorts().size()]),cmd.resultSort());
			SymbolTable.Entry entry = new SymbolTable.Entry(cmd.symbol(),fcnSort,null);
			if (symTable.add(entry, isGlobal(), false)) {
				checkSatStatus = null;
				return smtConfig.responseFactory.success();
			} else {
				return smtConfig.responseFactory.error("Symbol " + encodedName + " is already defined",cmd.symbol().pos());
			}
		} else {
			return list.get(0); // FIXME - return all?
		}
	}

	@Override
	public IResponse define_const(Idefine_const cmd) {
		return define_fun(cmd);
	}

	@Override
	public IResponse define_fun(Idefine_fun cmd) {
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a define-fun command is issued");
		}
		String encodedName = encode(cmd.symbol());
		List<IResponse> list = TypeChecker.checkFcn(symTable, cmd.symbol(), cmd.parameters(),cmd.resultSort(),cmd.expression(),cmd instanceof IPosable ? ((IPosable)cmd).pos(): null);
		if (list.isEmpty()) {
			ISort args[] = new ISort[cmd.parameters().size()];
			int i = 0;
			for (IExpr.IDeclaration d: cmd.parameters()) {
				args[i++] = d.sort(); // FIXME - use resolved sort?
				//newp.add(smtConfig.exprFactory.declaration(d.parameter(),d.sort(),d.pos()));
			}
			ISort.IFcnSort fcnSort = smtConfig.sortFactory.createFcnSort(args,cmd.resultSort());
			SymbolTable.Entry entry = new SymbolTable.Entry(cmd.symbol(),fcnSort,null);
			entry.definition = cmd.expression();
			if (symTable.add(entry, isGlobal(), false)) {
				checkSatStatus = null;
				return smtConfig.responseFactory.success();
			} else {
				return smtConfig.responseFactory.error("Symbol " + encodedName + " is already defined",cmd.symbol().pos());
			}
		} else {
			return list.get(0); // FIXME - return all?
		}
	}

	@Override
	public IResponse define_fun_rec(Idefine_fun_rec cmd) {
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a define-fun-rec command is issued");
		}
		List<IResponse> list = TypeChecker.checkFcnRec(symTable, isGlobal(), cmd.symbol(),
				cmd.parameters(), cmd.resultSort(), cmd.expression(),
				cmd instanceof IPosable ? ((IPosable) cmd).pos() : null);
		if (list.isEmpty()) {
			checkSatStatus = null;
			return smtConfig.responseFactory.success();
		} else {
			return list.get(0);
		}
	}

	@Override
	public IResponse define_funs_rec(Idefine_funs_rec cmd) {
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a define-funs-rec command is issued");
		}
		List<IResponse> list = TypeChecker.checkFcnsRec(symTable, isGlobal(),
				cmd.declarations(), cmd.bodies());
		if (list.isEmpty()) {
			checkSatStatus = null;
			return smtConfig.responseFactory.success();
		} else {
			return list.get(0);
		}
	}
    
    @Override 
    public IResponse declare_sort(Ideclare_sort cmd) {
        if (logicSet == null) {
            return smtConfig.responseFactory.error("The logic must be set before a declare-sort command is issued");
        }
        List<IResponse> list = TypeChecker.checkSortAbbreviation(symTable,cmd.sortSymbol(),null,null);
        boolean b = list.isEmpty();
        if (b) {
            INumeral sortArity = cmd.arity();
            b = symTable.addSortDefinition(cmd.sortSymbol(), sortArity, isGlobal());
            if (!b) return smtConfig.responseFactory.error("The identifier is already declared to be a sort: " + 
                    smtConfig.defaultPrinter.toString(cmd.sortSymbol()), cmd.sortSymbol().pos());
            checkSatStatus = null;
            return smtConfig.responseFactory.success();
        } else {
            return list.get(0); // FIXME - return all errors?
        }
    }
    
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
			return list.get(0); // FIXME - return all errors?
		}
	}

    @Override
    public IResponse declare_datatype(Ideclare_datatype cmd) {
        if (logicSet == null) {
            return smtConfig.responseFactory.error("The logic must be set before a declare-datatype command is issued");
        }
        ISymbol sortName = cmd.sortDeclaration().symbol();
        INumeral arity = cmd.sortDeclaration().arity();
        ISort.IDatatype dt = cmd.datatype();
        List<IResponse> nameErrors = TypeChecker.validateDatatypeNames(symTable, smtConfig,
            Collections.singletonList(cmd.sortDeclaration()),
            Collections.singletonList(dt));
        if (!nameErrors.isEmpty()) return nameErrors.get(0);
        if (!symTable.addSortDefinition(sortName, arity, isGlobal())) {
            return smtConfig.responseFactory.error("The sort is already declared: " + smtConfig.defaultPrinter.toString(sortName), sortName.pos());
        }
        IResponse err = registerDatatypeConstructors(sortName, dt);
        if (err != null) return err;
        checkSatStatus = null;
        return smtConfig.responseFactory.success();
    }

    @Override
    public IResponse declare_datatypes(Ideclare_datatypes cmd) {
        if (logicSet == null) {
            return smtConfig.responseFactory.error("The logic must be set before a declare-datatypes command is issued");
        }
        List<ISortDeclaration> sortDecls = cmd.sortDeclarations();
        List<ISort.IDatatype> datatypes = cmd.datatypes();
        List<IResponse> nameErrors = TypeChecker.validateDatatypeNames(symTable, smtConfig, sortDecls, datatypes);
        if (!nameErrors.isEmpty()) return nameErrors.get(0);
        // Register all sort names first so constructors can cross-reference them
        for (ISortDeclaration sd : sortDecls) {
            if (!symTable.addSortDefinition(sd.symbol(), sd.arity(), isGlobal())) {
                return smtConfig.responseFactory.error("The sort is already declared: " + smtConfig.defaultPrinter.toString(sd.symbol()), sd.symbol().pos());
            }
        }
        for (int i = 0; i < sortDecls.size(); i++) {
            IResponse err = registerDatatypeConstructors(sortDecls.get(i).symbol(), datatypes.get(i));
            if (err != null) return err;
        }
        checkSatStatus = null;
        return smtConfig.responseFactory.success();
    }

    /** Registers constructors and selectors for one datatype into the symbol table. */
    private IResponse registerDatatypeConstructors(ISymbol sortName, ISort.IDatatype dt) {
        ISort declaredSort = smtConfig.sortFactory.createSortExpression(sortName, new ISort[0]);
        List<ISymbol> ctorList = new java.util.ArrayList<>();
        for (IConstructor ctor : dt.constructors()) {
            List<ISort> argSorts = new java.util.LinkedList<>();
            for (ISelector sel : ctor.selectors()) argSorts.add(sel.sort());
            List<IResponse> errs = TypeChecker.checkFcn(symTable, ctor.symbol(), argSorts, declaredSort, ctor.symbol().pos());
            if (!errs.isEmpty()) return errs.get(0);
            ISort.IFcnSort ctorSort = smtConfig.sortFactory.createFcnSort(argSorts.toArray(new ISort[0]), declaredSort);
            symTable.add(new SymbolTable.Entry(ctor.symbol(), ctorSort, null), isGlobal(), false);
            ctorList.add(ctor.symbol());
            for (ISelector sel : ctor.selectors()) {
                ISort[] selArgs = new ISort[]{ declaredSort };
                List<IResponse> selErrs = TypeChecker.checkFcn(symTable, sel.symbol(), Arrays.asList(selArgs), sel.sort(), sel.symbol().pos());
                if (!selErrs.isEmpty()) return selErrs.get(0);
                ISort.IFcnSort selSort = smtConfig.sortFactory.createFcnSort(selArgs, sel.sort());
                symTable.add(new SymbolTable.Entry(sel.symbol(), selSort, null), isGlobal(), false);
            }
        }
        symTable.datatypeConstructors.put(sortName.value(), ctorList);
        return null;
    }
	
}
