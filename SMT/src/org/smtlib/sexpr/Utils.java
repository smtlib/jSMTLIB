package org.smtlib.sexpr;

import java.io.StringWriter;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.smtlib.IExpr.IDecimal;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.command.*;
import org.smtlib.impl.Pos;
import org.smtlib.*;

//FIXME - review asSort, find/load logic/theory, checkOptionType
// FIXME - document

/** Holds constants and utility methods pertinent to the S-expression concrete
 * implementation of the SMT-LIB syntax.
 */
public class Utils extends org.smtlib.Utils {
	
	/** Concrete syntax for the match token */
	public static final String MATCH = "match";
	/** Concrete syntax for the special NUMERAL token */
	public static final String NUMERAL = "NUMERAL";
	/** Concrete syntax for the special DECIMAL token */
	public static final String DECIMAL = "DECIMAL";
	/** Concrete syntax for the special STRING token */
	public static final String STRING = "STRING";
	/** Concrete syntax for the token that starts a parameterized identifier*/
	public static final String UNDERSCORE = "_";
	/** Concrete syntax for the token that starts a named expression */
	public static final String NAMED_EXPR = "!";


	/** A list of reserved words that are not commands */
	static public Set<String> reservedWordsNotCommands = new HashSet<String>();
	/** A list of all reserved words */
	static public Set<String> reservedWords = new HashSet<String>();
	static {
		reservedWordsNotCommands.add(NAMED_EXPR);
		reservedWordsNotCommands.add(UNDERSCORE);
		reservedWordsNotCommands.add(AS);
		reservedWordsNotCommands.add(DECIMAL);
		reservedWordsNotCommands.add(EXISTS);
		reservedWordsNotCommands.add(FORALL);
		reservedWordsNotCommands.add(LET);
		reservedWordsNotCommands.add(MATCH);
		reservedWordsNotCommands.add(NUMERAL);
		reservedWordsNotCommands.add(PAR);
		reservedWordsNotCommands.add(STRING);
		reservedWords.addAll(reservedWordsNotCommands);
		reservedWords.add(C_assert.commandName);
		reservedWords.add(C_check_sat.commandName);
		reservedWords.add(C_declare_fun.commandName);
		reservedWords.add(C_declare_sort.commandName);
		reservedWords.add(C_define_fun.commandName);
		reservedWords.add(C_define_sort.commandName);
		reservedWords.add(C_exit.commandName);
		reservedWords.add(C_get_assertions.commandName);
		reservedWords.add(C_get_assignment.commandName);
		reservedWords.add(C_get_info.commandName);
		reservedWords.add(C_get_option.commandName);
		reservedWords.add(C_get_proof.commandName);
		reservedWords.add(C_get_unsat_core.commandName);
		reservedWords.add(C_get_value.commandName);
		reservedWords.add(C_pop.commandName);
		reservedWords.add(C_push.commandName);
		reservedWords.add(C_set_info.commandName);
		reservedWords.add(C_set_logic.commandName);
		reservedWords.add(C_set_option.commandName);
	}
	
	private <T extends IPos.IPosable>T setPos(T p, IPos pos) { p.setPos(pos); return p; } 

	/** Creates a Utils instance for the given configuration */
	public Utils(SMT.Configuration smtConfig) {
		super(smtConfig);
	}
	
	/** Initializes the default printer and the smtConfig.smtFactory */
	public void initFactories(SMT.Configuration smtConfig) {
		smtConfig.smtFactory = new Factory();
		smtConfig.defaultPrinter = new Printer(new StringWriter());
	}
	
	/** This version of loadLogic loads a logic as defined in the logicExpr expression, if it is a valid definition
	 * of a logic.
	 * @param logicExpr the ILogic object to check and load
	 * @param symTable the symbol table into which to load the ids defined by the logic
	 * @return null (if all is well) or error responses
	 */
	public /*@Nullable*/IResponse loadLogic(ILogic logicExpr, SymbolTable symTable) {
		String logicName = logicExpr.logicName().value(); // FIXME = canonical value or some representation?
		
		// The smtlib-version attribute should be present and have the correct value
		IAttributeValue version = logicExpr.value(SMTLIB_VERSION);
		if (version == null) return smtConfig.responseFactory.error("Logic definition for " + logicName + " is missing the " + SMTLIB_VERSION + " attribute");
		if (!(version instanceof IDecimal)) return smtConfig.responseFactory.error("The value of " + SMTLIB_VERSION + " must be expressed as a decimal");
		if (version.toString().compareTo(SMTLIB_VERSION_CURRENT) > 0) return smtConfig.responseFactory.error("Only implemented version " + SMTLIB_VERSION_CURRENT + " of smtConfig-lib, not " + version);
		
		// Get the list of theories for this logic
		IAttributeValue o = logicExpr.value(THEORIES);
		if (!(o instanceof ISexpr.ISeq)) {
			return smtConfig.responseFactory.error("Expected a list of theories for the value of the " + THEORIES + " attribute");
		}
		/*@Mutable*/ IResponse res = null;
		try {
			symTable.push();
			res = loadTheory(CORE,symTable);
			if (res != null) return res;
			ISexpr.ISeq theories = (ISexpr.ISeq)o;
			for (ISexpr theory: theories.sexprs()) { // FIXME - what about parameterized theories
				if (!(theory instanceof IExpr.ISymbol)) return smtConfig.responseFactory.error("Expected a simple symbol to designate a theory");
				// TODO - do we want to use the canonical value of the theory name or some representation?
				ISymbol theoryName = (IExpr.ISymbol)theory;
				if (CORE.equals(theoryName.value())) continue;
				if ("ALL".equals(logicName)) {
					// For ALL: parse the theory to check its version; skip theories that
					// require a newer SMT-LIB version than the one configured.
					boolean savedRelax = smtConfig.relax;
					String savedSmtlib = smtConfig.smtlib;
					smtConfig.relax = true; // suppress version-mismatch exception in findTheory
					smtConfig.smtlib = null; // use latest lexer rules to read the theory file
					ITheory th;
					try {
						th = findTheory(theoryName.value(), smtConfig.logicPath);
					} catch (SMTLIBException e) {
						res = e.errorResponse;
						return res;
					} finally {
						smtConfig.relax = savedRelax;
						smtConfig.smtlib = savedSmtlib;
					}
					IAttributeValue tv = th.value(SMTLIB_VERSION);
					if (tv instanceof IDecimal) {
						SMT.Configuration.SMTLIB ver = SMT.Configuration.SMTLIB.find("V" + tv.toString());
						if (ver != null && !smtConfig.atLeastVersion(ver)) continue;
					}
					res = loadTheory(th, symTable);
					if (res == null) {
						String tname = th.theoryName().value();
						if (tname.equals("ArraysEx")) symTable.arrayTheorySet = true;
						if (tname.equals("Fixed_Size_BitVectors") || tname.equals("FixedSizeBitVectors")) symTable.bitVectorTheorySet = true;
						if (tname.equals("Reals_Ints")) symTable.realsIntsTheorySet = true;
						if (tname.equals("HO-Core")) symTable.hoTheorySet = true;
					}
				} else {
					res = loadTheory(theoryName.value(), symTable);
				}
				if (res != null) return res;
			}
		} finally {
			if (res != null) symTable.pop(); // error occurred - reset symbol table
			else symTable.moveToBackground(); // else save ids to background
		}
		return res;
	}
	
	/** This version of loadTheory loads a theory into the symbol table,
	 * as defined in the theory expression, if it is a valid definition
	 * of a logic.
	 * @param theory the theory object to load
	 * @param symTable the symbol table into which to load the ids defined by the theory
	 * @return null (if all is well) or an error response
	 */
	public /*@Nullable*/IResponse loadTheory(ITheory theory, SymbolTable symTable) {
		String theoryName = theory.theoryName().value();
		
		// Check the version
		// The smtlib-version attribute should be present and have the correct value
		IAttributeValue version = theory.value(SMTLIB_VERSION);
		if (version == null) return smtConfig.responseFactory.error("Theory definition for " + theoryName + " is missing the " + SMTLIB_VERSION + " attribute");
		if (!(version instanceof IDecimal)) return smtConfig.responseFactory.error("The value of " + SMTLIB_VERSION + " must be expressed as a decimal");
		if (version.toString().compareTo(SMTLIB_VERSION_CURRENT) > 0) return smtConfig.responseFactory.error("Only implemented version " + SMTLIB_VERSION_CURRENT + " of smtConfig-lib, not " + version);

		// Find and install any Sorts the theory defines (handles multiple :sorts attributes)
		for (IAttributeValue sortsVal : theory.values(SORTS)) {
			if (!(sortsVal instanceof ISexpr.ISeq)) {
				return smtConfig.responseFactory.error("The list of sorts in theory " + theoryName + " is ill-formed: " + sortsVal);
			}
			Iterator<ISexpr> iter = ((ISexpr.ISeq)sortsVal).sexprs().iterator();
			while (iter.hasNext()) {
				ISexpr.ISeq sx = (ISexpr.ISeq)iter.next(); // FIXME - check casts and number here and on subsequent lines
				IExpr.ISymbol name = ((IExpr.ISymbol)sx.sexprs().get(0));
				INumeral arity = (IExpr.INumeral)sx.sexprs().get(1);
				symTable.addSortDefinition(name,arity);
				if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Added sort " + name);
			}
		}

		// Find and install any functions and constants the theory defines
		// Multiple :funs attributes are all processed
		for (IAttributeValue funsVal : theory.values(FUNS)) {
			IResponse r = loadFuns(funsVal, theoryName, symTable);
			if (r != null) return r;
		}
		if (theoryName.equals("ArraysEx")) {
			ISort.IFcnSort fs = smtConfig.sortFactory.createFcnSort(new ISort[0],null);
			SymbolTable.Entry e = new SymbolTable.Entry(
					smtConfig.exprFactory.symbol("store"),
					fs,null);
			symTable.add(e);
			e = new SymbolTable.Entry(
					smtConfig.exprFactory.symbol("select"),
					fs,null);
			symTable.add(e);
		}
		// FIXME - declare all bitvector functions

		return null; // Successful
	}
	
	/** Interprets an ISexpr as a Sort, returns null if not a Sort
	 * (no error messages are logged).
	 * 
	 * @param sexpr the ISexpr to interpret
	 * @param symtab the symbol table to use for symbol lookup
	 * @return null or the corresponding Sort
	 */
	/** Loads a single :funs or :fun attribute value into the symbol table. Returns an error response or null on success. */
	private /*@Nullable*/IResponse loadFuns(IAttributeValue funsVal, String theoryName, SymbolTable symTable) {
		if (!(funsVal instanceof ISexpr.ISeq)) return smtConfig.responseFactory.error("Expected a sequence of function declarations instead of " + funsVal);
		Iterator<ISexpr> iter = ((ISexpr.ISeq)funsVal).sexprs().iterator();
		while (iter.hasNext()) {
			ISexpr next = iter.next();
			if (!(next instanceof ISexpr.ISeq)) continue; // skip embedded keywords/strings (e.g. :notes)
			ISexpr.ISeq sx = (ISexpr.ISeq)next;
			ISexpr first = sx.sexprs().get(0);
			if (!(first instanceof IExpr.ISymbol)) continue; // skip indexed identifiers like (_ re.^ n) — not yet supported
			IExpr.ISymbol sym = (IExpr.ISymbol)first;
			String name = sym.value();
			if (name.equals(PAR)) continue; // FIXME - not handling parameterized as yet
			Iterator<ISexpr> iter2 = sx.sexprs().iterator();
			iter2.next();
			List<ISort> sorts = new LinkedList<ISort>();
			ISexpr key = null;
			while (iter2.hasNext()) {
				key = iter2.next();
				if (key instanceof IExpr.IKeyword) break; // end of sorts, start of attributes
				ISort ss = asSort(key, symTable);
				if (ss == null) {
					return smtConfig.responseFactory.error("Unknown sort given: " + key);
				}
				sorts.add(ss);
				key = null;
			}
			ISort result = sorts.remove(sorts.size()-1); // The result sort is the last one
			List<IExpr.IAttribute<?>> attrs = new LinkedList<IExpr.IAttribute<?>>();
			if (key != null) while (true) {
				if (iter2.hasNext()) {
					ISexpr key2 = iter2.next();
					if (key2 instanceof IExpr.IKeyword) {
						attrs.add(setPos(smtConfig.exprFactory.attribute((IExpr.IKeyword)key,null),key.pos()));
						key = key2;
					} else {
						attrs.add(setPos(smtConfig.exprFactory.attribute((IExpr.IKeyword)key,key2),
									new Pos(key.pos().charStart(),key2.pos().charEnd(),key.pos().source()))); // FIXME - factory?
						if (!iter2.hasNext()) break;
						key = iter2.next();
					}
				} else {
					attrs.add(setPos(smtConfig.exprFactory.attribute((IExpr.IKeyword)key,null),key.pos()));
					break;
				}
			}
			ISort.IFcnSort fcnSort = smtConfig.sortFactory.createFcnSort(sorts.toArray(new ISort[sorts.size()]),result);

			boolean b = symTable.add(new SymbolTable.Entry(sym,fcnSort,attrs),true);
			if (!b) return smtConfig.responseFactory.error("Failed to add to symbol table: " + smtConfig.defaultPrinter.toString(sym) + " " + smtConfig.defaultPrinter.toString(fcnSort));
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Added symbol " + name);
		}
		return null;
	}

	public /*@Nullable*/ISort asSort(ISexpr sexpr, SymbolTable symtab) {
		if (sexpr instanceof IExpr.ISymbol) {
			IExpr.ISymbol sym = (IExpr.ISymbol)sexpr; 
			ISort.IDefinition def = symtab.lookupSort(sym);
			if (def == null || def.intArity() != 0) {
				return null;
			}
			ISort.IApplication sort = smtConfig.sortFactory.createSortExpression(def.identifier());
			sort.definition(def);
			return sort;
//		} else if (sexpr instanceof ISexpr.ISeq) {  // FIXME - do we need to expand this ???
//			List<ISexpr> sexprs = ((ISexpr.ISeq)sexpr).sexprs();
		}
		return null;
	}
	

	
}