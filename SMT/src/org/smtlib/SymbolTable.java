/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;

import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.IParameterizedIdentifier;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.ISort.IFcnSort;
import org.smtlib.ISort.IParameter;

// FIXME - define an interface for symbol table?

/** This class manages a symbol table used for storing definitions and looking up ids in expressions.
 *  The table maps names to Entry objects that hold information about the defined symbol. */
public class SymbolTable {

	/** true if the Array theory has been set */
	// Used only while we have store and select built in
	public boolean arrayTheorySet = false;
	
	/** true if the bit-vector theory has been set */
	// Used only while we have BitVec built in
	public boolean bitVectorTheorySet = false;
	
	/** true if the RealsInts theory is set (which allows implicit promotion of ints to reals) */
	public boolean realsIntsTheorySet = false;

	/** true if the HO-Core theory has been set */
	// Used only while we have @ built in
	public boolean hoTheorySet = false;

	/** true if the FloatingPoint theory has been set */
	// Used only while we have FloatingPoint built in
	public boolean floatingPointTheorySet = false;


	/** Maps each datatype sort name to its constructors (in declaration order); populated by declare-datatype/declare-datatypes */
	public Map<String, List<ISymbol>> datatypeConstructors = new HashMap<>();

	/** The logic that is being used - this value is used to check that
	 * expressions, etc., conform to the language restrictions of the current
	 * logic.
	 */
	public ILogic logicInUse = null;
	
	/** A reference to the Configuration for this instance of SMT. */
	public SMT.Configuration smtConfig;
	
	/* The tops of the stack are at the beginning of the lists.  The table 
	 * manages a stack of scopes, each stack element holds a scope.  
	 * Within a scope, a symbol can be defined with various different arities 
	 * (and multiple mappings for a given arity) and different sort arguments. 
	 */
	
	//@ private invariant sorts = sortStack.get(0);
	/** The stack of Sort declaration scopes */
	private List<Map<IIdentifier,ISort.IDefinition>> sortStack;
	/** The top-most Sort scope */
	private Map<IIdentifier,ISort.IDefinition> sorts;
	
	//@ private invariant names == symStack.get(0);
	/** The stack of Symbol scopes. Entries for a given name are kept in one flat list (not
	 * bucketed by arity): an attributed (:left-assoc etc.) or par-polymorphic entry's
	 * declared arity need not match the arity of an actual call it can still be used for, so
	 * a per-arity index would have to be bypassed for those cases anyway -- see lookup(). */
	private List<Map<IIdentifier,List<Entry>>> symStack;
	/** The top-most Symbol scope */
	private Map<IIdentifier,List<Entry>> names;
	
	/** An object that holds all the information about the defined symbol (or aliased definition). */
	public static class Entry {
		
		/** Constructs a symbol table entry */
		public Entry(IIdentifier name, ISort.IFcnSort sort, /*@Nullable*/ List<IExpr.IAttribute<?>> attrs, /*@Nullable*/ List<ISort.IParameter> parameters) {
			this.name = name;
			this.sort = sort;
			this.attributes = attrs;
			this.parameters = parameters;
			this.definition = null;
		}

		/** The identifier */
		public IIdentifier name;
		/** The Sort of the identifier */ // FIXME _ what about parameter names ?
		public ISort.IFcnSort sort;
		/** Any attributes (null if none), e.g. :left-assoc */
		public /*@Nullable*/ List<IExpr.IAttribute<?>> attributes;
		/** The par-polymorphic parameters declared for this entry (null if this is a plain,
		 * monomorphic fun_symbol_decl rather than a par_fun_symbol_decl); sort's argSorts/
		 * resultSort may reference these as ISort.IParameter placeholders, to be bound
		 * against actual argument sorts by a caller that wants to use this entry. */
		public /*@Nullable*/ List<ISort.IParameter> parameters;
		/** The definition of the symbol, if any */
		public /*@Nullable*/ IExpr definition;
	}
	
	/** An iterator over all of the Symbols in the symbol scope stack from the top-most scope
	 * on down.
	 * @author David R. Cok
	 */
	public static class Iterator implements java.util.Iterator<Entry> {
		private java.util.Iterator<Map<IIdentifier,List<Entry>>> stackIter;
		private /*@Nullable*/ java.util.Iterator<List<Entry>> symIter = null;
		private /*@Nullable*/ java.util.Iterator<Entry> entryIter = null;

		/** Constructs a new iterator, initialized at the beginning */
		public Iterator(SymbolTable sym) {
			stackIter = sym.symStack.iterator();
		}

		/*@AssertNonNullIfTrue({"symIter"})*/
		@Override
		public boolean hasNext() {
			while (entryIter == null || !entryIter.hasNext()) {
				while (symIter == null || !symIter.hasNext()) {
					if (!stackIter.hasNext()) return false;
					symIter = stackIter.next().values().iterator();
				}
				entryIter = symIter.next().iterator();
			}
			return true;
		}
		
		@Override
		public Entry next() {
			if (!hasNext()) throw new NoSuchElementException();
			return entryIter.next();
		}
		
		@Override
		public void remove() {
			throw new UnsupportedOperationException();
		}
	}
	
	/** Constructs an empty symbol table */
	public SymbolTable(SMT.Configuration smtConfig) {
		this.smtConfig = smtConfig;
		clear(false);
	}
	
	/** Makes a copy of the symbol table */
	public SymbolTable(SymbolTable s) {
		clear(false);
		this.smtConfig = s.smtConfig;
		sortStack = new LinkedList<Map<IIdentifier,ISort.IDefinition>>();
		symStack = new LinkedList<Map<IIdentifier,List<Entry>>>();
		sortStack.addAll(s.sortStack);
		symStack.addAll(s.symStack);
		names = symStack.get(0);
		sorts = sortStack.get(0);
		datatypeConstructors = new HashMap<>(s.datatypeConstructors);
	}
	
	/** Returns a fresh iterator over the symbol table's contents */
	public Iterator iterator() {
		return new Iterator(this);
	}
	
	/** Initializes the symbol table with an empty background frame and one empty frame. */
	public void clear(boolean keepBackground) {
		if (keepBackground) {
			while (sortStack.size() > 1) sortStack.remove(0);
			while (symStack.size() > 1) symStack.remove(0);
			// add()/addSortParameter() write through the sorts/names fields, not through
			// symStack/sortStack directly -- without this they'd keep pointing at the
			// frame Map just removed above, silently losing any subsequent declaration.
			sorts = sortStack.get(0);
			names = symStack.get(0);
		} else {
			sortStack = new LinkedList<Map<IIdentifier,ISort.IDefinition>>();
			symStack = new LinkedList<Map<IIdentifier,List<Entry>>>();
			datatypeConstructors = new HashMap<>();
			push(); // an empty background frame
			push(); // an empty primary frame
		}
	}

	/** Adds a new empty frame on the top of the symbol table stack. */
	public void push() {
		sortStack.add(0,sorts=new HashMap<IIdentifier,ISort.IDefinition>());
		symStack.add(0,names=new HashMap<IIdentifier,List<Entry>>());
	}

	/** Combines the top two symbol scopes, removing the current top scope; presumes that there
	 * is no shadowing of symbols; the top sort scope is discarded.
	 */ // TODO - say more about why this is used/needed; also review this
	public void merge() {
		Map<IIdentifier,List<SymbolTable.Entry>> oldnames = names;
		pop();
		// Put everything in oldnames into the current top
		for (List<SymbolTable.Entry> ee: oldnames.values()) {
			for (SymbolTable.Entry entry: ee) {
				// We have already checked that there is no shadowing
				add(entry, false);
			}
		}
	}
	
	/** Removes the top frame from the symbol table stack. 
	 * The symbol table must have at least one non-background scope or an 
	 * InternalException will be thrown.
	 */
	public void pop() {
		// The comparison is <= 1 since there is always also the background scope
		if (symStack.size() <= 1) {
			// We throw an InternalException (that is, a bug), since pop should not be called if
			// there are no scopes to pop.
			throw new SMT.InternalException("Invalid pop - no more symbol table scopes to pop");
		}
		sortStack.remove(0);
		symStack.remove(0);
		sorts = sortStack.get(0);
		names = symStack.get(0);
	}
	
	// FIXME _ why is this needed?
	/** Removes the previous background frame, then removes the top frame and 
	 * inserts it as the bottom (background) frame. */
	public void moveToBackground() {
		sortStack.remove(sortStack.size()-1);
		symStack.remove(symStack.size()-1);
		sortStack.add(sortStack.remove(0));
		symStack.add(symStack.remove(0));
		names = symStack.get(0);
		sorts = sortStack.get(0);
	}
	
	/** Adds the given symbol as a sort to the top scope of the sort table; 
	 * returns false if the given symbol is already in the top scope (and the sort table is unchanged);
	 * returns true if the symbol is not already in the top scope.
	 * @param symbol the symbol to add
	 * @return true if successfully added, false if already present
	 */
	public boolean addSortParameter(ISymbol symbol, boolean global) {
		Map<IIdentifier, ISort.IDefinition> target = global ? sortStack.get(sortStack.size()-1) : sorts;
		ISort.IDefinition previous = target.put(symbol, smtConfig.sortFactory.createSortParameter(symbol));
		if (previous == null) return true;
		target.put(symbol, previous);
		return false;
	}

	/** Adds a new sort declaration to the given frame (global = background, else current).
	 *
	 * @param identifier the identifier of the new Sort definition
	 * @param arity the arity of the new Sort definition
	 * @param global if true, add to the background frame; otherwise add to the current frame
	 * @return true if successfully added, false if there already is a sort (in any scope) with this identifier
	 */
	/** Adds a new sort family definition, with attributes (e.g. :right-assoc; null or empty if
	 * none), to the given frame (global = background, else current).
	 *
	 * @param identifier the identifier of the new Sort definition
	 * @param arity the arity of the new Sort definition
	 * @param attributes any attributes declared on the sort symbol (null or empty if none)
	 * @param global if true, add to the background frame; otherwise add to the current frame
	 * @return true if successfully added, false if there already is a sort (in any scope) with this identifier
	 */
	public boolean addSortDefinition(IIdentifier identifier, INumeral arity, /*@Nullable*/ List<IExpr.IAttribute<?>> attributes, boolean global) {
		ISort.IDefinition s = lookupSort(identifier);
		if (s != null) return false;
		ISort.IDefinition def = smtConfig.sortFactory.createSortFamily(identifier,arity,attributes);
		(global ? sortStack.get(sortStack.size()-1) : sorts).put(identifier, def);
		return true;
	}

	/** Adds a new sort abbreviation definition to the given frame (global = background, else current).
	 *
	 * @param identifier the name of the new Sort definition
	 * @param parameters the names of the parameters of the Sort abbreviation
	 * @param definition the expression of the Sort abbreviation
	 * @param global if true, add to the background frame; otherwise add to the current frame
	 * @return true if successfully added, false if there already is a sort by this name in the target scope
	 */
	public boolean addSortDefinition(IIdentifier identifier, List<IParameter> parameters, ISort definition, boolean global) {
		Map<IIdentifier, ISort.IDefinition> target = global ? sortStack.get(sortStack.size()-1) : sorts;
		if (target.get(identifier) != null) return false;
		target.put(identifier, smtConfig.sortFactory.createSortAbbreviation(identifier,parameters,definition));
		return true;
	}
	
	/** Looks up the Sort definition with the given name
	 * 
	 * @param name the name of the Sort definition to find
	 * @return null if not found
	 */
	/*@Nullable*/
	public ISort.IDefinition lookupSort(IIdentifier name) {
		for (Map<IIdentifier,ISort.IDefinition> set: sortStack) {
			ISort.IDefinition s = set.get(name);
			if (s != null) return s;
		}
		
		// FIXME _ improve so this is not hard coded
		if (name instanceof IParameterizedIdentifier) {
			IParameterizedIdentifier pf = (IParameterizedIdentifier)name;
			if (bitVectorTheorySet && Utils.BITVEC_SYM.equals(pf.headSymbol())) {
				if (pf.indices().size() != 1 || !(pf.indices().get(0) instanceof INumeral)) {
					return smtConfig.sortFactory.createErrorDefinition(name,"A bit-vector sort must have exactly one numeral",
							pf.indices().size() > 1 ? pf.indices().get(1).pos()
									: pf.headSymbol().pos());
				}
				if (((INumeral) pf.indices().get(0)).intValue() == 0) {
					return smtConfig.sortFactory.createErrorDefinition(name,"A bit-vector sort must have a length of at least 1",pf.indices().get(0).pos());
				}
				ISort.IDefinition def = smtConfig.sortFactory.createSortFamily(name,smtConfig.exprFactory.numeral(0),null);
				sorts.put(name, def);
				return def;
			}
			if (floatingPointTheorySet && Utils.FLOATINGPOINT_SYM.equals(pf.headSymbol())) {
				if (pf.indices().size() != 2 || !(pf.indices().get(0) instanceof INumeral) || !(pf.indices().get(1) instanceof INumeral)) {
					return smtConfig.sortFactory.createErrorDefinition(name,"A FloatingPoint sort must have exactly two numerals (eb sb)",
							pf.indices().size() > 0 ? pf.indices().get(pf.indices().size()-1).pos()
									: pf.headSymbol().pos());
				}
				int eb = ((INumeral) pf.indices().get(0)).intValue();
				int sb = ((INumeral) pf.indices().get(1)).intValue();
				if (eb <= 1 || sb <= 1) {
					return smtConfig.sortFactory.createErrorDefinition(name,"A FloatingPoint sort must have exponent and significand sizes greater than 1",
							(eb <= 1 ? pf.indices().get(0) : pf.indices().get(1)).pos());
				}
				ISort.IDefinition def = smtConfig.sortFactory.createSortFamily(name,smtConfig.exprFactory.numeral(0),null);
				sorts.put(name, def);
				return def;
			}
		}

		return null;
	}
	
	/** Lookup the Symbol with the given identifier and arity, returning its Sort.
	 * @param arity the arity of the Symbol
	 * @param name the name of the Symbol
	 * @return null if not found, the Sort of the Symbol if found
	 */
	/*@Nullable*/
	public IFcnSort lookup(int arity, IIdentifier name) {
		for (Map<IIdentifier,List<Entry>> set: symStack) {
			List<Entry> entrylist = set.get(name);
			if (entrylist != null) {
				for (Entry e: entrylist) {
					if (e.sort.argSorts().length == arity) return e.sort;
				}
			}
		}
		return null;
	}

	/** Lookup the Symbol with the given identifier, returning all of its declared entries
	 * (of any arity).
	 * @param name the name of the Symbol
	 * @return null if not found, the corresponding List&lt;Entry&gt; from the
	 * top-most scope in which the identifier is found
	 */
	public /*@Nullable*/ List<Entry> lookup(IIdentifier name) {
		for (Map<IIdentifier,List<Entry>> set: symStack) {
			List<Entry> entrylist = set.get(name);
			if (entrylist != null) return entrylist;
		}
		return null;
	}
	
	/** Lookup a Symbol with the given name and argument Sorts and result Sort.
	 * @param name the name to find
	 * @param argSorts the Sorts of the arguments
	 * @param resultSort the expected result sort (from an `as` qualifier), or null if none given
	 * @return the result Sort of the matching declaration, or null if none matches
	 */
	// The background scope may overload an identifier with definitions of the same or
	// different arity (but different sort). However, in non-background scopes, no
	// overloading is allowed of any arity in any scope.
	//
	// A candidate entry's declared arity is not necessarily the actual call's arity: a
	// :left-assoc/:right-assoc/:chainable/:pairwise entry is always declared at arity 2 but
	// can be called at arity 2..N (SMT-LIB Sec. 3.6.2's n-ary sugar), so entries are not
	// bucketed by arity -- every candidate for `name` is tried, exact-arity first, then (only
	// if nothing matched and the call has more than two arguments) the 2-arg/attributed
	// fallback. A par-polymorphic entry (entry.parameters != null) is tried via unify()
	// instead of plain equality; either way a mismatch on one candidate just moves on to the
	// next -- overloading means a unification/equality failure is not itself an error.
	/*@Nullable*/
	public ISort lookup(IIdentifier name, List<ISort> argSorts, ISort resultSort) {
		int arity = argSorts.size();
		for (Map<IIdentifier,List<Entry>> set: symStack) {
			List<Entry> entrylist = set.get(name);
			if (entrylist == null) continue;
			// We have a name match. First check for an exact match on arity.
			Entry found = null;
			ISort foundResult = null;
			boolean foundMatchButNotOnResult = false;
			for (Entry entry: entrylist) {
				if (entry.sort.argSorts().length != arity) continue;
				ISort candidateResult = matchExact(entry, argSorts);
				if (candidateResult == null) continue;
				// Cases to consider
				//   resultSort != null & just one argument sort match -> error - not supposed to use a qualifier
				//   resultSort != null & multiple argument sort matches -> pick the one that matches on result sort
				//   resultSort == null & and just one argument sort match -> return it
				//   resultSort == null & multiple argument sort matches -> ambiguous
				if (resultSort != null) {
					if (resultSort.equals(candidateResult)) {
						if (found != null) {
							// FIXME - there appear to be two entries that match on all arguments and the result
							return null;
						}
						found = entry;
						foundResult = candidateResult;
					} else {
						foundMatchButNotOnResult = true;
					}
				} else {
					// No result sort specified - there should not be any overloading
					if (found != null) {
						// Found something previously and now have this match - so ambiguous
						// FIXME - no place to give an error message that the result sort is ambiguous
						return null;
					}
					found = entry;
					foundResult = candidateResult;
					// Otherwise have just one match - keep checking the rest of the list
				}
			}
			if (resultSort != null && found != null && !foundMatchButNotOnResult) {
				// FIXME - should report unneeded disambiguation
				return null;
			}
			if (found != null) return foundResult;

			// Check for left-assoc etc.
			if (arity <= 2) return null;
			for (Entry entry: entrylist) {
				if (entry.sort.argSorts().length != 2) continue;
				ISort result = matchAssociative(entry, argSorts);
				if (result != null) return result;
			}
			return null;
		}
		return null;
	}

	/** Tries a single candidate entry, already known to have the actual call's arity, as an
	 * exact match: plain structural equality for a monomorphic entry, unification for a
	 * par-polymorphic one (substituting any discovered parameter bindings into the declared
	 * result sort). Returns the concrete result sort on success, or null on mismatch. */
	private /*@Nullable*/ ISort matchExact(Entry entry, List<ISort> argSorts) {
		ISort[] declaredArgs = entry.sort.argSorts();
		if (entry.parameters == null) {
			for (int i = 0; i < declaredArgs.length; i++) {
				if (!declaredArgs[i].equals(argSorts.get(i))) return null;
			}
			return entry.sort.resultSort();
		}
		Map<ISort.IParameter,ISort> bindings = new HashMap<ISort.IParameter,ISort>();
		for (int i = 0; i < declaredArgs.length; i++) {
			bindings = unify(declaredArgs[i], argSorts.get(i), bindings);
			if (bindings == null) return null;
		}
		return entry.sort.resultSort().substitute(bindings);
	}

	/** Tries a single 2-arg candidate entry, carrying an associativity attribute, against an
	 * actual call with more than two arguments -- the SMT-LIB Sec. 3.6.2 n-ary sugar for
	 * :left-assoc ((f t1 t2 t3) = (f (f t1 t2) t3)), :right-assoc ((f t1 t2 t3) =
	 * (f t1 (f t2 t3))), and :chainable/:pairwise (every argument must independently match
	 * the declared, shared argument sort). A monomorphic entry is matched with plain
	 * equality; a par entry unifies at each fold step, which can rebind its parameters
	 * differently every time -- needed for e.g. HO-Core's @, where each curry step's ->
	 * domain/codomain differ. Returns the concrete result sort on success, or null if this
	 * entry's attribute doesn't apply or the sorts don't match. */
	private /*@Nullable*/ ISort matchAssociative(Entry entry, List<ISort> argSorts) {
		ISort left = entry.sort.argSorts()[0];
		ISort right = entry.sort.argSorts()[1];
		ISort declaredResult = entry.sort.resultSort();
		boolean isPar = entry.parameters != null;
		if (hasAttribute(entry,":left-assoc")) {
			ISort acc = argSorts.get(0);
			for (int i = 1; i < argSorts.size(); i++) {
				ISort next = argSorts.get(i);
				if (isPar) {
					Map<ISort.IParameter,ISort> bindings = unify(left, acc, new HashMap<ISort.IParameter,ISort>());
					if (bindings == null) return null;
					bindings = unify(right, next, bindings);
					if (bindings == null) return null;
					acc = declaredResult.substitute(bindings);
				} else {
					if (!acc.equals(left) || !next.equals(right)) return null;
					acc = declaredResult;
				}
			}
			return acc;
		} else if (hasAttribute(entry,":right-assoc")) {
			ISort acc = argSorts.get(argSorts.size() - 1);
			for (int i = argSorts.size() - 2; i >= 0; i--) {
				ISort next = argSorts.get(i);
				if (isPar) {
					Map<ISort.IParameter,ISort> bindings = unify(left, next, new HashMap<ISort.IParameter,ISort>());
					if (bindings == null) return null;
					bindings = unify(right, acc, bindings);
					if (bindings == null) return null;
					acc = declaredResult.substitute(bindings);
				} else {
					if (!next.equals(left) || !acc.equals(right)) return null;
					acc = declaredResult;
				}
			}
			return acc;
		} else if (hasAttribute(entry,":chainable") || hasAttribute(entry,":pairwise")) {
			if (isPar) {
				Map<ISort.IParameter,ISort> bindings = new HashMap<ISort.IParameter,ISort>();
				for (ISort actual: argSorts) {
					bindings = unify(left, actual, bindings);
					if (bindings == null) return null;
				}
				return declaredResult.substitute(bindings);
			} else {
				for (ISort actual: argSorts) {
					if (!actual.equals(left)) return null;
				}
				return declaredResult;
			}
		}
		return null;
	}

	/** Attempts to unify a (possibly parameter-containing) declared sort against a concrete
	 * actual sort, extending the given bindings with any newly-discovered parameter
	 * bindings. Returns null if the two cannot be unified (a structural mismatch, or a
	 * parameter that would need two different bindings); otherwise the (possibly extended)
	 * bindings -- a new map is returned rather than mutating the argument in place, so
	 * callers must use the return value. */
	private /*@Nullable*/ Map<ISort.IParameter,ISort> unify(ISort declared, ISort actual, Map<ISort.IParameter,ISort> bindings) {
		if (declared instanceof ISort.IParameter) {
			ISort bound = bindings.get(declared);
			if (bound == null) {
				Map<ISort.IParameter,ISort> next = new HashMap<ISort.IParameter,ISort>(bindings);
				next.put((ISort.IParameter) declared, actual);
				return next;
			}
			return bound.equals(actual) ? bindings : null;
		}
		if (declared instanceof ISort.IApplication && actual instanceof ISort.IApplication) {
			ISort.IApplication da = (ISort.IApplication) declared;
			ISort.IApplication aa = (ISort.IApplication) actual;
			if (!da.family().equals(aa.family())) return null;
			List<ISort> dparams = da.parameters();
			List<ISort> aparams = aa.parameters();
			if (dparams.size() != aparams.size()) return null;
			Map<ISort.IParameter,ISort> current = bindings;
			for (int i = 0; i < dparams.size(); i++) {
				current = unify(dparams.get(i), aparams.get(i), current);
				if (current == null) return null;
			}
			return current;
		}
		return declared.equals(actual) ? bindings : null;
	}

	/** Returns true if the entry contains a value for the given attribute name */ // FIXME - lookup by keyword?
	private boolean hasAttribute(Entry entry, String attr) {
		for (IExpr.IAttribute<?> a: entry.attributes) {
			if (a.keyword().value().equals(attr)) return true;
		}
		return false;
	}
	
	/** Adds the given entry to the symbol table.
	 * @param entry the Entry to add
	 */
	public void add(Entry entry, boolean global) {
		Map<IIdentifier,List<Entry>> lnames = names;
		if (global) {
			lnames = symStack.get(symStack.size()-1);
		}
		List<Entry> entrylist = lnames.get(entry.name);
		if (entrylist == null) {
			entrylist = new LinkedList<Entry>();
			lnames.put(entry.name,entrylist);
		}
		entrylist.add(entry);
	}
	
	/** Adds the given entry to the symbol table; if overload is false and the 
	 * identifier in the entry is already in the table,
	 * the method returns false (without changing the symbol table); 
	 * otherwise the entry is added and the
	 * method returns true
	 * 
	 * @param entry the Entry to add
	 */
	public boolean add(Entry entry, boolean global, boolean overload) {
		// Check if the entry is already present in any scope;
		// return false if it is.  Allow overloading if overload is true.
		if (!overload) {
			for (Map<IIdentifier,List<Entry>> set: symStack) {
				if (set.get(entry.name) != null) {
					return false;
				}
			}
		}
		// Symbol is not present or overloading is allowed, so add it
		add(entry, global);
		return true;
	}
}
