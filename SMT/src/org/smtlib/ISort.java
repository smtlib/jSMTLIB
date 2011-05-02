/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

import java.util.List;
import java.util.Map;

import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IPos.IPosable;
import org.smtlib.IVisitor.VisitorException;

/** The interface for an SMT-LIB concept of a Sort */
public interface ISort extends IAccept, IPosable {
	
	/** Returns true if the object and receiver represent the same Sort */
	boolean equals(Object o);

	/** Returns true if the object and receiver represent the same Sort, under the given sort parameter substitutions */
	boolean equals(Map<IIdentifier,ISort> leftmap, ISort s, Map<IIdentifier,ISort> rightmap, SymbolTable symTable);

	/** Returns true if the receiver designates the Bool pre-defined Sort. */
	boolean isBool();
	
	/** Returns a new sort with any parameters substituted */
	ISort substitute(java.util.Map<IIdentifier,ISort> map);

	/** A super-interface for definitions of new sort ids; there are two
	 * kinds of such definitions: new Sort families and new Sort abbreviations.
	 */
	static public interface IDefinition extends IAccept {
		/** The identifier for the sort symbol */
		IIdentifier identifier();
		
		/** A new sort expression that results from applying the sort symbol to a list of sorts */
		//@ requires sorts.size() == intArity();
		ISort eval(List<ISort> sorts);
		
		/** The arity of the symbol*/
		//@ ensures \result >= 0;
		int intArity();
	}
	
	// FIXME - do we really want this - is it properly abstract?
	static public class ErrorDefinition implements IDefinition {
		public IIdentifier id;
		public String error;
		public IPos pos;
		
		public ErrorDefinition(IIdentifier id, String error, IPos pos) {
			this.id = id;
			this.error = error;
			this.pos = pos;
		}
		
		@Override
		public <T> T accept(IVisitor<T> v) throws VisitorException {
			return null;
		}

		@Override
		public IIdentifier identifier() {
			return id;
		}

		@Override
		public ISort eval(List<ISort> sorts) {
			return null;
		}

		@Override
		public int intArity() {
			return 0;
		}
		
	}
	
	/** This interface represents a new Sort symbol designating either
	 * a new Sort (if the arity is 0) or a new parameterized Sort family
	 * (if the arity is greater than 0); each new symbol has a (new) name
	 * and a non-negative arity.
	 */
	static public interface IFamily extends IDefinition {
		/** The unique identifier for this sort symbol */
		IIdentifier identifier();
		
		/** The arity of the sort symbol */
		//@ ensures \result.intValue() >= 0;
		INumeral arity();
	}
	
	/** This interface represents a new Sort symbol designating an
	 * abbreviation for a (possibly parameterized) sort expression.
	 */
	static public interface IAbbreviation extends IDefinition {
		IIdentifier identifier();
		List<IParameter> parameters();
		ISort sortExpression();
	}
	
	/** The interface for a Sort expression that consists either of
	 * an arity 0 sort symbol or a positive-arity symbol with the 
	 * appropriate number of arguments.
	 */
	static public interface IExpression extends ISort {
		IIdentifier family();
		//@ requires i >= 0 && i < parameters().size();
		ISort param(int i);
		List<ISort> parameters();
		IDefinition definition();
		IDefinition definition(IDefinition definition);
		boolean equals(/*@Nullable*/Object o);
		boolean equals(Map<IIdentifier,ISort> leftmap, ISort s, Map<IIdentifier,ISort> rightmap, SymbolTable symTable);

	}

	/** The interface for a sort parameter, as used in sort abbreviations
	 * (including in the defining expression).
	 */
	static public interface IParameter extends ISort, IDefinition {
		ISymbol symbol();
		boolean equals(/*@Nullable*/Object o);
		boolean equals(Map<IIdentifier,ISort> leftmap, ISort s, Map<IIdentifier,ISort> rightmap, SymbolTable symTable);
	}
	
	/** An interface to represent the Sort of a function; this is
	 * not something that can be written as a sort expression in SMT-LIB,
	 * but it is convenient to be able to represent the sorts of function
	 * ids uniformly with the sorts of other ids.  // FIXME - perhaps we can get around this - IFcnSort
	 */
	static public interface IFcnSort extends ISort {
		ISort resultSort();
		ISort[] argSorts();
	}
	
	/** The interface for a Sort-creating factory */
	static public interface IFactory {
		
		IFamily createSortFamily(IIdentifier identifier, INumeral arity);
		IParameter createSortParameter(ISymbol symbol);
		IExpression createSortExpression(IIdentifier sortFamily, ISort... exprs);
		IExpression createSortExpression(IIdentifier sortFamily, List<ISort> exprs);
		IAbbreviation createSortAbbreviation(IIdentifier identifier, List<IParameter> params, ISort sortExpr);
		IFcnSort createFcnSort(ISort[] args, ISort result);
		
		/** Returns the Bool Sort */
		IExpression Bool();
	}
}
