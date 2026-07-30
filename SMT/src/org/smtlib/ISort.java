/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

import java.util.List;
import java.util.Map;

import org.smtlib.IExpr.IConstructor;
import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IPos.IPosable;
import org.smtlib.IVisitor.VisitorException;

/** The interface for an SMT-LIB concept of a Sort. Two kinds of things are modeled here.
 * <P>
 * First, a definition of a Sort, modeled by ISort.IDefinition. There are these kinds of 
 * definitions:
 * <UL>
 * <LI> an ISort.IFamily, which defines a new sort symbol of a given arity
 * <LI> an ISort.IAbbreviation, which defines a (possibly parameterized) abbreviation for a sort expression.
 * <LI> an ISort.IParameter, which defines a sort name used as a parameter in an abbreviation definition
 * <LI> The ISort.ErrorDefinition class, which is used as a definition place holder for ill-formed definitions, to avoid excessive redundant errors
 * </UL>
 * Second, Sort expressions themselves, modeled by ISort:
 * <UL>
 * <LI>A ISort.IApplication, which is the application of an IDefinition to the appropriate number
 * (possibly 0) of Sort expressions
 * <LI>A ISort.IParameter, which is a simple symbol designating the parameter of a parameterized abbreviation
 * <LI>A ISort.IFcnSort, an expression designating a function sort; this is not expressible in SMT-LIBv2, but is 
 * useful internally within jSMTLIB.
 * </UL>
 */
public interface ISort extends INode, IPosable {

	/** Structural equality after expansion of abbreviations, but without any substitution of free parameters. */
	//@ pure
	@Override
	boolean equals(Object o);

	/** Structural equality after expansion of abbreviations (as looked up in the symbol table)
	 * and substitution of free parameters according to the respective maps. 
	 */
	//@ pure
	boolean equals(Map<IParameter,ISort> leftmap, ISort s, Map<IParameter,ISort> rightmap, SymbolTable symTable);

	/** Returns true if the receiver designates the Bool pre-defined Sort. */
	//@ pure
	boolean isBool();
	
	/** Expands all abbreviations */
	//@ pure
	ISort expand();
	
	/** Returns a new sort with any parameters substituted */
	//@ pure
	ISort substitute(java.util.Map<IParameter,ISort> map);

	/** Compares sort expressions without abbreviation expansion or parameter substitution */
	//@ pure
	boolean equalsNoExpand(ISort sort);
	
	/** A super-interface for definitions of new sort ids.
	 */
	static public interface IDefinition extends INode {
		/** The identifier for the sort symbol */
		//@ pure
		IIdentifier identifier();
		
		/** A new sort expression that results from applying the sort symbol to a list of sort expressions */
		//@ requires sorts.size() == intArity();
		//@ pure
		ISort eval(List<ISort> sorts);
		
		/** The arity of the symbol*/
		//@ ensures \result >= 0;
		//@ pure
		int intArity();
	}
	
	/** Represents an erroneous sort definition; by having an actual IDefinition,
	 * redundant cascading errors are suppressed.
	 */
	static public interface IErrorDefinition extends IDefinition {
		/** The error message describing why the definition is ill-formed */
		String errorMessage();
		/** The source position of the error */
		IPos errorPos();
	}
	
	/** This interface represents a new Sort symbol designating either
	 * a new Sort (if the arity is 0) or a new parameterized Sort family
	 * (if the arity is greater than 0); each new symbol has a (new) name
	 * and a non-negative arity.
	 */
	static public interface IFamily extends IDefinition {
		/** The unique identifier for this sort symbol */
		@Override
		IIdentifier identifier();
		
		/** The arity of the sort symbol */
		//@ ensures \result.intValue() >= 0;
		INumeral arity();
	}
	
	/** This interface represents a new Sort symbol designating an
	 * abbreviation for a (possibly parameterized) sort expression.
	 */
	static public interface IAbbreviation extends IDefinition {
		/** The identifier of the abbreviation */
		@Override
		IIdentifier identifier();

		/** The list of parameters of the abbreviation (possibly empty, but not null) */
		List<IParameter> parameters();

		/** The sort expression that the abbreviation represents, presumably using the given parameters */
		ISort sortExpression();
	}
	
	/** The interface for a Sort expression that consists of either
	 * an arity 0 sort symbol or a positive-arity symbol with the 
	 * appropriate number of arguments.
	 */
	static public interface IApplication extends ISort {
		/** The head identifier of the sort expression */
		IIdentifier family();
		
		/** Returns the ith parameter */
		//@ requires i >= 0 && i < parameters().size();
		ISort param(int i);
		
		/** Returns the list of parameters */
		List<ISort> parameters();
		
		/** The definition of the family identifier, valid after the sort expression has been type-checked. */
		IDefinition definition();

		/** Sets and returns the value of definition() for this object to the value that is the argument */
		//@ ensures \result == definition;
		IDefinition definition(IDefinition definition);
		
		/** Expands any head abbreviations, if any; requires definition() to be defined */
		@Override
		ISort expand();

		@Override
		boolean equals(/*@Nullable*/Object o);
		
		@Override
		boolean equals(Map<IParameter,ISort> leftmap, ISort s, Map<IParameter,ISort> rightmap, SymbolTable symTable);

		@Override
		boolean equalsNoExpand(ISort sort);

	}

	/** The interface for a sort parameter, as used in sort abbreviations
	 * (including in the defining expression).
	 */
	static public interface IParameter extends ISort, IDefinition {
		/** The symbol that names the parameter */
		ISymbol symbol();
		
		@Override
		boolean equals(/*@Nullable*/Object o);
		
		@Override
		boolean equals(Map<IParameter,ISort> leftmap, ISort s, Map<IParameter,ISort> rightmap, SymbolTable symTable);
		
		@Override
		boolean equalsNoExpand(ISort sort);

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
	
	/** The interface for a datatype declaration (used in declare-datatype and declare-datatypes). */
	static public interface IDatatype extends INode, IPosable {
		List<IConstructor> constructors();
		/*@ nullable */ List<ISymbol> symbols();
		//@ pure
		@Override
		String toString();
	}

	/** The interface for a Sort-creating factory. */
	static public interface IFactory {
		/** Creates a sort family with the given identifier and arity. */
		IFamily createSortFamily(IIdentifier identifier, INumeral arity);

		/** Creates a parameter for a parameterized sort abbreviation. */
		IParameter createSortParameter(ISymbol symbol);

		/** Creates a sort expression, applying a family to a list of sort arguments;
		 * the arity of the identifier in the applicable symbol table must match the number of sort arguments.
		 */
		IApplication createSortExpression(IIdentifier sortFamily, ISort... exprs);

		/** Creates a sort expression, applying a family to a list of sort arguments;
		 * the arity of the identifier in the applicable symbol table must match the number of sort arguments.
		 */
		IApplication createSortExpression(IIdentifier sortFamily, List<ISort> exprs);

		/** Creates a new sort abbreviation. */
		IAbbreviation createSortAbbreviation(IIdentifier identifier, List<IParameter> params, ISort sortExpr);

		/** Creates a function sort. */
		IFcnSort createFcnSort(ISort[] args, ISort result);

		/** Creates an error-placeholder definition (suppresses cascading errors). */
		IErrorDefinition createErrorDefinition(IIdentifier id, String errorMessage, IPos pos);

		/** Returns the Bool sort. */
		IApplication Bool();
	}
}
