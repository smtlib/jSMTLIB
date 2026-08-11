/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.impl;

import java.util.*;

import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.INumeral;
import org.smtlib.*;
import org.smtlib.impl.SMTExpr.Numeral;
import org.smtlib.impl.SMTExpr.Symbol;

/** This class implements the abstract ISort interface */
public abstract class Sort extends Pos.Printable implements ISort {
	
	/** Returns true iff the receiver is a Sort expression designating the pre-defined Bool sort */
	@Override
	public boolean isBool() {
		return this == Bool || ((this instanceof IApplication) && Bool.family().equals(((IApplication)this).family()));
	}

	/** Returns the pre-defined Bool sort */
	static public ISort.IApplication Bool() {
		return Bool;
	}
	
	/** Concrete syntax for the pre-defined Bool sort */
	static final private String BOOL = "Bool";
	
	/** A cached instance of the pre-defined Bool sort */
	static final private Sort.Application Bool = new Sort.Application(new Symbol(BOOL), new LinkedList<ISort>());
	static {
		// Application.equals()/expand() require definition() to be set (as symTable-driven
		// sort resolution normally does via Family.eval()); without this, comparing this
		// singleton against a distinct (non-identical) Bool instance NPEs inside expand().
		Bool.definition(new Sort.Family(new Symbol(BOOL), new Numeral(0)));
	}

	/** Represents a new sort symbol, with a given identifier and arity */
	static public class Family extends Pos.Printable implements IFamily {
		protected IIdentifier identifier;
		protected INumeral arity;
		/** Creates a sort family with the given identifier and arity. */
		public Family(IIdentifier identifier, INumeral arity) {
			this.identifier = identifier;
			this.arity = arity;
		}
		@Override
		public IIdentifier identifier() { return identifier; }
		
		@Override
		public INumeral arity() { return arity; }

		@Override
		public int intArity() { return arity().intValue(); }

		@Override
		public IApplication eval(List<ISort> sorts) {
			if (sorts.size() != arity().intValue()) {
				throw new SMT.InternalException("Incorrect number of arguments: " + sorts.size() + "vs. " +  arity().intValue());
			}
			Application e = new Application(this.identifier(),sorts);
			e.definition(this);
			return e;
		}

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (!(o instanceof IFamily)) return false;
			return identifier().equals(((IFamily)o).identifier());  // FIXME - is this sufficient in the presence of overriding symbols?
		}

		@Override
		public int hashCode() {
			return identifier.hashCode();
		}
		
		@Override
		public </*@Nullable*/T> /*@Nullable*/T accept(IVisitor</*@Nullable*/T> v) throws IVisitor.VisitorException {
			return v.visit(this);
		}
	}

	/** Implements a Sort abbreviation (parameterized definition, possibly with no parameters) */
	static public class Abbreviation extends Pos.Printable implements IAbbreviation {

		protected IIdentifier identifier;
		protected List<IParameter> parameters;
		protected ISort sortExpression;

		/** Creates a sort abbreviation with the given identifier, parameter list, and defining expression. */
		public Abbreviation(IIdentifier identifier, List<IParameter> parameters, ISort sortExpression) {
			this.identifier = identifier;
			this.parameters = parameters;
			this.sortExpression = sortExpression;
		}
		
		@Override
		public IIdentifier identifier() { return identifier; }
		
		@Override
		public List<IParameter> parameters() { return parameters; }
		
		@Override
		public ISort sortExpression() { return sortExpression; }

		@Override
		public int intArity() { return parameters().size(); }
		
		@Override
		public ISort eval(List<ISort> sorts) {
			if (sorts.size() != parameters().size()) {
				throw new SMT.InternalException("Incorrect number of arguments: " + sorts.size() + " instead of " + parameters().size());
			}
			Map<IParameter,ISort> map = new HashMap<IParameter,ISort>();
			int i = 0;
			for (IParameter p: parameters) {
				if (map.put(p,sorts.get(i))!=null) {
					throw new SMT.InternalException("Duplicate parameter: " + p);
				}
				i++;
			}
			return sortExpression.substitute(map);
		}
		
		// FIXME - equals and hasCode should consider parameters and sort expression

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (!(o instanceof IAbbreviation)) return false;
			return identifier().equals(((IAbbreviation)o).identifier());
		}
		
		@Override
		public int hashCode() {
			// The identifier is supposed to be unique across all in-scope definitions
			return identifier().hashCode(); 
		}
		
		@Override
		public </*@Nullable*/T> /*@Nullable*/T accept(IVisitor</*@Nullable*/T> v) throws IVisitor.VisitorException {
			return v.visit(this);
		}
	}

	/** Represents a sort expression consisting of a sort symbol or sort abbreviation symbol applied to a
	 * corresponding number of sort arguments 
	 */
	static public class Application extends Sort implements IApplication {
		protected IIdentifier sortID;
		protected List<ISort> sortParameters;
		
		/** Reference to definition; filled in during type-checking */
		protected ISort.IDefinition definition;

		/** Cached value for expanded() */
		protected ISort expanded = null;
		
		/** Creates a sort application from a sort identifier and a list of sort arguments. */
		public Application(IIdentifier sortID, List<ISort> sortParameters) {
			this.sortID = sortID;
			this.sortParameters = sortParameters;
		}

		/** Creates a sort application from a sort identifier and a varargs array of sort arguments. */
		public Application(IIdentifier sortID, ISort... sortParameters) {
			this.sortID = sortID;
			this.sortParameters = Arrays.asList(sortParameters);
		}
		
		@Override
		public IIdentifier family() { return sortID; }
		
		@Override
		public ISort param(int i) { return sortParameters.get(i); }
		
		@Override
		public List<ISort> parameters() { return sortParameters; }
		
		@Override
		public IDefinition definition() { return definition; }
		
		@Override
		public IDefinition definition(IDefinition definition) {
			this.definition = definition;
			return definition;
		}
		
		@Override
		public ISort expand() {
			// Note we could call definition().eval(sortParameters) always, but that 
			// creates a duplicate object in Family.eval
			
			if (expanded == null) {
				boolean changed = false;
				ISort ss = this;
				for (ISort param: parameters()) {
					ISort p = param.expand();
					if (p != param) changed = true;
				}
				while (ss instanceof Application) {
					if (((Application)ss).definition() instanceof IFamily) return ss;
					ss = definition().eval(sortParameters);
				}
				expanded = ss;
			}
			return expanded;
		}
		
// TODO _ review all the equals implementations
		@Override
		public boolean equals(Object sort) {
			if (this == sort) return true;
			if (!(sort instanceof ISort)) return false;
			return expand().equalsNoExpand( ((ISort)sort).expand());
//			Object esort = sort;
//			if (sort instanceof IApplication) {
//				IApplication e = (IApplication)sort;
//				if (e.family().equals(this.family())) {
//					boolean matches = true;
//					int i = 0;
//					for (ISort p: this.parameters()) {
//						if (!p.equals(e.param(i++))) { matches = false; break; }
//					}
//					if (matches) return true;
//				}
//				esort = e.expand();
//			}
//			// Substitute abbreviations
//			ISort ethis = expand();
//			// If either one was expanded, call equals recursively
//			if (this != ethis || sort != esort) return ethis.equals(esort);
//			return false;
		}
		
		@Override
		public boolean equalsNoExpand(ISort sort) {
			if (this == sort) return true;
			if (!(sort instanceof IApplication)) return false;
			IApplication esort = (IApplication)sort;
			if (esort.family().equals(this.family())) {
				// If the family() is equal, the arity must be equal
				int i = 0;
				for (ISort p: this.parameters()) {
					if (!p.equalsNoExpand(esort.param(i++))) return false;
				}
				return true;
			} else {
				return false;
			}
		}	
		
		@Override
		public boolean equals(Map<IParameter,ISort> leftmap, ISort sort, Map<IParameter,ISort> rightmap, SymbolTable symTable) {
			//if (this == sort) return true; // Only the case if the maps are the same
			Object esort = sort;
			if (sort instanceof IApplication) {
				IApplication e = (IApplication)sort;
				if (e.family().equals(this.family())) {
					boolean matches = true;
					int i = 0;
					for (ISort p: this.parameters()) {
						if (!p.equals(leftmap,e.param(i++),rightmap,symTable)) { matches = false; break; }
					}
					if (matches) return true;
				}
				esort = e.expand();
			}
			// Substitute abbreviations
			ISort ethis = expand();
			// If either one was expanded, call equals recursively
			if (this != ethis || sort != esort) return ethis.equals(esort);
			return false;
			
			
			
// TODO _ delete when tests are successful			
//			if (this == sort) return true;
//			if (!(sort instanceof IApplication)) return false;
//			IApplication e = (IApplication)sort;
//			if (!(e.family().equals(sortFamily))) {
//				IDefinition leftdef = symTable.lookupSort(sortFamily);
//				if (!(leftdef instanceof IAbbreviation)) return sort.equals(rightmap,this,leftmap,symTable);
//				IAbbreviation leftabbrev = (IAbbreviation)leftdef;
//				if (leftabbrev.intArity() != e.parameters().size()) {
//					return false; // FIXME - actually a problem - mismatched aritities?
//				}
//				Map<IIdentifier,ISort> newmap = new HashMap<IIdentifier,ISort>();
//				newmap.putAll(leftmap);
//				for (int i = 0; i<leftdef.intArity(); ++i) {
//					newmap.put(leftabbrev.parameters().get(i).symbol(),
//							e.parameters().get(i));
//				}
//				return leftabbrev.sortExpression().equals(newmap,sort,rightmap,symTable);
//			}
//			// If the family() is equal, the arity must be equal
//			int i = 0;
//			for (ISort p: sortParameters) {
//				if (!p.equals(e.param(i++))) return false;
//			}
//			return true;
		}

		@Override
		public int hashCode() {
			int hash = sortID.hashCode();
			for (ISort s: sortParameters) {
				hash += s.hashCode();
			}
			return hash;
		}
		
		@Override
		public ISort substitute(Map<IParameter,ISort> map) {
			IIdentifier id = family();
			List<ISort> params = new LinkedList<ISort>();
			for (ISort s: sortParameters) {
				params.add(s.substitute(map));
			}
			ISort s = map.get(id);
			if (s != null) return s;
			Application e = new Application(id,params);
			e.definition(this.definition());
			return e;
		}
		
		@Override
		public </*@Nullable*/T> /*@Nullable*/T accept(IVisitor</*@Nullable*/T> v) throws IVisitor.VisitorException {
			return v.visit(this);
		}
	}

	/** Represents the class of the sort of a function symbol.  This is not a 
	 * sort that can be expressed in SMT-LIB sort grammar, except implicitly 
	 * when function ids are defined in define-fun and declare-fun
	 * commands and in theory definitions.
	 */
	static public class FcnSort extends Sort implements IFcnSort {
		static protected ISort[] noargs = new ISort[0];
		protected ISort resultSort;
		protected ISort[] argSorts;
		
		/** Creates a function sort with the given argument sorts and result sort. */
		public FcnSort(ISort[] argSorts, ISort resultSort) {
			this.argSorts = argSorts;
			this.resultSort = resultSort;
		}

		/** Creates a zero-argument (nullary) function sort with the given result sort. */
		public FcnSort(ISort resultSort) {
			this.argSorts = noargs;
			this.resultSort = resultSort;
		}
		
		@Override
		public ISort expand() { return this; } // TODO: Fix this?
		
		@Override
		public ISort resultSort() { return resultSort; }
		
		@Override
		public ISort[] argSorts() { return argSorts; }
		
		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (!(o instanceof IFcnSort)) return false;
			IFcnSort fs = (IFcnSort)o;
			if (!(fs.resultSort().equals(resultSort))) return false;
			if (fs.argSorts().length != argSorts.length) return false;
			for (int i=0; i<argSorts.length; ++i) {
				if (!(fs.argSorts()[i].equals(argSorts[i]))) return false;
			}
			return true;
		}
		
		@Override
		public boolean equalsNoExpand(ISort sort) {
			if (this == sort) return true;
			if (!(sort instanceof IFcnSort)) return false;
			IFcnSort fs = (IFcnSort)sort;
			if (!(fs.resultSort().equals(resultSort))) return false;
			if (fs.argSorts().length != argSorts.length) return false;
			for (int i=0; i<argSorts.length; ++i) {
				if (!(fs.argSorts()[i].equalsNoExpand(argSorts[i]))) return false;
			}
			return true;
		}


		@Override
		public boolean equals(Map<IParameter,ISort> leftmap, ISort sort, Map<IParameter,ISort> rightmap, SymbolTable symTable) {
			// FcnSorts are not parameterized
			return equals(sort);
		}

		@Override
		public int hashCode() {
			int hash = resultSort.hashCode();
			for (ISort s: argSorts) {
				hash += s.hashCode();
			}
			return hash;
		}
		
		@Override
		public ISort substitute(Map<IParameter, ISort> map) {
			// Actually, do not expect a FcnSort to have any substitutable parameters
			ISort newResult = resultSort.substitute(map);
			ISort[] newArgs = new ISort[argSorts.length];
			for (int i = 0; i<argSorts.length; ++i) {
				newArgs[i] = ((Sort)argSorts[i]).substitute(map);
			}
			return new FcnSort(newArgs,newResult);
		}
		
		@Override
		public </*@Nullable*/T> /*@Nullable*/T accept(IVisitor</*@Nullable*/T> v) throws IVisitor.VisitorException {
			return v.visit(this);
		}
	}

	/** Represents a Sort parameter, such as in either the parameter list or the expression of a Sort abbreviation */
	static public class Parameter extends Sort implements IParameter {
		protected IExpr.ISymbol symbol;

		/** Creates a sort parameter for the given symbol name. */
		public Parameter(IExpr.ISymbol symbol) {
			this.symbol = symbol;
		}
		
		@Override
		public IExpr.ISymbol symbol() { return symbol; }
		
		@Override
		public ISort substitute(Map<IParameter,ISort> map) {
			ISort s = map.get(this);
			return s == null ? this : s;
		}
		
		@Override
		public ISort expand() { return this; } // TODO: Fix this?
		
		@Override
		public boolean equals(Object o) {
			// Parameters are equal only under object equality
			// Two parameters with the same name in different scopes are not equal
			return this == o;
		}
		
		@Override
		public boolean equalsNoExpand(ISort sort) {
			return this == sort;
		}


		@Override
		public boolean equals(Map<IParameter,ISort> leftmap, ISort sort, Map<IParameter,ISort> rightmap, SymbolTable symTable) {
			ISort s = leftmap.get(this);
			if (s != null) {
				return sort.equals(rightmap,s,leftmap,symTable);
			} else if (sort instanceof IParameter) {
				ISort ss = rightmap.get(sort);
				if (ss == null) return this == sort;
				return ss.equals(rightmap,this,leftmap,symTable);
			} else {
				if (s == null) s = this;
				return sort.equals(rightmap,s,leftmap,symTable);
			}
		}
		
		@Override
		public int hashCode() {
			return System.identityHashCode(this);
		}
		
		@Override
		public </*@Nullable*/T> /*@Nullable*/T accept(IVisitor</*@Nullable*/T> v) throws IVisitor.VisitorException {
			return v.visit(this);
		}

		@Override
		public IIdentifier identifier() {
			return symbol;
		}
		
		@Override
		public ISort eval(List<ISort> sorts) {
			// Do nothing to evaluate a parameter that does not have arguments
			if (!sorts.isEmpty()) throw new SMT.InternalException("May not call eval on an IParameter with arguments");
			return this;
		}
		
		@Override
		public int intArity() {
			return 0;
		}
	}

	/** A placeholder sort definition used when a sort declaration is ill-formed, to suppress cascading errors. */
	static public class ErrorDefinition extends Pos.Printable implements ISort.IErrorDefinition {
		protected IIdentifier id;
		protected String error;

		/** Creates an error placeholder for the given identifier, error message, and source position. */
		public ErrorDefinition(IIdentifier id, String error, IPos pos) {
			this.id = id;
			this.error = error;
			setPos(pos);
		}

		@Override public String errorMessage() { return error; }
		@Override public IPos errorPos() { return pos(); }
		@Override public IIdentifier identifier() { return id; }
		@Override public ISort eval(List<ISort> sorts) { return null; }
		@Override public int intArity() { return 0; }

		@Override
		public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
			return null;
		}
	}

}
