/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.impl;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.*;

import org.smtlib.*;
import org.smtlib.IExpr.IConstructor;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IVisitor.VisitorException;

/** This class defines a number of subclasses that implement the SMT-LIB abstract AST;
 * they are used by commands and expressions. */
public abstract class SMTExpr implements IExpr {
	public static SMT.Configuration smtConfig;

	/** Abstract base class for all literal value AST nodes; holds the typed value and provides a shared implementation. */
	static abstract public class Literal<T> extends Pos.AbstractExpr {
		protected T value;

		/** Creates a literal with the given value. */
		public Literal(T value) { this.value = value; }

		public T value() { return value; }

		public boolean isError() { return false; }
	}

	/** This class represents an SMT Numeral expression or syntax token */
	static public class Numeral extends Literal<BigInteger> implements INumeral {
		/** A value equivalent to the BigInteger, when it is in range. */
		protected int number;

		/** Constructs a Numeral with the given value. */  // FIXME - test with too big a number
		public Numeral(BigInteger i) {
			super(i);
			number = value.intValue();
		}

		/** Constructs a Numeral with the given value. */
		public Numeral(int i) {
			super(BigInteger.valueOf(i));
			number = i;
		}

		@Override
		public int intValue() { return number; }

		/** Equal to any INumeral with the same numeric value */
		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (!(o instanceof INumeral)) return false;
			return ((INumeral)o).value().equals(value);
		}

		@Override
		public int hashCode() { return value.hashCode(); }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}

	/** This class represents an SMT String literal expression or syntax token */
	static public class StringLiteral extends Literal<String> implements IStringLiteral {

		// The 'value' field holds an unquoted string

		/** Creates a string literal.  If {@code quoted} is true the argument is the raw SMT-LIB text
		 * (with enclosing quotes and escape sequences); if false it is already the unescaped Java string.
		 */
		public StringLiteral(String value, boolean quoted) {
			super(quoted ? smtConfig.utils.unescape(value) : value);
		}

		/** Equal to any IStringLiteral with the same string value */
		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (!(o instanceof IStringLiteral)) return false;
			return ((IStringLiteral)o).value().equals(value);
		}

		@Override
		public int hashCode() { return value.hashCode(); }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }

	}

	/** This class represents an SMT Decimal literal expression or syntax token */
	static public class Decimal extends Literal<BigDecimal> implements IDecimal {

		/** Creates a Decimal literal with the given value. */
		public Decimal(BigDecimal v) {
			super(v);
		}

		/** Equal to any IDecimal with the same BigDecimal value */
		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (!(o instanceof IDecimal)) return false;
			return ((IDecimal)o).value().equals(value);
		}

		@Override
		public int hashCode() { return value.hashCode(); }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}

	/** This class represents an SMT Keyword syntax token */
	static public class Keyword extends Pos.Printable implements IKeyword {
		protected String value; // Keyword string with leading colon

		/** Creates a Keyword from the given canonical string (including the leading colon). */
		public Keyword(String v) {
			super();
			value = v.intern();
		}

		@Override
		public String value() { return value; }

		@Override
		public String kind() { return "keyword"; }

		/** Equal to any IKeyword designating the same abstract keyword. */
		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (!(o instanceof IKeyword)) return false;
			return ((IKeyword)o).value().equals(value);
		}

		@Override
		public int hashCode() { return value.hashCode(); }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }

	}

	/** This class represents an SMT as-identifier AST */
	static public class AsIdentifier extends Pos.AbstractExpr implements IAsIdentifier {
		protected IIdentifier head;
		protected ISort qualifier;

		/** Creates an as-identifier from the given base identifier and sort qualifier. */
		public AsIdentifier(IIdentifier symbol, ISort qualifier) {
			this.head = symbol;
			this.qualifier = qualifier;
		}

		@Override
		public IIdentifier head() { return head; }

		@Override
		public ISymbol headSymbol() { return head.headSymbol(); }

		@Override
		public ISort qualifier() { return qualifier; }

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (!(o instanceof IAsIdentifier)) return false;
			IAsIdentifier p = (IAsIdentifier)o;
			return this.head().equals(p.head()) &&
					this.qualifier().equals(p.qualifier());
		}

		@Override
		public int hashCode() {
			int hash = (head().hashCode() << 4) ^ qualifier().hashCode();
			return hash;
		}

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }

	}

	/** This class represents an SMT parameterized-identifier AST (e.g. {@code (_ BitVec 32)}). */
	static public class ParameterizedIdentifier extends Pos.AbstractExpr implements IParameterizedIdentifier {
		protected IIdentifier head;
		protected List<IIndex> indices;

		/** Creates a parameterized identifier from the given base identifier and index list. */
		public ParameterizedIdentifier(IIdentifier symbol, List<IIndex> indices) {
			this.head = symbol;
			this.indices = indices;
		}

		@Override
		public IIdentifier head() { return head; }

		@Override
		public ISymbol headSymbol() { return head.headSymbol(); }

		@Override
		public List<IIndex> indices() { return indices; }

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (!(o instanceof IParameterizedIdentifier)) return false;
			IParameterizedIdentifier p = (IParameterizedIdentifier)o;
			if (!this.headSymbol().equals(p.headSymbol())) return false;
			if (this.indices().size() != p.indices().size()) return false;
			for (int i = 0; i < this.indices().size(); i++) {
				if (!this.indices().get(i).equals(p.indices().get(i))) return false;
			}
			return true;
		}

		@Override
		public int hashCode() {
			int hash = headSymbol().hashCode();
			for (IIndex idx : indices) hash = (hash << 1) + idx.hashCode();
			return hash;
		}

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }

	}

	/** This class represents an SMT Symbol */
	static public class Symbol extends Pos.AbstractExpr implements ISymbol {

		// FIXME - this incorporates some concrete syntax

		protected String value; // canonical string (without bars)
		protected String originalString;

		/** The argument is a Symbol string, with or without enclosing bars */
		public Symbol(String v) {
			value = v.length() > 0 && v.charAt(0) == '|' ? v.substring(1,v.length()-1) : v;
			originalString = v;
		}

		/** Returns the unique string for this symbol (e.g. modulo enclosing bars) */
		@Override
		public String value() { return value; }

		@Override
		public ISymbol headSymbol() { return this; }

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (!(o instanceof ISymbol)) return false;
			return ((ISymbol)o).value().equals(value());
		}

		@Override
		public int hashCode() { return value().hashCode(); }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException {
			return v.visit(this);
		}

		/** Returns the original String - use for debugging and use a printer to print to concrete syntax. */
		@Override
		public String toString() { return originalString; }

		@Override
		public boolean isOK() { return value.equals(Response.OK) || value.equals(Response.EMPTY); }

		@Override public boolean isError() { return false; }

//		// FIXME - do we want these?
//		public static class Parameter extends Symbol implements IParameter {
//			public Parameter(ISymbol s) { super(s.toString()); pos = s.pos(); }
//		}
//
//		public static class LetParameter extends Symbol implements ILetParameter {
//
//
//			public LetParameter(ISymbol s) { super(s.toString()); pos = s.pos();  }
//		}

	}

	/** Represents a function-application expression: a qualified identifier applied to a list of argument expressions. */
	static public class FcnExpr extends Pos.AbstractExpr implements IFcnExpr {
		protected IQualifiedIdentifier id;
		protected List<IExpr> args;

		/** Creates a function application from the given identifier and argument list. */
		public FcnExpr(IQualifiedIdentifier id, List<IExpr> args) {
			this.id = id;
			this.args = args;
		}

		@Override
		public IQualifiedIdentifier head() { return id; }

		@Override
		public List<IExpr> args() { return args; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }

	}

	/** Represents an SMT-LIB binary literal (e.g. {@code #b1010}); the value string contains only {@code 0} and {@code 1} digits. */
	static public class BinaryLiteral extends Literal<String> implements IBinaryLiteral {
		protected int length;
		protected BigInteger intValue;

		/** Creates a binary literal from a string of {@code 0} and {@code 1} digits (no {@code #b} prefix). */
		public BinaryLiteral(String unquotedValue) {
			super(unquotedValue);
			length = unquotedValue.length();
			intValue = new BigInteger(unquotedValue,2);
		}

		@Override
		public BigInteger intValue() { return intValue; }

		@Override
		public int length() { return length; }

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (!(o instanceof IBinaryLiteral)) return false;
			return ((IBinaryLiteral)o).intValue().equals(intValue);
		}

		@Override
		public int hashCode() { return intValue.hashCode(); }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}

	/** Represents an SMT-LIB hex literal (e.g. {@code #xDEAD}); the value string contains only lowercase hex digits. */
	static public class HexLiteral extends Literal<String> implements IHexLiteral {
		protected int length; // in hex digits
		protected BigInteger intValue;

		/** Creates a hex literal from a string of hex digits (no {@code #x} prefix). */
		public HexLiteral(String unquotedValue) {
			super(unquotedValue);
			length = unquotedValue.length();
			intValue = new BigInteger(unquotedValue,16);
		}

		@Override
		public BigInteger intValue() { return intValue; }

		@Override
		public int length() { return length; }

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (!(o instanceof IHexLiteral)) return false;
			return ((IHexLiteral)o).intValue().equals(intValue);
		}

		@Override
		public int hashCode() { return value.hashCode(); }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}

	/** Represents an SMT-LIB let expression: a list of bindings and a body expression. */
	static public class Let extends Pos.AbstractExpr implements ILet {
		protected List<IBinding> bindings;
		protected IExpr expression;

		/** Creates a let expression with the given bindings and body. */
		public Let(List<IBinding> bindings, IExpr expr) {
			this.bindings = bindings;
			this.expression = expr;
		}

		@Override
		public List<IBinding> bindings() { return bindings; }

		@Override
		public IExpr expr() { return expression; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }

	}

	/** Represents an SMT-LIB existential quantifier expression. */
	static public class Exists extends Pos.AbstractExpr implements IExists {
		protected List<IDeclaration> parameters;
		protected IExpr expression;

		/** Creates an exists expression with the given bound variable declarations and body. */
		public Exists(List<IDeclaration> parameters, IExpr expr) {
			this.parameters = parameters;
			this.expression = expr;
		}

		@Override
		public List<IDeclaration> parameters() { return parameters; }

		@Override
		public IExpr expr() { return expression; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }

	}

	/** Represents an SMT-LIB universal quantifier expression. */
	static public class Forall extends Pos.AbstractExpr implements IForall {
		protected List<IDeclaration> parameters;
		protected IExpr expression;

		/** Creates a forall expression with the given bound variable declarations and body. */
		public Forall(List<IDeclaration> parameters, IExpr expr) {
			this.parameters = parameters;
			this.expression = expr;
		}

		@Override
		public List<IDeclaration> parameters() { return parameters; }

		@Override
		public IExpr expr() { return expression; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }

	}

	/** Represents a sort declaration (symbol and arity) used in declare-datatype and declare-datatypes. */
	static public class SortDeclaration extends Pos.Printable implements IExpr.ISortDeclaration {
		protected ISymbol symbol;
		protected INumeral arity;

		/** Creates a sort declaration for the given sort name and arity. */
		public SortDeclaration(ISymbol symbol, INumeral arity) {
			this.symbol = symbol;
			this.arity = arity;
		}

		@Override public ISymbol symbol() { return symbol; }
		@Override public INumeral arity() { return arity; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}

	/** Represents a selector declaration within a datatype constructor. */
	static public class Selector extends Pos.Printable implements ISelector {
		protected ISymbol symbol;
		protected ISort sort;

		/** Creates a selector with the given name and result sort. */
		public Selector(ISymbol symbol, ISort sort) {
			this.symbol = symbol;
			this.sort = sort;
		}

		@Override public ISymbol symbol() { return symbol; }

		@Override public ISort sort() { return sort; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}

	/** Represents a constructor declaration within a datatype, consisting of a name and a list of selectors. */
	static public class Constructor extends Pos.Printable implements IConstructor {
		//@ nullable
		protected ISymbol symbol;
		protected List<ISelector> selectors;

		/** Creates a constructor with the given name and list of selector declarations. */
		public Constructor(ISymbol symbol, List<ISelector> selectors) {
			this.symbol = symbol;
			this.selectors = selectors;
		}

		@Override public ISymbol symbol() { return symbol; }

		@Override public List<ISelector> selectors() { return selectors; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}

	/** Represents a datatype body: a list of constructors and (for parametric forms) a list of sort parameter symbols. */
	static public class Datatype extends Pos.Printable implements ISort.IDatatype {
		protected List<IConstructor> constructors;
		/*@ nullable */ protected List<ISymbol> symbols;

		/** Creates a datatype body; {@code symbols} is non-null only for parametric (par) forms. */
		public Datatype(List<IConstructor> constructors, /*@ nullable */ List<ISymbol> symbols) {
			this.constructors = constructors;
			this.symbols = symbols;
		}

		@Override public List<IConstructor> constructors() { return constructors; }

		@Override public /*@ nullable */ List<ISymbol> symbols() { return symbols; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}

	/** Represents a sorted variable declaration (parameter name and its sort), used in forall/exists/define-fun. */
	static public class Declaration extends Pos.Printable implements IDeclaration {
		protected ISymbol parameter;
		protected ISort sort;

		/** Creates a declaration binding the given symbol to the given sort. */
		public Declaration(ISymbol parameter, ISort sort) {
			this.parameter = parameter;
			this.sort = sort;
		}

		@Override
		public ISymbol parameter() { return parameter; }

		@Override
		public ISort sort() { return sort; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}

	/** Represents a function declaration header (name, sorted parameters, result sort), used in define-funs-rec. */
	static public class FunctionDeclaration extends Pos.Printable implements IExpr.IFunctionDeclaration {
		protected ISymbol symbol;
		protected List<IDeclaration> parameters;
		protected ISort sort;

		/** Creates a function declaration with the given name, parameter declarations, and result sort. */
		public FunctionDeclaration(ISymbol symbol, List<IDeclaration> parameters, ISort sort) {
			this.symbol = symbol;
			this.parameters = parameters;
			this.sort = sort;
		}

		@Override public ISymbol symbol() { return symbol; }

		@Override public List<IDeclaration> parameters() { return parameters; }

		@Override public ISort sort() { return sort; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}

	/** Represents a let-binding: a symbol bound to an expression. */
	static public class Binding extends Pos.Printable implements IBinding {
		protected ISymbol parameter;
		protected IExpr expression;

		/** Creates a binding of the given symbol to the given expression. */
		public Binding(ISymbol parameter, IExpr expr) {
			this.parameter = parameter;
			this.expression = expr;
		}

		@Override
		public ISymbol parameter() { return parameter; }

		@Override
		public IExpr expr() { return expression; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}

	/** Represents an SMT-LIB attribute: a keyword optionally paired with a value. */
	static public class Attribute<TT extends IAttributeValue> extends Pos.Printable implements IAttribute<TT> {
		protected IKeyword keyword;
		protected TT value;

		/** Creates an attribute from the given keyword and (possibly null) value. */
		public Attribute(IKeyword keyword, TT value) {
			this.keyword = keyword;
			this.value = value;
		}

		@Override
		public IKeyword keyword() { return keyword; }

		@Override
		public TT attrValue() { return value; }

		@Override public boolean isOK() { return false; }
		@Override public boolean isError() { return false; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}

	/** Represents an SMT-LIB attributed expression ({@code (! expr attrs...)}). */
	static public class AttributedExpr extends Pos.AbstractExpr implements IAttributedExpr {
		protected IExpr expression;
		protected List<IAttribute<?>> attributes;

		/** Creates an attributed expression from the given base expression and attribute list. */
		public AttributedExpr(IExpr expression, List<IAttribute<?>> attributes) {
			this.expression = expression;
			this.attributes = attributes;
		}

		@Override
		public IExpr expr() { return expression; }

		@Override
		public List<IAttribute<?>> attributes() { return attributes; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }

	}

	static public class Logic implements ILogic {
		/** The name of the logic */
		protected ISymbol logicName;

		/** The logic's attributes */
		protected Map<IKeyword,IAttribute<?>> attributes = new HashMap<IKeyword,IAttribute<?>>();

		/** Creates a logic */
		public Logic(ISymbol name, Collection<IAttribute<?>> attributes) {
			this.logicName = name;
			for (IAttribute<?> attr: attributes) {
				this.attributes.put(attr.keyword(),attr);
			}
		}

		/** The name of the logic */
		@Override
		public ISymbol logicName() { return logicName; }

		/** The attributes, as a Map, keyed by the keyword in the attribute */
		@Override
		public Map<IKeyword,IAttribute<?>> attributes() { return attributes; }

		/** The value of a given attribute */
		@Override
		public /*@Nullable*/IAttributeValue value(IKeyword keyword) {
			IAttribute<?> attr = attributes.get(keyword);
			if (attr == null) return null;
			return attr.attrValue();
		}

		// FIXME - do we really want this here
		@Override
		public void validExpression(IExpr expr)  throws IVisitor.VisitorException {}

		@Override
		public void checkFcnDeclaration(IExpr.IIdentifier id, List<ISort> argSorts, ISort resultSort, /*@Nullable*/IExpr definition) throws IVisitor.VisitorException {}

		@Override
		public void checkSortDeclaration(IIdentifier id, List<ISort.IParameter> params, ISort expr) throws IVisitor.VisitorException {}

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}

	static public class Theory implements ITheory {
		/** The name of the theory */
		protected ISymbol theoryName;

		/** The theory attributes — last occurrence wins for duplicate keywords */
		protected Map<IKeyword,IAttribute<?>> attributes = new HashMap<IKeyword,IAttribute<?>>();

		/** All theory attributes in source order, preserving duplicates */
		protected List<IAttribute<?>> attributesList = new ArrayList<>();

		/** Creates a theory */
		public Theory(ISymbol name, Collection<IAttribute<?>> attributes) {
			this.theoryName = name;
			this.attributesList.addAll(attributes);
			for (IAttribute<?> attr: attributes) {
				this.attributes.put(attr.keyword(),attr);
			}
		}

		/** The name of the theory */
		@Override
		public ISymbol theoryName() { return theoryName; }

		/** The attributes, as a Map, keyed by the keyword in the attribute */
		@Override
		public Map<IKeyword,IAttribute<?>> attributes() { return attributes; }

		/** The value of a given attribute (last occurrence wins for duplicate keywords) */
		@Override
		public /*@Nullable*/ IAttributeValue value(IKeyword keyword) {
			IAttribute<?> attr = attributes.get(keyword);
			if (attr == null) return null;
			return attr.attrValue();
		}

		/** All values for a given attribute keyword, in source order */
		@Override
		public List<IAttributeValue> values(IKeyword keyword) {
			List<IAttributeValue> result = new ArrayList<>();
			for (IAttribute<?> attr : attributesList) {
				if (attr.keyword().equals(keyword)) {
					result.add(attr.attrValue());
				}
			}
			return result;
		}

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}

	/** Represents an expression-level error node inserted during parsing to allow error recovery. */
	static public class Error extends Pos.AbstractExpr implements IError {
		protected String message;

		/** Creates an error expression node with the given informational message. */
		public Error(String msg) {
			message = msg;
		}

		/** Returns the error message */
		@Override
		public String value() { return this.message; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }

	}

	/** Represents a match pattern: a constructor name applied to zero or more variable symbols. */
	static public class Pattern extends Pos.Printable implements IExpr.IPattern {
		protected ISymbol constructor;
		protected List<ISymbol> params;

		/** Creates a pattern from the given constructor symbol and variable list. */
		public Pattern(ISymbol constructor, List<ISymbol> params) {
			this.constructor = constructor;
			this.params = params;
		}

		@Override public ISymbol constructor() { return constructor; }
		@Override public List<ISymbol> params() { return params; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}

	/** Represents a single case in a match expression: a pattern and its result body. */
	static public class MatchCase extends Pos.Printable implements IExpr.IMatchCase {
		protected IExpr.IPattern pattern;
		protected IExpr body;

		/** Creates a match case from the given pattern and body expression. */
		public MatchCase(IExpr.IPattern pattern, IExpr body) {
			this.pattern = pattern;
			this.body = body;
		}

		@Override public IExpr.IPattern pattern() { return pattern; }
		@Override public IExpr body() { return body; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}

	/** Represents an SMT-LIB 2.7 match expression: an expression matched against a list of cases. */
	static public class Match extends Pos.AbstractExpr implements IExpr.IMatch {
		protected IExpr expression;
		protected List<IExpr.IMatchCase> cases;

		/** Creates a match expression from the given scrutinee and list of cases. */
		public Match(IExpr expr, List<IExpr.IMatchCase> cases) {
			this.expression = expr;
			this.cases = cases;
		}

		@Override public IExpr expr() { return expression; }
		@Override public List<IExpr.IMatchCase> cases() { return cases; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }

	}
}
