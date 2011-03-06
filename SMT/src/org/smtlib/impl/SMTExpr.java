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

// FIXME - Decide whether we use reference or structural equality - either complete or remove equals and hashCode

/** This class defines a number of subclasses that implement the SMT-LIB abstract AST */
public abstract class SMTExpr implements IExpr {
	
	/** Just a convenient base class to provide some method implementations */
	static abstract public class Literal<T> extends Pos.Posable {
		protected T value;
		public T value() { return value; }
		public Literal(T value) { this.value = value; }
		public boolean isOK() { return false; }
		public boolean isError() { return false; }
		
		/** Just for debugging - use a Printer for proper output */
		public String toString() { return value.toString(); }
	}

	/** This class represents a Numeral expression or syntax token */
	static public class Numeral extends Literal<BigInteger> implements INumeral {
		protected int number;
		public Numeral(BigInteger i) {
			super(i);
			number = value.intValue();
		}
		
		public Numeral(int i) {
			super(BigInteger.valueOf(i));
			number = i;
		}
		
		@Override
		public int intValue() { return number; }
		
		@Override
		public String kind() { return "numeral"; }
		
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
	
	static public class StringLiteral extends Literal<String>  implements IStringLiteral {
		
		/** If quoted is true, then the value should be the string with all escape sequences intact and
		 * enclosing quotes in place; if quoted is false, the value should not have enclosing quotes and
		 * any escape sequences should be replaced by the actual characters.
		 */
		public StringLiteral(String value, boolean quoted) {
			super(quoted ? Utils.unescape(value) : value);
		}
		
		/** For a StringLiteral, toString produces a properly escaped and quoted string */
		public String toString() { return Utils.quote(value); }

		
		@Override
		public String kind() { return "string-literal"; }

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
	
	static public class Decimal extends Literal<BigDecimal> implements IDecimal {
		
		public Decimal(BigDecimal v) {
			super(v);
		}
		
		@Override
		public String kind() { return "decimal"; }

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
	
	static public class Keyword extends Pos.Posable  implements IKeyword {
		protected String value;
		
		public Keyword(String v) {
			super();
			value = v;
		}
		
		@Override
		public String value() { return value; }
		
		@Override
		public String kind() { return "keyword"; }

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

		/** Just for debugging - use a Printer for proper output */
		public String toString() { return value.toString(); }
	}
	
	static public class ParameterizedIdentifier extends Pos.Posable implements IParameterizedIdentifier {
		protected ISymbol head;
		protected List<INumeral> numerals = new LinkedList<INumeral>();
		
		public ParameterizedIdentifier(ISymbol symbol, List<INumeral> nums) {
			this.head = symbol;
			this.numerals = nums;
		}
		
		@Override
		public ISymbol headSymbol() { return head; }
		
		@Override
		public List<INumeral> numerals() { return numerals; }
		
		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (!(o instanceof ParameterizedIdentifier)) return false;
			ParameterizedIdentifier p = (ParameterizedIdentifier)o;
			if (!this.headSymbol().equals(p.headSymbol())) return false;
			if (this.numerals().size() != p.numerals().size()) return false;
			Iterator<INumeral> iter1 = this.numerals().iterator();
			Iterator<INumeral> iter2 = p.numerals().iterator();
			while (iter1.hasNext() && iter2.hasNext()) {
				if (!iter1.next().equals(iter2.next())) return false;
			}
			return iter1.hasNext() == iter2.hasNext();
		}
		
		@Override
		public int hashCode() {
			int hash = headSymbol().hashCode();
			Iterator<INumeral> iter = this.numerals().iterator();
			while (iter.hasNext()) {
				hash = (hash<<1) + iter.next().hashCode();
			}
			return hash;
		}
		
		@Override
		public String kind() { return "parameterizedSymbol"; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }

		/** Just for debugging - use a Printer for proper output */
		public String toString() { return org.smtlib.sexpr.Printer.write(this); }

	}
	
	static public class AsIdentifier extends Pos.Posable implements IAsIdentifier {
		protected IIdentifier head;
		protected ISort qualifier;
		
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
			if (!(o instanceof AsIdentifier)) return false;
			AsIdentifier p = (AsIdentifier)o;
			return this.head().equals(p.head()) &&
					this.qualifier().equals(p.qualifier);
		}
		
		@Override
		public int hashCode() {
			int hash = (head().hashCode() << 4) ^ qualifier().hashCode();
			return hash;
		}
		
		@Override
		public String kind() { return "qualifiedSymbol"; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
		
		/** Just for debugging - use a Printer for proper output */
		public String toString() { return org.smtlib.sexpr.Printer.write(this); }

	}
	
	static public class Symbol extends Pos.Posable  implements ISymbol {
		
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
		
		/** Returns the original String - use for debugging and use a printer to print to concrete syntax. */
		@Override
		public String toString() { return originalString; }
		
		@Override
		public ISymbol headSymbol() { return this; }
		
		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (!(o instanceof Symbol)) return false;
			return ((Symbol)o).value().equals(value());
		}
		
		@Override
		public int hashCode() {
			return value().hashCode();
		}
		
		@Override
		public String kind() { return "symbol"; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { 
			return v.visit(this); 
		}
		
		@Override
		public boolean isOK() { return value.equals(Response.OK); }

		@Override
		public boolean isError() { return false; }
		
		public static class Parameter extends Symbol implements IParameter {
			public Parameter(ISymbol s) { super(s.toString()); pos = s.pos(); }
		}

		public static class LetParameter extends Symbol implements ILetParameter {
			public LetParameter(ISymbol s) { super(s.toString()); pos = s.pos();  }
		}

	}
	
	static public class FcnExpr extends Pos.Posable implements IFcnExpr {
		protected IQualifiedIdentifier id;
		protected List<IExpr> args;
		
		public FcnExpr(IQualifiedIdentifier id, List<IExpr> args) {
//			super(new LinkedList<ISexpr>());
//			sexprs().add((ISexpr)id);
//			for (IExpr e: args) sexprs().add((ISexpr)e);
			this.id = id;
			this.args = args;
		}

		@Override
		public IQualifiedIdentifier head() {
			return id;
		}

		@Override
		public List<IExpr> args() {
			return args;
		}
		
		@Override
		public String kind() { return "fcn"; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }

		/** Just for debugging - use a Printer for proper output */
		public String toString() { return org.smtlib.sexpr.Printer.write(this); }

	}

	static public class BinaryLiteral extends Literal<String>  implements IBinaryLiteral {
		
		public BinaryLiteral(String unquotedValue) {
			super(unquotedValue.substring(2));
			length = unquotedValue.length()-2;
			intvalue = new BigInteger(unquotedValue.substring(2),2);
		}
		
		int length;
		BigInteger intvalue;
		
		@Override
		public BigInteger intValue() { return intvalue; }
		
		@Override
		public int length() { return length; }
		
		@Override
		public String kind() { return "binary"; }

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (!(o instanceof IBinaryLiteral)) return false;
			return ((IBinaryLiteral)o).intValue().equals(intvalue);
		}
		
		@Override
		public int hashCode() { return intvalue.hashCode(); }
		
		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}
	
	static public class HexLiteral extends Literal<String>  implements IHexLiteral {
		
		public HexLiteral(String unquotedValue) {
			super(unquotedValue.substring(2));
			length = unquotedValue.length() - 2;
			intvalue = new BigInteger(unquotedValue.substring(2),16);
		}
		
		int length; // in hex digits
		BigInteger intvalue;
		
		@Override
		public BigInteger intValue() { return intvalue; }
		
		@Override
		public int length() { return length; }
		
		@Override
		public String kind() { return "hex-literal"; }

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (!(o instanceof IHexLiteral)) return false;
			return ((IHexLiteral)o).intValue().equals(intvalue);
		}
		
		@Override
		public int hashCode() { return value.hashCode(); }
		
		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}
	
	static public class Let extends Pos.Posable  implements ILet {
		
		protected List<IBinding> bindings;
		protected IExpr expression;
		
		public Let(List<IBinding> bindings, IExpr expr) {
			this.bindings = bindings;
			this.expression = expr;
		}
		
		@Override
		public List<IBinding> bindings() { return bindings; }
		
		@Override
		public IExpr expr() { return expression; }

		@Override
		public String kind() {
			return "let";
		}

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
		
	}

	static public class Exists extends Pos.Posable implements IExists {

		protected List<IDeclaration> parameters;
		protected IExpr expression;
		
		public Exists(List<IDeclaration> parameters, IExpr expr) {
			this.parameters = parameters;
			this.expression = expr;
		}
		
		@Override
		public List<IDeclaration> parameters() { return parameters; }
		
		@Override
		public IExpr expr() { return expression; }

		@Override
		public String kind() {
			return "exists";
		}

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}

	static public class Forall extends Pos.Posable implements IForall {

		protected List<IDeclaration> parameters;
		protected IExpr expression;
		
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

		@Override
		public String kind() {
			return "forall";
		}
	}

	static public class Declaration extends Pos.Posable implements IDeclaration {
		ISymbol.IParameter parameter;
		ISort sort;
		
		public Declaration(ISymbol.IParameter parameter, ISort sort) {
			this.parameter = parameter;
			this.sort = sort;
		}
		
		@Override
		public ISymbol.IParameter parameter() { return parameter; }
		
		@Override
		public ISort sort() { return sort; }
		
		// @Override
		public String kind() {
			return "declaration";
		}

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}

	static public class Binding extends Pos.Posable implements IBinding {
		ISymbol.ILetParameter parameter;
		IExpr expr;
		
		public Binding(ISymbol.ILetParameter parameter, IExpr expr) {
			this.parameter = parameter;
			this.expr = expr;
		}
		
		@Override
		public ISymbol.ILetParameter parameter() { return parameter; }
		
		@Override
		public IExpr expr() { return expr; }
		
		// @Override
		public String kind() {
			return "binding";
		}

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}
	
	static public class Attribute<TT extends IAttributeValue> extends Pos.Posable implements IAttribute<TT> {
		protected IKeyword keyword;
		protected TT value;
		protected /*@Nullable*//*@ReadOnly*/IPos pos;
		
		public Attribute(IKeyword keyword, TT value) {
			this.keyword = keyword;
			this.value = value;
		}
		
		public boolean isOK() { return false; }
		
		public boolean isError() { return false; }
		
		public IKeyword keyword() { return keyword; }
		
		public TT attrValue() { return value; }
		
		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }

		// for debugging only
		@Override
		public String toString() {
			return keyword.toString() + " " + value.toString();
		}
	}
	
	static public class AttributedExpr extends Pos.Posable implements IAttributedExpr {
		
		protected IExpr expression;
		protected List<IAttribute<?>> attributes;
		
		public AttributedExpr(IExpr expression, List<IAttribute<?>> attributes) {
			this.expression = expression;
			this.attributes = attributes;
		}

		@Override
		public String kind() {
			return "attributedExpr";
		}

		@Override
		public IExpr expr() {
			return expression;
		}

		@Override
		public List<IAttribute<?>> attributes() {
			return attributes;
		}

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }

		// For debugging only
		@Override
		public String toString() {
			String s = "(! " + expr().toString();
			for (IAttribute<?> a: attributes) s = s + " " + a.toString();
			return s + ")";
		}
	}
	
	static public class Logic implements ILogic {
		/** Creates a logic */
		public Logic(ISymbol name, Collection<IAttribute<?>> attributes) {
			this.logicName = name;
			for (IAttribute<?> attr: attributes) {
				this.attributes.put(attr.keyword().value(),attr);
			}
		}
		/** The name of the logic */
		protected ISymbol logicName;
		
		/** The logic's attributes */
		protected Map<String,IAttribute<?>> attributes = new HashMap<String,IAttribute<?>>();
		
		/** The name of the logic */
		@Override
		public ISymbol logicName() { return logicName; }
		
		/** The attributes, as a Map, keyed by the keyword in the attribute */
		@Override
		public Map<String,IAttribute<?>> attributes() { return attributes; }
		
		/** The value of a given attribute */
		@Override
		public /*@Nullable*/IAttributeValue value(String keyword) {
			IAttribute<?> attr = attributes.get(keyword);
			if (attr == null) return null;
			return attr.attrValue();
		}
		
		// @Override
		public String kind() { return "logic"; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}
	
	static public class Theory implements ITheory {
		/** Creates a theory */
		public Theory(ISymbol name, Collection<IAttribute<?>> attributes) {
			this.theoryName = name;
			for (IAttribute<?> attr: attributes) {
				this.attributes.put(attr.keyword().value(),attr);
			}
		}
		/** The name of the theory */
		protected ISymbol theoryName;
		
		/** The theory attributes */
		protected Map<String,IAttribute<?>> attributes = new HashMap<String,IAttribute<?>>();
		
		/** The name of the theory */
		@Override
		public ISymbol theoryName() { return theoryName; }
		
		/** The attributes, as a Map, keyed by the keyword in the attribute */
		@Override
		public Map<String,IAttribute<?>> attributes() { return attributes; }
		
		/** The value of a given attribute */
		@Override
		public /*@Nullable*/ IAttributeValue value(String keyword) {
			IAttribute<?> attr = attributes.get(keyword);
			if (attr == null) return null;
			return attr.attrValue();
		}
		
		// @Override
		public String kind() { return "theory"; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}
	
	static public class Error extends Pos.Posable  implements IError {
		protected String message;
		
		public Error(String msg) {
			message = msg;
		}
		
		/** Returns the error message */
		@Override
		public String value() {
			return this.message;
		}
		
		/** Shows a string for debugging; use an IPrinter to get concrete syntax */
		@Override
		public String toString() {
			return "Error: " + this.message;
		}
		
		@Override
		public String kind() { return "error"; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}
	

}
