/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;

import org.smtlib.ICommand.IScript;
import org.smtlib.IPos.IPosable;

/** This interface represents the functionality for any class implementing an SMT-LIB term or formula */
public interface IExpr extends IAccept, IPosable {
	
	/** Helpful method that indicates the class of expression, used in human-readable messages. */
	//@ pure
	String kind();

	/** The interface defining the factory type for producing objects of various subtypes of IExpr;
	 * the IPos argument is an optional argument giving information about the textual position of an expression. */
	static public interface IFactory {
		INumeral numeral(String v);
		INumeral numeral(long v);
		IDecimal decimal(String v);
		/** The argument is a pure character string, with no Java or SMTLIB escapes or enclosing quotes */
		IStringLiteral unquotedString(String v);
		/** The argument is SMTLIB escaped, with enclosing quotes */
		IStringLiteral quotedString(String v);
		IKeyword keyword(String v);
		IBinaryLiteral binary(String v);
		IHexLiteral hex(String v);
		ISymbol symbol(String v);
		IAttribute<?> attribute(IKeyword k);
		<T extends IAttributeValue> IAttribute<T> attribute(IKeyword k, T value);
		//@ requires attributes.size() > 0;
		IAttributedExpr attributedExpr(IExpr e, List<IAttribute<?>> attributes);
		<T extends IAttributeValue> IAttributedExpr attributedExpr(IExpr e, IKeyword key, /*@Nullable*/T value);
        IFcnExpr fcn(IQualifiedIdentifier id, List<IExpr> args);
        IFcnExpr fcn(IQualifiedIdentifier id, IExpr... args);
		//@ requires num.size() > 0;
		IParameterizedIdentifier id(ISymbol symbol, List<INumeral> num);
		IAsIdentifier id(IIdentifier identifier, ISort qualifier);
		//@ requires bindings.size() > 0;
		ILet let(List<IBinding> bindings, IExpr e);
		IBinding binding(ISymbol.ILetParameter symbol, IExpr expr);
		IDeclaration declaration(ISymbol.IParameter symbol, ISort sort);
		//@ requires params.size() > 0;
		IForall forall(List<IDeclaration> params, IExpr e);
		//@ requires params.size() > 0;
		IExists exists(List<IDeclaration> params, IExpr e);

		IScript script(/*@Nullable*/IStringLiteral filename, /*@Nullable*/List<ICommand> commands);

		IError error(String text);

		// FIXME - get rid of the following
		INumeral numeral(String v, /*@Nullable*//*@ReadOnly*/ IPos pos);
		IDecimal decimal(String v, /*@Nullable*//*@ReadOnly*/ IPos pos);
		/** THe argument is a pure character string, with no Java or SMTLIB escapes or enclosing quotes */
		IStringLiteral unquotedString(String v, /*@Nullable*//*@ReadOnly*/ IPos pos);
		/** The argument is SMTLIB escaped, with enclosing quotes */
		IStringLiteral quotedString(String v, /*@Nullable*//*@ReadOnly*/ IPos pos);
		IKeyword keyword(String v, /*@Nullable*//*@ReadOnly*/ IPos pos);
		IBinaryLiteral binary(String v, /*@Nullable*//*@ReadOnly*/ IPos pos);
		IHexLiteral hex(String v, /*@Nullable*//*@ReadOnly*/ IPos pos);
		ISymbol symbol(String v, /*@Nullable*//*@ReadOnly*/ IPos pos);
		IAttribute<?> attribute(IKeyword k, /*@Nullable*//*@ReadOnly*/ IPos pos);
		<T extends IAttributeValue> IAttribute<T> attribute(IKeyword k, T value, /*@Nullable*//*@ReadOnly*/ IPos pos);
		//@ requires attributes.size() > 0;
		IAttributedExpr attributedExpr(IExpr e, List<IAttribute<?>> attributes, /*@Nullable*//*@ReadOnly*/ IPos pos);
		<T extends IAttributeValue> IAttributedExpr attributedExpr(IExpr e, IKeyword key, /*@Nullable*/T value, /*@Nullable*//*@ReadOnly*/ IPos pos);
        IFcnExpr fcn(IQualifiedIdentifier id, List<IExpr> args, /*@Nullable*//*@ReadOnly*/ IPos pos);
		//@ requires num.size() > 0;
		IParameterizedIdentifier id(ISymbol symbol, List<INumeral> num, /*@Nullable*//*@ReadOnly*/ IPos pos);
		IAsIdentifier id(IIdentifier identifier, ISort qualifier, /*@Nullable*//*@ReadOnly*/ IPos pos);
		//@ requires bindings.size() > 0;
		ILet let(List<IBinding> bindings, IExpr e, /*@Nullable*//*@ReadOnly*/ IPos pos);
		IBinding binding(ISymbol.ILetParameter symbol, IExpr expr, /*@Nullable*//*@ReadOnly*/IPos pos);
		IDeclaration declaration(ISymbol.IParameter symbol, ISort sort, /*@Nullable*//*@ReadOnly*/IPos pos);
		//@ requires params.size() > 0;
		IForall forall(List<IDeclaration> params, IExpr e, /*@Nullable*//*@ReadOnly*/ IPos pos);
		//@ requires params.size() > 0;
		IExists exists(List<IDeclaration> params, IExpr e, /*@Nullable*//*@ReadOnly*/ IPos pos);

		IError error(String text, /*@Nullable*//*@ReadOnly*/ IPos pos);
	}
	
	/** This interface represents all literal (explicit constant) expressions. */
	static public interface ILiteral extends IExpr, IAttributeValue {
	}
	
	/** This interface represents non-negative integers of arbitrary size. */
	static public interface INumeral extends ILiteral {
		//@ ensures compareTo(BigInteger.ZERO) >= 0;
		/*@ pure */
		BigInteger value();
		
		//@ ensures \result >= 0;
		/*@ pure */
		int intValue();
		
		//@ public invariant value().compareTo(BigInteger.valueOf(Integer.INT_MAX)) <= 0 ==> value().intValue() == intValue();
	}
	
	/** This interface represents non-negative decimal numbers of arbitrary size
	 * (i.e. an arbitrary non-negative integer divided by an arbitrary non-negative power of ten).
	 */
	static public interface IDecimal extends ILiteral {
		//@ pure
		BigDecimal value();
	}
	
	/** This interface represents SMT-LIB ids; equal ids have equal (using .equals) values
	 * of value().
	 */
	static public interface ISymbol extends IAttributeValue, IIdentifier {
		/** A String giving the canonical value of symbol. */
		//@ pure
		String value();

		/** A printable String giving the original text of this symbol. */
		//@ pure
		String toString();
		
		static public interface IParameter extends ISymbol {}
		static public interface ILetParameter extends ISymbol {}
	}
	
	/** This interface represents SMT-LIB attribute and infoflag names. */
	static public interface IKeyword extends IAccept, IPosable{
		/** A canonical representation of keyword key */
		//@ pure
		String value();
		
		/** The original textual representation of the keyword */
		//@ pure
		String toString();
		
		/** Helpful method that indicates the class of expression, used in human-readable messages. */
		//@ pure
		String kind();
	}
	
	/** This interface represents SMT-LIB binary literals */
	static public interface IBinaryLiteral extends ILiteral {
		/** Returns a canonical value of the binary literal: 0 and 1 digits from MSB to LSB */
		String value();
		
		/** The binary value as an unsigned integer */
		BigInteger intValue();
		
		/** Number of binary bits */
		int length();
	}
	
	/** This interface represents SMT-LIB hex literals */
	static public interface IHexLiteral extends ILiteral {
		/** Returns a canonical value of the hex literal; lower-case hex digits from MS to LS */
		String value(); 
		
		/** The hex value as an unsigned integer */
		BigInteger intValue();
		
		/** Number of hex digits */
		int length();
	} // FIXME HexLiteral
	
	/** This interface represents SMT-LIB string literals */
	static public interface IStringLiteral extends ILiteral {
		/** Returns the value without enclosing quotes and without any escape sequences */
		//@ pure
		String value();

		/** Returns a value with enclosing quotes and appropriate SMT-LIB escape sequences so that the String value
		 * can be represented with SMT-LIB printable characters; the result may have explicit newline characters. */
		//@ pure
		String toString();
	}
	
	/** This interface represents SMT-LIB expressions that are a function identifier applied to one or more arguments. */
	static public interface IFcnExpr extends IExpr {
		/** The function identifier */
		//@ pure
		IQualifiedIdentifier head();
		
		/** The arguments of the function */
		//@ ensures \result.size() > 0;
		//@ pure
		List<IExpr> args();
	}

	/** This interface represents SMT-LIB identifiers for function ids (either ids or parameterized ids
	 * or as-type identifiers) */
	static public interface IQualifiedIdentifier extends IExpr {
		/** The head symbol of the identifier */
		ISymbol headSymbol();
	}
	
	/** This interface represents SMT-LIB identifiers (either ids or parameterized ids) */
	static public interface IIdentifier extends IQualifiedIdentifier {
		/** The head symbol of the identifier */
		ISymbol headSymbol();

	}
	
	/** This interface represents SMT-LIB identifiers that are sort qualifiers on function ids */
	static public interface IAsIdentifier extends IQualifiedIdentifier {
		/** The head of the identifier */
		IIdentifier head();
		
		/** The head symbol of the identifier */
		ISymbol headSymbol();

		/** The Sort qualifier */
		ISort qualifier();
	}
	
	/** This interface represents SMT-LIB identifiers (either ids or parameterized ids) */
	static public interface IParameterizedIdentifier extends IIdentifier {
		
		IIdentifier head();
		
		/** The head symbol of the identifier */
		ISymbol headSymbol();
		
		/** The non-negative integer parameters of the identifier */
		//@ ensures \result.size() > 0;
		List<INumeral> numerals();
	}
	
	/** This interface represents an SMT-LIB expression with attributes. */
	static public interface IAttributedExpr extends IExpr {
		//@ pure
		IExpr expr();
		//@ ensures \result.size() > 0;
		//@ pure
		List<IAttribute<?>> attributes();
	}
	
	/** This interface represents the general class of attribute values; in the
	 * abstract syntax it has no particular structure, though it does include
	 * true, false, string literals, numerals, and various pre-defined constants.
	 */
	static public interface IAttributeValue extends IResponse, IPos.IPosable {
	}
	
	/** This interface represents an SMT-LIB attribute-value pair */
	static public interface IAttribute<TT extends IAttributeValue> extends IAccept, IPosable, IResponse {
		//@ pure
		IKeyword keyword();
		//@ pure
		/*@Nullable*/ TT attrValue();
	}
	
	/** This interface represents a declaration of a parameter and its sort */
	static public interface IDeclaration extends IAccept, IPosable {
		ISymbol.IParameter parameter();
		ISort sort();
	}
	
	/** This interface represents a binding of a parameter and an expression */
	static public interface IBinding extends IAccept, IPosable {
		ISymbol.ILetParameter parameter();
		IExpr expr();
	}
	
	/** This interface represents an SMT-LIB let-expression */
	static public interface ILet extends IExpr {
		//@ ensures \result.size() > 0;
		List<IBinding> bindings();
		IExpr expr();
	}

	/** This interface represents an SMT-LIB quantified forall expression */
	static public interface IForall extends IExpr {
		//@ ensures \result.size() > 0;
		List<IDeclaration> parameters();
		IExpr expr();
	}
	
	/** This interface represents an SMT-LIB quantified exists expression */
	static public interface IExists extends IExpr {
		//@ ensures \result.size() > 0;
		List<IDeclaration> parameters();
		IExpr expr();
	}
	
	/** This interface represents an error, e.g. a parsing error that is part of a larger
	 * expression.  Using an error expression as a sub-expression allows further error
	 * checking to be performed.
	 */
	static public interface IError extends IExpr {
		/** Returns an informational message about the error */
		String value();
	}

}
