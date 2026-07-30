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
import org.smtlib.IExpr.IDeclaration;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IPos.IPosable;

// FIXME - any new s-expressions

/** This interface represents the functionality for any class implementing an SMT-LIB term or formula */
public interface IExpr extends INode, IPosable, IAttributeValue {
    
    default boolean isError() { return false; }

	
	/** The interface defining the factory type for producing objects of various subtypes of IExpr;
	 * the IPos argument is an optional argument giving information about the textual position of an expression. */
	static public interface IFactory {
		/** Creates an INumeral object; the argument must be a string of digits. */
		INumeral numeral(String v);
		/** Creates an INumeral object; the argument must be non-negative. */
		//@ requires v >= 0;
		INumeral numeral(long v);
		/** Creates an IDecimal object; the argument must be a string of digits with just one decimal point. */
		IDecimal decimal(String v);
		/** Creates an IStringLiteral from a pure character string with no SMT-LIB escapes or enclosing quotes. */
		IStringLiteral unquotedString(String v);
		/** Creates an IStringLiteral from a string that is SMT-LIB escaped with enclosing quotes. */
		IStringLiteral quotedString(String v);
		/** Creates an IKeyword object from a canonical string representation. */
		IKeyword keyword(String v);
		/** Creates an IBinaryLiteral from a string of 0 and 1 digits. */
		IBinaryLiteral binary(String v);
		/** Creates an IHexLiteral object from a string of hex digits (either case). */
		IHexLiteral hex(String v);
		/** Creates an ISymbol object from a canonical String representation of the symbol. */
		ISymbol symbol(String v);
		/** Creates an attribute with just a keyword and no attribute value. */
		IAttribute<?> attribute(IKeyword k);
		/** Creates an attribute with a keyword and a value. */
		<T extends IAttributeValue> IAttribute<T> attribute(IKeyword k, T value);
		/** Creates an attributed expression (an expression with a positive number of attributes). */
		//@ requires attributes.size() > 0;
		IAttributedExpr attributedExpr(IExpr e, List<IAttribute<?>> attributes);
		/** Creates an attributed expression with just one attribute. */
		<T extends IAttributeValue> IAttributedExpr attributedExpr(IExpr e, IKeyword key, /*@Nullable*/T value);
		/** Creates a function expression (perhaps with an empty argument list). */
        IFcnExpr fcn(IQualifiedIdentifier id, List<IExpr> args);
		/** Creates a function expression (perhaps with an empty argument list). */
        IFcnExpr fcn(IQualifiedIdentifier id, IExpr... args);
        /** Creates a parameterized identifier from a symbol and a non-empty list of indices (each INumeral or ISymbol). */
        //@ requires indices.size() > 0;
		IParameterizedIdentifier id(ISymbol symbol, List<IIndex> indices);
		/** Creates an 'as' identifier from an identifier and a sort qualifier. */
		IAsIdentifier id(IIdentifier identifier, ISort qualifier);
		/** Creates a Let expression. */
		//@ requires bindings.size() > 0;
		ILet let(List<IBinding> bindings, IExpr e);
		/** Creates a binding for a Let expression. */
		IBinding binding(ISymbol symbol, IExpr expr);
		/** Creates a parameter declaration. */
		IDeclaration declaration(ISymbol symbol, ISort sort);
		/** Creates a Forall expression. */
		//@ requires params.size() > 0;
        IForall forall(List<IDeclaration> params, IExpr e);
		/** Creates a Forall expression with trigger patterns. */
		//@ requires params.size() > 0;
        IForall forall(List<IDeclaration> params, IExpr e, List<IExpr> patterns);
		/** Creates an Exists expression. */
		//@ requires params.size() > 0;
        IExists exists(List<IDeclaration> params, IExpr e);
		/** Creates an Exists expression with trigger patterns. */
		//@ requires params.size() > 0;
        IExists exists(List<IDeclaration> params, IExpr e, List<IExpr> patterns);

		/** Creates an error expression. */
		IError error(String text);

		/** Creates a sort declaration (symbol + arity) for use in declare-datatype(s). */
		ISortDeclaration sortDeclaration(ISymbol symbol, INumeral arity);
		/** Creates a selector declaration. */
		ISelector selector(ISymbol symbol, ISort sort);
		/** Creates a constructor declaration. */
		IConstructor constructor(ISymbol symbol, List<ISelector> selectors);
		/** Creates a datatype declaration; symbols is non-null only for parametric (par) forms. */
		ISort.IDatatype datatype(List<IConstructor> constructors, /*@nullable*/ List<ISymbol> symbols);
		/** Creates a function declaration (used in define-funs-rec). */
		IFunctionDeclaration functionDeclaration(ISymbol symbol, List<IDeclaration> parameters, ISort sort);

		/** Creates a match pattern. */
		IPattern pattern(ISymbol constructor, List<ISymbol> params);
		/** Creates a single match case. */
		IMatchCase matchCase(IPattern pattern, IExpr body);
		/** Creates a match expression. */
		IMatch match(IExpr expr, List<IMatchCase> cases);

	}
	
	/** This interface represents all literal (explicit constant) expressions. */
	static public interface ILiteral extends IExpr, IAttributeValue {
	}

	/** Marker interface for the two legal index types in a parameterized identifier: INumeral and ISymbol. */
	static public interface IIndex extends IExpr {
	}

	/** This interface represents non-negative integers of arbitrary size. */
	static public interface INumeral extends ILiteral, IIndex {
		//@ ensures compareTo(BigInteger.ZERO) >= 0;
		/*@ pure */
		BigInteger value();
		
		//@ ensures value().compareTo(BigInteger.valueOf(Integer.INT_MAX)) <= 0 ==> value().intValue() == \result;
		//@ ensures \result >= 0;
		/*@ pure */
		int intValue();
		
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
	static public interface ISymbol extends IAttributeValue, IIdentifier, IIndex {
		/** A String giving the canonical value of symbol. */
		//@ pure
		String value();

		/** A printable String giving the original text of this symbol. */
		//@ pure
		@Override
		String toString();
	}
	
    /** Pairs a sort name with its arity; used in declare-datatype and declare-datatypes. */
    static public interface ISortDeclaration extends INode, IPosable {
        ISymbol symbol();
        INumeral arity();
    }

    /** A selector declaration within a constructor; pairs a selector name with its result sort. */
    static public interface ISelector extends INode, IPosable {
        ISymbol symbol();
        ISort sort();
        //@ pure
        @Override
        String toString();
    }

    /** A constructor declaration within a datatype; pairs a constructor name with its selectors. */
    static public interface IConstructor extends INode, IPosable {
        ISymbol symbol();
        List<? extends ISelector> selectors();
        //@ pure
        @Override
        String toString();
    }
    
	/** This interface represents SMT-LIB attribute and infoflag names. */
	static public interface IKeyword extends INode, IPosable {
		/** A canonical representation of keyword key */
		//@ pure
		String value();
		
		/** The original textual representation of the keyword */
		//@ pure
		@Override
		String toString();
		
		/** Helpful method that indicates the class of expression, used in human-readable messages. */
		//@ pure
		String kind();
		
		@Override
		boolean equals(Object o);
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
		/** Returns a canonical value of the hex literal; lower-case hex digits from most-significant to least-significant */
		String value(); 
		
		/** The hex value as an unsigned integer */
		BigInteger intValue();
		
		/** Number of hex digits */
		int length();
	}
	
	// FIXME - document toString for all interfaces
	// FIXME - review headSymbol, head
	// FIXME - review IParameter, ILetParameter
	
	/** This interface represents SMT-LIB string literals */
	static public interface IStringLiteral extends ILiteral {
		/** Returns the value without enclosing quotes and without any escape sequences; there may be explicit new line (and other white space characters) */
		//@ pure
		String value();

		/** Returns a value with enclosing quotes and appropriate SMT-LIB escape sequences so that the String value
		 * can be represented with SMT-LIB printable characters; the result may have explicit newline characters. */
		//@ pure
		@Override
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
		@Override
		ISymbol headSymbol();

	}
	
	/** This interface represents SMT-LIB identifiers that are sort qualifiers on function ids */
	static public interface IAsIdentifier extends IQualifiedIdentifier {
		/** The head of the identifier */
		IIdentifier head();
		
		/** The head symbol of the identifier */
		@Override
		ISymbol headSymbol();

		/** The Sort qualifier */
		ISort qualifier();
	}
	
	/** This interface represents SMT-LIB parameterized identifiers */
	static public interface IParameterizedIdentifier extends IIdentifier {

		// TODO - document
		IIdentifier head();

		/** The head symbol of the identifier */
		@Override
		ISymbol headSymbol();

		/** All indices of the identifier; each element is either an INumeral or an ISymbol.
		 *  Symbol indices are allowed only in SMT-LIB V2.5 and later. */
		//@ ensures \result.size() > 0;
		List<IIndex> indices();
	}
	
	/** This interface represents an SMT-LIB expression with attributes. */
	static public interface IAttributedExpr extends IExpr {
		//@ pure
		IExpr expr();
		
		//@ ensures \result.size() > 0;
		//@ pure
		List<IAttribute<?>> attributes();
	}
	
	/** This interface represents an SMT-LIB attribute-value pair; the value may be null (keyword-only attribute). */
	static public interface IAttribute<TT extends IAttributeValue> extends INode, IPosable, IResponse {
		//@ pure
		IKeyword keyword();

		//@ pure
		/*@Nullable*/ TT attrValue();
	}
	
    /** This interface represents a declaration of a parameter and its sort */
    static public interface IDeclaration extends INode, IPosable {
        ISymbol parameter();
        ISort sort();
    }
    
    /** A function declaration: a name, a parameter list (sorted variables), and a result sort;
     *  used in the header list of define-funs-rec. */
    static public interface IFunctionDeclaration extends INode, IPosable {
        ISymbol symbol();
        List<IDeclaration> parameters();
        ISort sort();
    }
    
	/** This interface represents a binding of a parameter and an expression */
	static public interface IBinding extends INode, IPosable {
		ISymbol parameter();
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

	/** This interface represents a match pattern: either a bare symbol (variable/nullary-constructor)
	 *  or a constructor applied to zero or more variable symbols. */
	static public interface IPattern extends INode, IPosable {
		ISymbol constructor();
		List<ISymbol> params();
	}

	/** This interface represents one case in a match expression: a pattern and its body. */
	static public interface IMatchCase extends INode, IPosable {
		IPattern pattern();
		IExpr body();
	}

	/** This interface represents an SMT-LIB 2.7 match expression. */
	static public interface IMatch extends IExpr {
		IExpr expr();
		List<IMatchCase> cases();
	}

}
