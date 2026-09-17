/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.sexpr;

import java.util.List;

import org.smtlib.INode;
import org.smtlib.IAttributeValue;
import org.smtlib.IPos.IPosable;

/** This interface represents S-expressions as used in SMT-LIB;
 * they are used as values for attributes in the standard concrete
 * syntax.  
 */
public interface ISexpr extends IPosable, IAttributeValue, INode {
	
	/** A word characterizing the subclass */
	String kind();
	
	/** Represents a sequence of S-expressions */
	public static interface ISeq extends ISexpr {
		List<ISexpr> sexprs();
	}
	
	/** Represents a single S-expression token */
	public static interface IToken<T> extends ISexpr  {
		T value();
	}

	// Deliberately no IFactory here, unlike IExpr/ISort: those are pervasive, fully-general
	// recursive structures with real substitutability needs, wired into every parse/type-check/
	// solver-adapter call site via SMT.Configuration's exprFactory/sortFactory. ISexpr is not
	// that kind of type -- SMT-LIB's grammar is fully specified everywhere except attribute
	// values (attribute_value ::= spec_constant | symbol | ( s_expr* )), so the parser always
	// knows exactly what it's building and constructs the real typed AST node directly (a
	// Symbol, a Numeral, ...) rather than going through a generic intermediate. The only
	// genuinely open-ended part of that one production is the sequence structure itself, which
	// Sexpr.Seq already serves directly at its one real call site (sexpr/Parser.parseSeq()) --
	// there is no untyped s-expression leaf in this grammar for a generic createToken() to be
	// needed for. See issue #84.

}
