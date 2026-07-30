package org.smtlib.sexpr;

import org.smtlib.IPos;

/** An interface to indicate AST classes that are also lexical tokens in the 
 * concrete syntax. 
 * @author David R. Cok
 *
 */
public interface ILexToken {
	/** The lexical position of the token */
	/*@Nullable*//*@ReadOnly*/ IPos pos();
	
	/** A short word characterizing the class of token (e.g. {@code "numeral"}, {@code "symbol"}). */
	String kind();

	/** Returns true if this token represents a lexical error. */
	boolean isError();
	/** Returns true if this token is a left parenthesis. */
	default boolean isLP()  { return false; }
	/** Returns true if this token is a right parenthesis. */
	default boolean isRP()  { return false; }
	/** Returns true if this token signals the end of the input. */
	default boolean isEOD() { return false; }
}
