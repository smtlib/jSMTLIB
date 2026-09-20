/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.impl;


import java.io.IOException;

import org.smtlib.*;
import org.smtlib.IParser;
import org.smtlib.sexpr.Printer;

/** This abstract class is the base class for all commands within this implementation. */
public abstract class Command extends Pos.Printable implements ICommand {

	/** Whitespace/comment text, if any, that appeared on the same physical source line
	 *  immediately after this command's closing parenthesis (before the next line
	 *  terminator) -- typically a trailing "; comment". Captured separately from a
	 *  standalone comment (which parses as its own C_comment) so that sending this command
	 *  to a solver stays exactly one real source line per one sent line, regardless of
	 *  whether a trailing comment is present. Never forwarded to a solver (see
	 *  AbstractSolver's command dispatch); printed back out here purely for round-trip/echo
	 *  fidelity, since it was real text in the original source. */
	protected /*@Nullable*/ String trailingText;

	/** The text captured in {@link #trailingText}, or null if this command has none. */
	public /*@Nullable*/ String trailingText() { return trailingText; }

	/** Sets the text captured in {@link #trailingText}. */
	public void setTrailingText(/*@Nullable*/ String text) { trailingText = text; }

	/** The command name */
	abstract public String commandName();

	/** Writes the command arguments (everything between the opening parenthesis +
	 *  command name and the closing parenthesis); called by {@link #write}.
	 *  Extension commands override this; standard commands are printed via the visitor. */
	public void writeArgs(Printer p) throws IOException, IVisitor.VisitorException {}

	/** Writes the full command: {@code (commandName() <writeArgs output>)}, followed by its
	 *  trailingText (if any) -- see {@link #trailingText}. */
	public void write(Printer p) throws IOException, IVisitor.VisitorException {
		p.writer().append("(" + commandName());
		writeArgs(p);
		p.writer().append(")");
		if (trailingText != null) p.writer().append(trailingText);
	}
	
	/** Creates a ParserException with the given message and position. */
	static public IParser.ParserException error(SMT.Configuration smt, String msg, IPos pos) {
		return new IParser.ParserException(msg, pos);
	}

}