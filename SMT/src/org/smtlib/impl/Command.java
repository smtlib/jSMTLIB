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

	public /*@Nullable*//*@ReadOnly*/ String prefixText;

	/** The command name */
	abstract public String commandName();

	/** Writes the command arguments (everything between the opening parenthesis +
	 *  command name and the closing parenthesis); called by {@link #write}.
	 *  Extension commands override this; standard commands are printed via the visitor. */
	public void writeArgs(Printer p) throws IOException, IVisitor.VisitorException {}

	/** Writes the full command: {@code (commandName() <writeArgs output>)}. */
	public void write(Printer p) throws IOException, IVisitor.VisitorException {
		p.writer().append("(" + commandName());
		writeArgs(p);
		p.writer().append(")");
	}
	
	/** Creates a ParserException with the given message and position. */
	static public IParser.ParserException error(SMT.Configuration smt, String msg, IPos pos) {
		return new IParser.ParserException(msg, pos);
	}

}