/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;

import org.smtlib.ICommand.Iget_model;
import org.smtlib.IParser.ParserException;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.IVisitor;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** Implements the get-model command */
public class C_get_model extends Command implements Iget_model {
	/** Constructs a command instance */
	public C_get_model() {
	}
	
	/** Parses the command, producing a new command instance */
	static public /*@Nullable*/ C_get_model parse(Parser p) throws ParserException {
		return p.checkNoArg() ? new C_get_model() : null;
	}

	/** The command name */
	public static final String commandName = "get-model";
	/** The command name */
	@Override
	public String commandName() { return commandName; }
	
	@Override
	public IResponse execute(ISolver solver) {
		return solver.get_model();
	}

	@Override
	public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}
}
