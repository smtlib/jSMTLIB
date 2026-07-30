/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;

import org.smtlib.ICommand.Ideclare_sort_parameter;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IParser.ParserException;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.IVisitor;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** Implements the declare-sort-parameter command (a jSMTLIB extension to declare a sort parameter) */
public class C_declare_sort_parameter extends Command implements Ideclare_sort_parameter{
	/** The command name */
	public static final String commandName = "declare-sort-parameter";

	/** The new sort symbol */
	protected ISymbol sortSymbol;
	
	/** The command name */
	@Override
	public String commandName() { return commandName; }

	/** The sort symbol declared by this command */
	public ISymbol sortSymbol() { return sortSymbol; }
	
	/** Constructs a new command object */
	public C_declare_sort_parameter(ISymbol id) {
		this.sortSymbol = id;
	}
	
	/** Parses the arguments of the command, producing a new command instance */
	static public C_declare_sort_parameter parse(Parser p) throws IOException, ParserException {
		ISymbol id = p.parseSymbol();
		return new C_declare_sort_parameter(id);
	}

	@Override
	public IResponse execute(ISolver solver) {
		return solver.declare_sort_parameter(this);
	}

	@Override
	public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}
}
