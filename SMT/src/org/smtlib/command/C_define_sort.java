/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;
import java.util.List;

import org.smtlib.ICommand.Idefine_sort;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IParser.ParserException;
import org.smtlib.*;
import org.smtlib.ISort.IParameter;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** Implements the define-sort command */
public class C_define_sort extends Command implements Idefine_sort {
	/** The command name */
	public static final String commandName = "define-sort";
	/** The command name */
	@Override
	public String commandName() { return commandName; }
	
	/** The name of the sort being defined */
	protected ISymbol sortName;
	/** The sort parameters of the sort being defined. */
	protected List<IParameter> args;
	/** The defining expression for the function */
	protected ISort expression;
	
	/** Returns the name of the sort being defined. */
	@Override
	public ISymbol sortSymbol() { return sortName; }
	/** Returns the sort parameters of the sort being defined. */
	@Override
	public List<IParameter> parameters() { return args; };
	/** The defining expression for the function */
	@Override
	public ISort expression() { return expression; }
	
	/** Constructs a command instance */
	public C_define_sort(ISymbol id, List<IParameter> parameters, ISort expr) {
		this.sortName = id;
		this.args = parameters;
		this.expression = expr;
	}
	
	/** Parses the command arguments and creates a command instance */
	static public C_define_sort parse(Parser p) throws ParserException {
		ISymbol name = p.parseSymbol();
		List<IParameter> list = p.parseList(
				() -> p.smt().sortFactory.createSortParameter(p.parseSymbol()), "parameter", true);
		ISort expr = p.parseSort(list);
		return new C_define_sort(name,list,expr);
	}

	@Override
	public IResponse execute(ISolver solver) {
		return solver.define_sort(this);
	}

	@Override
	public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}
	
	
}
