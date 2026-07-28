/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;
import java.util.List;

import org.smtlib.ICommand.Ideclare_fun;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IParser.ParserException;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.ISort;
import org.smtlib.IVisitor;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** Implements the declare-fun command */
public class C_declare_fun extends Command implements Ideclare_fun {
	
	/** The command name */
	public static final String commandName = "declare-fun";

	/** The name of the function being declared */
	protected ISymbol fcnName;

	/** The sorts of the arguments of the function being declared */
	protected List<ISort> argSorts;

	/** The result sort of the function being declared */
	protected ISort resultSort;
	
	/** The command name */
	@Override
	public String commandName() { return commandName; }
	
	@Override
	public ISymbol symbol() { return fcnName; }
	
	@Override
	public List<ISort> argSorts() { return argSorts; }
	
	@Override
	public ISort resultSort() { return resultSort; }
	
	/** Constructs a command instance from its components */
	public C_declare_fun(ISymbol symbol, List<ISort> argSorts, ISort resultSort) {
		this.fcnName = symbol;
		this.argSorts = argSorts;
		this.resultSort = resultSort;
	}

	/** Parses the arguments of the command, producing a new command instance */
	static public C_declare_fun parse(Parser p) throws ParserException {
		ISymbol symbol = p.parseSymbol();
		List<ISort> argSorts = p.parseList(() -> p.parseSort(null), "sort", true);
		ISort result = p.parseSort(null);
		return new C_declare_fun(symbol,argSorts,result);
	}

	@Override
	public IResponse execute(ISolver solver) {
		return solver.declare_fun(this);
	}

	@Override
	public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}
}
