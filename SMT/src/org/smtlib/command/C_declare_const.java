/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import org.smtlib.ICommand.Ideclare_const;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IParser.ParserException;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.ISort;
import org.smtlib.IVisitor;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** Implements the declare-fun command */
public class C_declare_const extends C_declare_fun implements Ideclare_const {
	
	/** The command name */
	public static final String commandName = "declare-const";

	/** The command name */
	@Override
	public String commandName() { return commandName; }
	
	static final private List<ISort> emptyList = new LinkedList<ISort>();
	
	/** Constructs a command instance from its components */
	public C_declare_const(ISymbol symbol, ISort resultSort) {
		super(symbol, emptyList, resultSort);
	}

	@Override
	public void writeArgs(Printer p) throws IOException, IVisitor.VisitorException {
		p.writer().append(" ");
		symbol().accept(p);
		p.writer().append(" ");
		resultSort().accept(p);
	}

	/** Parses the arguments of the command, producing a new command instance */
	static public /*@Nullable*/ C_declare_const parse(Parser p) throws ParserException {
		/*@Nullable*/ ISymbol symbol = p.parseSymbol();
		if (symbol == null) return null;

		/*@Nullable*/ ISort result = p.parseSort(null);
		if (result == null) return null;
        if (!p.checkUserId(symbol)) return null;
		return new C_declare_const(symbol,result);
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
