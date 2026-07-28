/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;
import java.util.Collections;

import org.smtlib.ICommand.Idefine_const;
import org.smtlib.IExpr;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IParser.ParserException;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.ISort;
import org.smtlib.IVisitor;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** Implements the define-const command: syntactic sugar for define-fun with no parameters */
public class C_define_const extends C_define_fun implements Idefine_const {

	/** The command name */
	public static final String commandName = "define-const";

	/** The command name */
	@Override
	public String commandName() { return commandName; }

	/** Constructs a command instance */
	public C_define_const(ISymbol symbol, ISort resultSort, IExpr expression) {
		super(symbol, Collections.emptyList(), resultSort, expression);
	}

	@Override
	public void writeArgs(Printer p) throws IOException, IVisitor.VisitorException {
		p.writer().append(" ");
		symbol().accept(p);
		p.writer().append(" ");
		resultSort().accept(p);
		p.writer().append(" ");
		expression().accept(p);
	}

	/** Parses the arguments of the command, producing a new command instance */
	static public C_define_const parse(Parser p) throws ParserException {
		ISymbol symbol = p.parseSymbol();
		ISort resultSort = p.parseSort(null);
		IExpr expr = p.parseExpr();
		p.checkUserId(symbol);
		return new C_define_const(symbol, resultSort, expr);
	}

	@Override
	public IResponse execute(ISolver solver) {
		return solver.define_fun(this);
	}

	@Override
	public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}
}
