/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;
import java.util.List;

import org.smtlib.ICommand.Idefine_fun_rec;
import org.smtlib.*;
import org.smtlib.IExpr.IDeclaration;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IParser.ParserException;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** Implements the define-fun command */
public class C_define_fun_rec extends Command implements Idefine_fun_rec {
	/** The command name */
	public static final String commandName = "define-fun-rec";
	/** The command name */
	@Override
	public String commandName() { return commandName; }
	
	/** The name of the function being defined */
	protected ISymbol fcnName;
	/** The sorts of the arguments of the function being defined */
	protected List<IDeclaration> args;
	/** The sort of the result */
	protected ISort resultSort;
	/** The defining expression for the function */
	protected IExpr expression;
	
	/** The name of the function being defined */
	@Override
	public ISymbol symbol() { return fcnName; }
	/** The sorts of the arguments of the function being defined */
	@Override
	public List<IDeclaration> parameters() { return args; };
	/** The result sort */
	@Override
	public ISort resultSort() { return resultSort; }
	/** The defining expression for the function */
	@Override
	public IExpr expression() { return expression; }
	
	// FIXME - typechecking needs to check that the resultSort matches the expression's sort
	
	/** Constructs a command instance */
	public C_define_fun_rec(ISymbol id, List<IDeclaration> declarations, ISort resultSort, IExpr expr) {
		this.fcnName = id;
		this.args = declarations;
		this.resultSort = resultSort;
		this.expression = expr;
	}
	
	@Override
	public void writeArgs(Printer p) throws IOException, IVisitor.VisitorException {
		p.writer().append(" ");
		symbol().accept(p);
		p.writer().append(" (");
		for (IDeclaration d: parameters()) {
			d.accept(p);
		}
		p.writer().append(") ");
		resultSort().accept(p);
		p.writer().append(" ");
		expression().accept(p);
	}
	
	/** Parses the command arguments and creates a command instance */
	static public C_define_fun_rec parse(Parser p) throws ParserException {
		ISymbol name = p.parseSymbol();
		List<IDeclaration> list = p.parseList(p::parseDeclaration, "declaration", true);
		ISort resultSort = p.parseSort(null);
		IExpr expr = p.parseExpr();
		return new C_define_fun_rec(name,list,resultSort,expr);
	}

	@Override
	public IResponse execute(ISolver solver) {
		return solver.define_fun_rec(this);
	}

	@Override
	public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}
}
