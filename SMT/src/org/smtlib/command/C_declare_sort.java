/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;

import org.smtlib.ICommand.Ideclare_sort;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IParser.ParserException;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.IVisitor;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** Implements the declare-sort command */
public class C_declare_sort extends Command implements Ideclare_sort {
	/** The command name */
	public static final String commandName = "declare-sort";

	/** The new sort symbol */
	protected ISymbol sortSymbol;
	
	/** The arity of the sort symbol */
	protected INumeral arity;
	
	/** The command name */
	@Override
	public String commandName() { return commandName; }

	/** The arity of the sort symbol */
	@Override
	public INumeral arity() { return arity; }
	
	/** The sort symbol declared by this command */
	@Override
	public ISymbol sortSymbol() { return sortSymbol; }
	
	/** Constructs a new command object */
	public C_declare_sort(ISymbol id, INumeral n) {
		this.sortSymbol = id;
		this.arity = n;
	}
	
	@Override
	public void writeArgs(Printer p) throws IOException, IVisitor.VisitorException {
		p.writer().append(" ");
		sortSymbol().accept(p);
		p.writer().append(" ");
		arity().accept(p);
	}

	/** Parses the arguments of the command, producing a new command instance */
	static public C_declare_sort parse(Parser p) throws IOException, ParserException {
		ISymbol id = p.parseSymbol();
		INumeral numeral = p.parseNumeral();
		p.checkUserId(id);
		return new C_declare_sort(id,numeral);
	}

	@Override
	public IResponse execute(ISolver solver) {
		return solver.declare_sort(this);
	}

	@Override
	public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}
}
