/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;

import org.smtlib.ICommand.Ideclare_datatype;
import org.smtlib.IExpr.IDatatype;
import org.smtlib.IExpr.ISortDeclaration;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IParser.ParserException;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.IVisitor;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** Implements the declare-datatype command */
public class C_declare_datatype extends Command implements Ideclare_datatype {
	/** The command name */
	public static final String commandName = "declare-datatype";

	/** The sort declaration (symbol + arity derived from datatype body) */
	protected ISortDeclaration sortDeclaration;

	protected IDatatype datatype;

	/** The command name */
	@Override
	public String commandName() { return commandName; }

	@Override
	public ISortDeclaration sortDeclaration() { return sortDeclaration; }

	/** Constructs a new command object */
	public C_declare_datatype(ISortDeclaration sortDeclaration, IDatatype d) {
		this.sortDeclaration = sortDeclaration;
		this.datatype = d;
	}

	/** Parses the arguments of the command, producing a new command instance */
	static public C_declare_datatype parse(Parser p) throws IOException, ParserException {
		ISymbol id = p.parseSymbol();
		IDatatype datatype = p.parseDatatype();
		int arityVal = datatype.symbols() == null ? 0 : datatype.symbols().size();
		ISortDeclaration sortDecl = p.smt().exprFactory.sortDeclaration(id, p.smt().exprFactory.numeral(arityVal));
		return new C_declare_datatype(sortDecl, datatype);
	}

	@Override
	public IResponse execute(ISolver solver) {
		return solver.declare_datatype(this);
	}

	@Override
	public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}

    @Override
    public IDatatype datatype() { return datatype; }
}
