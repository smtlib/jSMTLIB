/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;

import org.smtlib.ICommand.Ideclare_datatype;
import org.smtlib.IExpr.IDatatype;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IParser.ParserException;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.IVisitor;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** Implements the declare-sort command */
public class C_declare_datatype extends Command implements Ideclare_datatype {
	/** The command name */
	public static final String commandName = "declare-datatype";

	/** The new sort symbol */
	protected ISymbol sortSymbol;
	
	protected IDatatype datatype;
	
	/** The command name */
	@Override
	public String commandName() { return commandName; }

	/** The sort symbol declared by this command */
	@Override
	public ISymbol symbol() { return sortSymbol; }
	
	/** Constructs a new command object */
	public C_declare_datatype(ISymbol id, IDatatype d) {
		this.sortSymbol = id;
		// FIXME
	}
	
	/** Writes the command in the syntax of the given printer */
	public void write(Printer p) throws IOException, IVisitor.VisitorException {
		p.writer().append("(" + commandName + " ");
		sortSymbol.accept(p);
		p.writer().append(" ");
		datatype.accept(p);
		p.writer().append(")");
	}

	/** Parses the arguments of the command, producing a new command instance */
	static public /*@Nullable*/C_declare_datatype parse(Parser p) throws IOException, ParserException {
		/*@Nullable*/ISymbol id = p.parseSymbol();
		if (id == null) return null;
		/*@Nullable*/IDatatype datatype = p.parseDatatype();
		if (datatype == null) return null;
        if (!p.checkUserId(id)) return null;
		return new C_declare_datatype(id,datatype);
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
    public IDatatype datatype() {
        // TODO Auto-generated method stub
        return null;
    }
}
