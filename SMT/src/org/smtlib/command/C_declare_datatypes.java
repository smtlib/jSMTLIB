/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;
import java.util.List;
import java.util.LinkedList;

import org.smtlib.ICommand.Ideclare_datatypes;
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
public class C_declare_datatypes extends Command implements Ideclare_datatypes {
	/** The command name */
	public static final String commandName = "declare-datatypes";

	/** The new sort symbol */
	protected List<ISymbol> sortSymbols;
	
	protected List<IDatatype> datatypes;
	
	/** The command name */
	@Override
	public String commandName() { return commandName; }

	/** The sort symbol declared by this command */
	@Override
	public List<ISymbol> symbols() { return sortSymbols; }
	
	/** Constructs a new command object */
	public C_declare_datatypes(List<ISymbol> ids, List<IDatatype> datatypes) {
		this.sortSymbols = ids;
		this.datatypes = datatypes;
	}
	
	@Override
	public void writeArgs(Printer p) throws IOException, IVisitor.VisitorException {
//FIXME		sortSymbols.accept(p);
		p.writer().append(" ");
//FIXME		datatypes.accept(p);
		// FIXME
	}

	/** Parses the arguments of the command, producing a new command instance */
	static public C_declare_datatypes parse(Parser p) throws IOException, ParserException {
	    List<ISymbol> ids = new LinkedList<ISymbol>();
		ISymbol id = p.parseSymbol();
		List<IDatatype> datatypes = new LinkedList<IDatatype>();
		p.checkUserId(id);
		return new C_declare_datatypes(ids,datatypes);
	}

	@Override
	public IResponse execute(ISolver solver) {
		return solver.declare_datatypes(this);
	}

	@Override
	public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}

    @Override
    public List<IDatatype> datatypes() {
        // TODO Auto-generated method stub
        return null;
    }
}
