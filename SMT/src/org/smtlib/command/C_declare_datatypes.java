/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import org.smtlib.ICommand.Ideclare_datatypes;
import org.smtlib.IExpr.IDatatype;
import org.smtlib.IExpr.ISortDeclaration;
import org.smtlib.IParser.ParserException;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.IVisitor;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** Implements the declare-datatypes command */
public class C_declare_datatypes extends Command implements Ideclare_datatypes {
	/** The command name */
	public static final String commandName = "declare-datatypes";

	@Override
	public String commandName() { return commandName; }

	/** The sort declarations: (symbol arity) pairs */
	protected List<ISortDeclaration> sortDeclarations;
	/** The datatype declarations, parallel to sortDeclarations */
	protected List<IDatatype> datatypes;

	@Override
	public List<ISortDeclaration> sortDeclarations() { return sortDeclarations; }
	@Override
	public List<IDatatype> datatypes() { return datatypes; }

	/** Constructs a new command object */
	public C_declare_datatypes(List<ISortDeclaration> sortDeclarations, List<IDatatype> datatypes) {
		this.sortDeclarations = sortDeclarations;
		this.datatypes = datatypes;
	}

	@Override
	public void writeArgs(Printer p) throws IOException, IVisitor.VisitorException {
		p.writer().append(" (");
		for (ISortDeclaration sd : sortDeclarations()) {
			p.writer().append(" ");
			sd.accept(p);
		}
		p.writer().append(") (");
		for (IDatatype dt : datatypes()) {
			p.writer().append(" ");
			dt.accept(p);
		}
		p.writer().append(")");
	}

	/** Parses the arguments: ( (symbol numeral)+ ) ( datatype_dec+ ) */
	static public C_declare_datatypes parse(Parser p) throws ParserException {
		List<ISortDeclaration> sortDecls = new LinkedList<>();
		p.parseLP();
		while (!p.isRP() && !p.isEOD()) {
			p.parseLP();
			var sym = p.parseSymbol();
			var arity = p.parseNumeral();
			p.parseRP();
			sortDecls.add(p.smt().exprFactory.sortDeclaration(sym, arity));
		}
		p.parseRP();
		if (sortDecls.isEmpty())
			throw new ParserException("Expected at least one sort declaration in declare-datatypes", null);

		List<IDatatype> datatypes = p.parseList(p::parseDatatype, "datatype declaration", false);

		if (sortDecls.size() != datatypes.size())
			throw new ParserException("Number of sort declarations (" + sortDecls.size() +
					") does not match number of datatype declarations (" + datatypes.size() + ")", null);

		for (ISortDeclaration sd : sortDecls) p.checkUserId(sd.symbol());
		return new C_declare_datatypes(sortDecls, datatypes);
	}

	@Override
	public IResponse execute(ISolver solver) {
		return solver.declare_datatypes(this);
	}

	@Override
	public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}
}
