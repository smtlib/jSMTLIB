/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;
import java.util.List;

import org.smtlib.ICommand.Idefine_funs_rec;
import org.smtlib.*;
import org.smtlib.IExpr.IFunctionDeclaration;
import org.smtlib.IParser.ParserException;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** Implements the define-funs-rec command */
public class C_define_funs_rec extends Command implements Idefine_funs_rec {
	/** The command name */
	public static final String commandName = "define-funs-rec";
	/** The command name */
	@Override
	public String commandName() { return commandName; }

	/** The list of function declarations (name, parameters, result sort) */
	protected List<IFunctionDeclaration> declarations;
	/** The list of defining bodies, one per declaration */
	protected List<IExpr> bodies;

	@Override
	public List<IFunctionDeclaration> declarations() { return declarations; }
	@Override
	public List<IExpr> bodies() { return bodies; }

	/** Constructs a command instance */
	public C_define_funs_rec(List<IFunctionDeclaration> declarations, List<IExpr> bodies) {
		this.declarations = declarations;
		this.bodies = bodies;
	}

	@Override
	public void writeArgs(Printer p) throws IOException, IVisitor.VisitorException {
		p.writer().append(" (");
		for (IFunctionDeclaration d : declarations()) { d.accept(p); p.writer().append(" "); }
		p.writer().append(") (");
		for (IExpr body : bodies()) { body.accept(p); p.writer().append(" "); }
		p.writer().append(")");
	}

	/** Parses the command arguments and creates a command instance */
	static public C_define_funs_rec parse(Parser p) throws ParserException {
		List<IFunctionDeclaration> decls = p.parseList(p::parseFunctionDeclaration, "function declaration", false);
		List<IExpr> bodies = p.parseList(p::parseExpr, "term", false);
		if (decls.size() != bodies.size())
			throw new ParserException("The number of function declarations (" + decls.size() +
					") must equal the number of bodies (" + bodies.size() + ")", null);
		return new C_define_funs_rec(decls, bodies);
	}

	@Override
	public IResponse execute(ISolver solver) {
		return solver.define_funs_rec(this);
	}

	@Override
	public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}
}
