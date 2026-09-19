/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.util.List;

import org.smtlib.ICommand.Idefine_fun_rec;
import org.smtlib.IExpr;
import org.smtlib.IExpr.IDeclaration;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IParser.ParserException;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.ISort;
import org.smtlib.IVisitor;
import org.smtlib.sexpr.Parser;

/** Implements the define-fun-rec command (recursive function definition); syntactically
 *  identical to define-fun (see {@link C_define_fun}), differing only in the dispatch
 *  target -- shares that class's fields, accessors, and constructor. */
public class C_define_fun_rec extends C_define_fun implements Idefine_fun_rec {
	/** The command name */
	public static final String commandName = "define-fun-rec";
	/** The command name */
	@Override
	public String commandName() { return commandName; }

	// TypeChecker.checkFcnRec() already checks the body's sort against resultSort -- called
	// from Solver_test.define_fun_rec()/Solver_simplify's override, not centralized in
	// TypeChecker.validate() (the universal pre-dispatch pass every solver adapter goes
	// through). That's deliberate: real solver adapters intentionally don't duplicate a
	// semantic check the real solver already performs and reports itself (see #46/#53),
	// so this check staying test/simplify-only, rather than moving into validate(), matches
	// that pattern instead of being a gap. See issue #40.

	/** Constructs a command instance */
	public C_define_fun_rec(ISymbol id, List<IDeclaration> declarations, ISort resultSort, IExpr expr) {
		super(id, declarations, resultSort, expr);
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
		return v.visit((Idefine_fun_rec)this);
	}
}
