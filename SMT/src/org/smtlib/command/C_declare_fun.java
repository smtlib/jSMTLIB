/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import org.smtlib.ICommand.Ideclare_fun;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IParser.ParserException;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.ISort;
import org.smtlib.ISort.IParameter;
import org.smtlib.IVisitor;
import org.smtlib.Utils;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** Implements the declare-fun command */
public class C_declare_fun extends Command implements Ideclare_fun {

	/** The command name */
	public static final String commandName = "declare-fun";

	/** The name of the function being declared */
	protected ISymbol fcnName;

	/** The sorts of the arguments of the function being declared */
	protected List<ISort> argSorts;

	/** The result sort of the function being declared */
	protected ISort resultSort;

	/** Any trailing attributes (see attributes()); null if none. */
	protected List<IAttribute<?>> attributes;

	/** The par-polymorphic parameters (see parameters()); null for an ordinary declaration. */
	protected List<IParameter> parameters;

	/** The command name */
	@Override
	public String commandName() { return commandName; }

	@Override
	public ISymbol symbol() { return fcnName; }

	@Override
	public List<ISort> argSorts() { return argSorts; }

	@Override
	public ISort resultSort() { return resultSort; }

	@Override
	public List<IAttribute<?>> attributes() { return attributes; }

	@Override
	public List<IParameter> parameters() { return parameters; }

	/** Constructs a command instance for an ordinary (non-attributed, non-par) declaration */
	public C_declare_fun(ISymbol symbol, List<ISort> argSorts, ISort resultSort) {
		this(symbol, argSorts, resultSort, null);
	}

	/** Constructs a command instance for an ordinary declaration, including any trailing
	 * attributes (see attributes()). */
	public C_declare_fun(ISymbol symbol, List<ISort> argSorts, ISort resultSort, List<IAttribute<?>> attributes) {
		this(symbol, argSorts, resultSort, attributes, null);
	}

	/** Constructs a command instance from all of its components, including the
	 * par-polymorphic parameters (see parameters()) for the "(declare-fun par ...)" form. */
	public C_declare_fun(ISymbol symbol, List<ISort> argSorts, ISort resultSort, List<IAttribute<?>> attributes, List<IParameter> parameters) {
		this.fcnName = symbol;
		this.argSorts = argSorts;
		this.resultSort = resultSort;
		this.attributes = attributes;
		this.parameters = parameters;
	}

	/** Parses the arguments of the command, producing a new command instance.
	 *
	 * Two non-standard extensions, both parsed unconditionally (whether either is actually
	 * accepted, rather than rejected with a specific message, is decided at type-checking
	 * time in Solver_test.declare_fun() -- see there):
	 *
	 * - A trailing attribute* after the result sort (e.g. :left-assoc), the same production a
	 *   theory's own fun_symbol_decl can carry, so a user-declared function can opt into the
	 *   same n-ary sugar handling SymbolTable.lookup() already applies to theory-declared
	 *   ones. Standard SMT-LIB declare-fun has no such production.
	 *
	 * - "(declare-fun par (param+) (name sort+ attribute*))": a par-polymorphic declaration,
	 *   detected by the literal reserved word "par" appearing where the function's own symbol
	 *   normally goes (the same technique parseDatatype() already uses to detect datatype's
	 *   own optional par form). The nested (name sort+ attribute*) is exactly the
	 *   par_fun_symbol_decl shape a theory's own :funs entry uses (e.g. Core.smt2's
	 *   (par (A) (= A A Bool :chainable))) -- reusing that shape verbatim, under the familiar
	 *   declare-fun command name, rather than inventing a different, unrelated syntax or a
	 *   wholly new top-level command name. SMT-LIB's declare-fun has no par form at all
	 *   (par otherwise only appears in declare-datatype's own constructor lists). */
	static public C_declare_fun parse(Parser p) throws ParserException {
		ISymbol tok = p.parseSymbolOrReservedWord("Expected a function symbol or 'par' here, not a #");
		if (Utils.PAR.equals(tok.value())) {
			List<IParameter> parameters = p.parseList(
					() -> p.smt().sortFactory.createSortParameter(p.parseSymbol()), "parameter", true);
			p.parseLP();
			ISymbol name = p.parseSymbol();
			List<ISort> sorts = new LinkedList<ISort>();
			while (!p.isRP() && !(p.peekToken() instanceof IKeyword)) {
				sorts.add(p.parseSort(parameters));
			}
			if (sorts.isEmpty()) {
				throw new ParserException("Expected at least a result sort", name.pos());
			}
			ISort result = sorts.remove(sorts.size()-1);
			List<IAttribute<?>> attrs = null;
			if (!p.isRP()) {
				attrs = p.parseAttributeSequence();
			}
			p.parseRP();
			return new C_declare_fun(name, sorts, result, attrs, parameters);
		}
		List<ISort> argSorts = p.parseList(() -> p.parseSort(null), "sort", true);
		ISort result = p.parseSort(null);
		List<IAttribute<?>> attrs = null;
		if (!p.isRP()) {
			attrs = p.parseAttributeSequence();
		}
		return new C_declare_fun(tok, argSorts, result, attrs);
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
