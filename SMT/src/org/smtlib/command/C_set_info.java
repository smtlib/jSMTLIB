/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;

import org.smtlib.ICommand.Iset_info;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IParser.ParserException;
import org.smtlib.*;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** Implements the set-info command */
public class C_set_info extends Command implements Iset_info {
	/** The command name */
	public static final String commandName = "set-info";
	/** The command name */
	@Override
	public String commandName() { return commandName; }

	/** The keyword info flag */
	protected IKeyword infoflag;

	/** The value of the info flag */
	protected /*@Nullable*/IAttributeValue value;

	@Override
	public IKeyword infoflag() { return infoflag; }

	@Override
	public IAttributeValue value() { return value; }

	/** Construct an instance of the command */
	public C_set_info(IKeyword keyword, IAttributeValue value) {
		super();
		this.infoflag = keyword;
		this.value = value;
	}
	
	/** Creates a command instance by parsing the concrete S-expression syntax */
	static public C_set_info parse(Parser p) throws ParserException  {
		IKeyword key = p.parseKeyword();
		IAttributeValue value = p.parseAttributeValue();
		return new C_set_info(key,value);
	}

	@Override
	public IResponse execute(ISolver solver) {
		if (prefixText != null) solver.comment(prefixText);
		return solver.set_info(infoflag,value);
	}

	@Override
	public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}
}
