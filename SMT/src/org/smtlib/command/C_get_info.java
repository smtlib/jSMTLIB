/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;

import org.smtlib.ICommand.Iget_info;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IParser.ParserException;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.IVisitor;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** This class implements the get-info command */
public class C_get_info extends Command implements Iget_info {
	/** The command name */
	public static final String commandName = "get-info";
	/** The command name */
	@Override
	public String commandName() { return commandName; }

	/** The keyword for the info item to fetch */
	protected IKeyword option;

	/** The keyword for the info item to fetch */
	@Override
	public IKeyword infoflag() { return option; }

	/** Constructs a command instance given the keyword */
	public C_get_info(IKeyword infoflag) { 
		this.option = infoflag;
	}
	
	/** Creates a command instance by parsing the concrete S-expression syntax */
	static public C_get_info parse(Parser p) throws ParserException {
		IKeyword key = p.parseKeyword();
		return new C_get_info(key);
	}
	
	@Override
	public void writeArgs(Printer p) throws IOException, IVisitor.VisitorException {
		p.writer().append(" ");
		option.accept(p);
	}
	
	@Override
	public IResponse execute(ISolver solver) {
		if (prefixText != null) solver.comment(prefixText);
		return solver.get_info(option);
	}

	@Override
	public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}
}
