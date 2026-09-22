/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import org.smtlib.ICommand;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.IVisitor;
import org.smtlib.impl.Command;

/** A synthetic pseudo-command representing a comment that appeared immediately before a real
 *  command in a script -- not part of the SMT-LIB command grammar itself, but modeled as a
 *  real, typed {@link ICommand.Icomment} (see issue #115) rather than a generic {@link
 *  ICommand}, so execution, typed-visitor traversal, and printing all dispatch to it the same
 *  way every other command does, with no reflection-based or generic-fallback special case.
 *  <p>
 *  Exists so a script's comments are carried as part of its command sequence -- consistent
 *  with how a script is modeled ({@code List<ICommand>}) -- rather than as metadata bolted
 *  onto the next real command. Every real command-dispatch path already just calls {@code
 *  command.execute(solver)} on whatever the parser hands it, so this forwards itself to any
 *  solver uniformly, with no per-command-class or per-dispatch-loop code needed. See issue
 *  #42. */
public class C_comment extends Command implements ICommand.Icomment {

	public static final String commandName = "<comment>";

	protected final String text;

	public C_comment(String text) {
		this.text = text;
	}

	@Override
	public String commandName() { return commandName; }

	@Override
	public String text() { return text; }

	// Printing (write()) used to be overridden here, invoked only via the generic
	// visit(ICommand) fallback's reflection-based write() lookup -- moved into
	// sexpr/Printer.visit(ICommand.Icomment) instead, now that Comment is a real, typed
	// command (see issue #115), so printing logic for every command, including this one,
	// lives in exactly one place: Printer's own typed visit() methods.

	@Override
	public IResponse execute(ISolver solver) {
		solver.comment(text);
		return solver.smt().responseFactory.empty();
	}

	@Override
	public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}
}
