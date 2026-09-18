/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;

import org.smtlib.ICommand;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.IVisitor;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Printer;

/** A synthetic pseudo-command representing a comment that appeared immediately before a real
 *  command in a script -- not part of the SMT-LIB command grammar itself (like {@link
 *  org.smtlib.ext.C_exec}/{@link org.smtlib.ext.C_what}, it just implements {@link ICommand}
 *  directly and relies on {@link IVisitor}'s generic {@code visit(ICommand)} fallback).
 *  <p>
 *  Exists so a script's comments are carried as part of its command sequence -- consistent
 *  with how a script is modeled ({@code List<ICommand>}) -- rather than as metadata bolted
 *  onto the next real command. Every real command-dispatch path already just calls {@code
 *  command.execute(solver)} on whatever the parser hands it, so this forwards itself to any
 *  solver uniformly, with no per-command-class or per-dispatch-loop code needed. See issue
 *  #42. */
public class C_comment extends Command implements ICommand {

	public static final String commandName = "<comment>";

	protected final String text;

	public C_comment(String text) {
		this.text = text;
	}

	@Override
	public String commandName() { return commandName; }

	/** Prints the comment text -- not the "(commandName args)" shape the base class's default
	 *  write() produces, since a comment was never S-expression syntax to begin with. Text
	 *  parsed from a real script is always already well-formed this way (every line,
	 *  including a multi-line block's continuation lines, already carries its own leading
	 *  {@code ;} in the source, so it prints back out verbatim, byte for byte) -- but text
	 *  supplied directly via the public constructor might have an embedded newline with no
	 *  {@code ;} on the continuation line, which would silently end the comment there and let
	 *  the continuation be re-parsed as code. So each line is checked, and given its own
	 *  {@code ;} if it doesn't already have one and isn't just blank. A comment parsed
	 *  immediately before a real command always already ends with a newline in the captured
	 *  source text (a {@code ;} comment can't share a line with whatever follows it, so
	 *  there's necessarily at least one newline swept into the capture) -- but a trailing
	 *  comment at true end-of-file, or text supplied directly via the public constructor,
	 *  might not. Printing without a final newline would risk whatever gets printed right
	 *  after landing on the same line and being silently swallowed by this comment (since
	 *  {@code ;} consumes to end of line), so one is always guaranteed here regardless. */
	@Override
	public void write(Printer p) throws IOException {
		String[] lines = text.split("\r\n|\n", -1);
		for (int i = 0; i < lines.length; i++) {
			if (i > 0) p.writer().append("\n");
			String line = lines[i];
			String trimmed = line.trim();
			if (!trimmed.isEmpty() && !trimmed.startsWith(";")) p.writer().append(";");
			p.writer().append(line);
		}
		if (!text.endsWith("\n")) p.writer().append("\n");
	}

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
