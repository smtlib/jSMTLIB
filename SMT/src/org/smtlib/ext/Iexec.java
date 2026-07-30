package org.smtlib.ext;

import org.smtlib.ICommand;

/** Interface for the SMT-LIB {@code exec} command (non-standard extension). */
public interface Iexec extends ICommand {
	/** Returns the script to execute. */
	IScript script();
}