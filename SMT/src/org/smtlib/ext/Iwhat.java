package org.smtlib.ext;

import java.util.List;

import org.smtlib.ICommand;
import org.smtlib.IExpr.IIdentifier;

/** Interface for the SMT-LIB {@code what} command (non-standard extension). */
public interface Iwhat extends ICommand {
	/** Returns the identifiers to look up and describe. */
	List<IIdentifier> ids();
}