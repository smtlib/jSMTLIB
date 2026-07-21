package org.smtlib.lsp;

import org.eclipse.lsp4j.Diagnostic;
import org.smtlib.ICommand;
import org.smtlib.ISource;

import java.util.List;

/**
 * Holds the result of parsing a single SMT-LIB 2 document.
 *
 * Immutable once constructed.
 */
public record ParsedDocument(
        String uri,
        String text,
        ISource source,
        List<ICommand> commands,
        List<Diagnostic> diagnostics
) {}
