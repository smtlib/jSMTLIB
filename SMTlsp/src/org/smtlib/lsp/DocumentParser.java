package org.smtlib.lsp;

import org.eclipse.lsp4j.Diagnostic;
import org.eclipse.lsp4j.DiagnosticSeverity;
import org.eclipse.lsp4j.Range;
import org.smtlib.CharSequenceReader;
import org.smtlib.ICommand;
import org.smtlib.IParser;
import org.smtlib.IPos;
import org.smtlib.IResponse;
import org.smtlib.ISource;
import org.smtlib.Log;
import org.smtlib.SMT;

import java.io.StringReader;
import java.util.ArrayList;
import java.util.List;

/**
 * Parses an SMT-LIB 2 document string into a {@link ParsedDocument}.
 *
 * A fresh {@link SMT} configuration is used per parse so that there is no
 * cross-document state leakage.  Parse errors are captured via a
 * {@link Log.IListener} and converted to LSP diagnostics.
 */
public class DocumentParser {

    private DocumentParser() {}

    public static ParsedDocument parse(String uri, String text) {
        SMT smt = new SMT();
        SMT.Configuration smtConfig = smt.smtConfig;

        // Suppress all default output from the Log — we capture errors ourselves.
        smtConfig.log.clearListeners();

        var diagnostics = new ArrayList<Diagnostic>();

        smtConfig.log.addListener(new Log.IListener() {
            @Override public void logOut(String msg) {}
            @Override public void logOut(IResponse result) {}
            @Override public void logDiag(String msg) {}
            @Override public void indent(String chars) {}

            @Override
            public void logError(String msg) {
                diagnostics.add(new Diagnostic(
                        new Range(new org.eclipse.lsp4j.Position(0, 0),
                                  new org.eclipse.lsp4j.Position(0, 0)),
                        msg,
                        DiagnosticSeverity.Error,
                        "smtlib"));
            }

            @Override
            public void logError(IResponse.IError result) {
                IPos pos = result.pos();
                Range range = (pos != null)
                        ? PositionUtils.toRange(pos)
                        : new Range(new org.eclipse.lsp4j.Position(0, 0),
                                    new org.eclipse.lsp4j.Position(0, 0));
                diagnostics.add(new Diagnostic(range, result.errorMsg(),
                        DiagnosticSeverity.Error, "smtlib"));
            }
        });

        ISource source;
        try {
            source = smtConfig.smtFactory.createSource(
                    new CharSequenceReader(new StringReader(text)), null);
        } catch (Exception e) {
            ServerLog.serverLog("Failed to create source for " + uri + ": " + e);
            return new ParsedDocument(uri, text, null, List.of(), diagnostics);
        }

        var commands = new ArrayList<ICommand>();

        try {
            IParser parser = smtConfig.smtFactory.createParser(smtConfig, source);
            while (!parser.isEOD()) {
                ICommand cmd = parser.parseCommand();
                if (cmd != null) {
                    commands.add(cmd);
                }
            }
        } catch (IParser.ParserException e) {
            // Fatal parser error — remaining commands cannot be parsed.
            IPos pos = e.pos();
            Range range = (pos != null)
                    ? PositionUtils.toRange(pos)
                    : new Range(new org.eclipse.lsp4j.Position(0, 0),
                                new org.eclipse.lsp4j.Position(0, 0));
            diagnostics.add(new Diagnostic(range,
                    e.getMessage() != null ? e.getMessage() : "Parser error",
                    DiagnosticSeverity.Error,
                    "smtlib"));
        } catch (Exception e) {
            ServerLog.serverLog("Unexpected parse error for " + uri + ": " + e);
        }

        return new ParsedDocument(uri, text, source, List.copyOf(commands), List.copyOf(diagnostics));
    }
}
