package org.smtlib.lsp;

import org.eclipse.lsp4j.DidChangeConfigurationParams;
import org.eclipse.lsp4j.DidChangeWatchedFilesParams;
import org.eclipse.lsp4j.ExecuteCommandParams;
import org.eclipse.lsp4j.SymbolInformation;
import org.eclipse.lsp4j.WorkspaceSymbolParams;
import org.eclipse.lsp4j.jsonrpc.messages.Either;
import org.eclipse.lsp4j.services.WorkspaceService;

import java.util.List;
import java.util.concurrent.CompletableFuture;

/**
 * Minimal workspace service for the SMT-LIB LSP server.
 *
 * Handles configuration changes and watched-file notifications (reparse on change).
 */
public class SMTWorkspaceService implements WorkspaceService {

    private final SMTTextDocumentService textDocumentService;

    public SMTWorkspaceService(SMTTextDocumentService textDocumentService) {
        this.textDocumentService = textDocumentService;
    }

    @Override
    public void didChangeConfiguration(DidChangeConfigurationParams params) {
        ServerLog.serverLog("[workspace/didChangeConfiguration]");
    }

    @Override
    public void didChangeWatchedFiles(DidChangeWatchedFilesParams params) {
        ServerLog.serverLog("[workspace/didChangeWatchedFiles]");
        for (var event : params.getChanges()) {
            String uri = event.getUri();
            if (uri != null && (uri.endsWith(".smt2") || uri.endsWith(".smt"))) {
                textDocumentService.reparseFromDisk(uri);
            }
        }
    }

    @Override
    public CompletableFuture<Either<List<? extends SymbolInformation>, List<? extends org.eclipse.lsp4j.WorkspaceSymbol>>>
            symbol(WorkspaceSymbolParams params) {
        String query = params.getQuery() != null ? params.getQuery().toLowerCase() : "";
        var results = textDocumentService.workspaceSymbols(query);
        return CompletableFuture.completedFuture(Either.forRight(results));
    }

    @Override
    public CompletableFuture<Object> executeCommand(ExecuteCommandParams params) {
        ServerLog.serverLog("[workspace/executeCommand] command=" + params.getCommand());
        return CompletableFuture.completedFuture(null);
    }
}
