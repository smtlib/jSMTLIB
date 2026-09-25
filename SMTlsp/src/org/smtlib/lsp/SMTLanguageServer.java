package org.smtlib.lsp;

import org.eclipse.lsp4j.*;
import org.eclipse.lsp4j.services.*;

import java.util.concurrent.CompletableFuture;

/**
 * Top-level LSP server for SMT-LIB 2 files.
 *
 * Capabilities:
 * <ul>
 *   <li>textDocumentSync: Full — client sends the entire document on every change</li>
 *   <li>documentSymbol: declarations visible in the Outline panel</li>
 *   <li>workspaceSymbol: cross-file declaration search</li>
 *   <li>hover: prints the SMT-LIB command under the cursor</li>
 * </ul>
 */
public class SMTLanguageServer implements LanguageServer, LanguageClientAware {

    private final SMTTextDocumentService textDocumentService = new SMTTextDocumentService();
    private final SMTWorkspaceService    workspaceService    = new SMTWorkspaceService(textDocumentService);

    private int exitCode = 1;

    @Override
    public CompletableFuture<InitializeResult> initialize(InitializeParams params) {
        ServerLog.serverLog("[initialize] rootUri=" + params.getRootUri());

        var caps = new ServerCapabilities();
        caps.setTextDocumentSync(TextDocumentSyncKind.Full);
        caps.setDocumentSymbolProvider(Boolean.TRUE);
        caps.setWorkspaceSymbolProvider(Boolean.TRUE);
        caps.setHoverProvider(Boolean.TRUE);

        return CompletableFuture.completedFuture(new InitializeResult(caps));
    }

    @Override
    public void initialized(InitializedParams params) {
        ServerLog.serverLog("[initialized]");
    }

    @Override
    public CompletableFuture<Object> shutdown() {
        exitCode = 0;
        textDocumentService.shutdown();
        return CompletableFuture.completedFuture(null);
    }

    @Override
    public void exit() {
        System.exit(exitCode);
    }

    @Override
    public TextDocumentService getTextDocumentService() {
        return textDocumentService;
    }

    @Override
    public WorkspaceService getWorkspaceService() {
        return workspaceService;
    }

    @Override
    public void connect(LanguageClient client) {
        textDocumentService.connect(client);
    }
}
