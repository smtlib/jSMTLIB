package org.smtlib.lsp;

import org.eclipse.lsp4j.DidChangeTextDocumentParams;
import org.eclipse.lsp4j.DidCloseTextDocumentParams;
import org.eclipse.lsp4j.DidOpenTextDocumentParams;
import org.eclipse.lsp4j.DidSaveTextDocumentParams;
import org.eclipse.lsp4j.DocumentSymbol;
import org.eclipse.lsp4j.DocumentSymbolParams;
import org.eclipse.lsp4j.Hover;
import org.eclipse.lsp4j.HoverParams;
import org.eclipse.lsp4j.MarkupContent;
import org.eclipse.lsp4j.MarkupKind;
import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.PublishDiagnosticsParams;
import org.eclipse.lsp4j.Range;
import org.eclipse.lsp4j.SymbolInformation;
import org.eclipse.lsp4j.WorkspaceSymbol;
import org.eclipse.lsp4j.WorkspaceSymbolLocation;
import org.eclipse.lsp4j.jsonrpc.messages.Either;
import org.eclipse.lsp4j.services.LanguageClient;
import org.eclipse.lsp4j.services.TextDocumentService;
import org.smtlib.ICommand;
import org.smtlib.IPos;

import java.io.IOException;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.ScheduledFuture;
import java.util.concurrent.TimeUnit;

/**
 * Handles text document lifecycle for SMT-LIB files.
 *
 * On open/change/save, the document is (re)parsed and diagnostics are published.
 * Document symbols, workspace symbols, and hover are derived from the parsed AST.
 *
 * Changes are debounced by {@value #DEBOUNCE_MS} ms so rapid edits don't
 * trigger unnecessary re-parses.
 */
public class SMTTextDocumentService implements TextDocumentService {

    private static final long DEBOUNCE_MS = 300;

    private final ConcurrentHashMap<String, ParsedDocument> documents = new ConcurrentHashMap<>();
    private final ConcurrentHashMap<String, ScheduledFuture<?>> pending  = new ConcurrentHashMap<>();
    private final ScheduledExecutorService executor =
            Executors.newSingleThreadScheduledExecutor(r -> {
                var t = new Thread(r, "smtlib-lsp-parser");
                t.setDaemon(true);
                return t;
            });

    private volatile LanguageClient client;

    public void connect(LanguageClient client) {
        this.client = client;
    }

    // -----------------------------------------------------------------------
    // Text document notifications
    // -----------------------------------------------------------------------

    @Override
    public void didOpen(DidOpenTextDocumentParams params) {
        String uri  = params.getTextDocument().getUri();
        String text = params.getTextDocument().getText();
        scheduleReparse(uri, text);
    }

    @Override
    public void didChange(DidChangeTextDocumentParams params) {
        String uri = params.getTextDocument().getUri();
        var changes = params.getContentChanges();
        if (changes == null || changes.isEmpty()) return;
        // Full sync: last change entry contains the full document text.
        String text = changes.get(changes.size() - 1).getText();
        scheduleReparse(uri, text);
    }

    @Override
    public void didSave(DidSaveTextDocumentParams params) {
        String uri = params.getTextDocument().getUri();
        ParsedDocument cached = documents.get(uri);
        if (cached != null) {
            // Save doesn't provide new text in Full sync; reparse cached text to
            // ensure any save-hook transformations are reflected.
            scheduleReparse(uri, cached.text());
        }
    }

    @Override
    public void didClose(DidCloseTextDocumentParams params) {
        String uri = params.getTextDocument().getUri();
        documents.remove(uri);
        cancelPending(uri);
        // Clear diagnostics for this document.
        if (client != null)
            client.publishDiagnostics(new PublishDiagnosticsParams(uri, List.of()));
    }

    // -----------------------------------------------------------------------
    // Document symbols
    // -----------------------------------------------------------------------

    @Override
    public CompletableFuture<List<Either<SymbolInformation, DocumentSymbol>>>
            documentSymbol(DocumentSymbolParams params) {
        String uri = params.getTextDocument().getUri();
        ParsedDocument doc = documents.get(uri);
        List<Either<SymbolInformation, DocumentSymbol>> result = new ArrayList<>();
        if (doc != null) {
            for (DocumentSymbol ds : DocumentSymbolProvider.extract(doc.commands(), doc.source())) {
                result.add(Either.forRight(ds));
            }
        }
        return CompletableFuture.completedFuture(result);
    }

    // -----------------------------------------------------------------------
    // Hover
    // -----------------------------------------------------------------------

    @Override
    public CompletableFuture<Hover> hover(HoverParams params) {
        String uri = params.getTextDocument().getUri();
        Position pos = params.getPosition();
        ParsedDocument doc = documents.get(uri);
        if (doc == null || doc.source() == null) return CompletableFuture.completedFuture(null);

        ICommand found = commandAt(doc, pos);
        if (found == null) return CompletableFuture.completedFuture(null);

        org.smtlib.SMT smtForPrinting = new org.smtlib.SMT();
        String printed = smtForPrinting.smtConfig.defaultPrinter.toString(found);
        var content = new MarkupContent(MarkupKind.MARKDOWN, "```smt2\n" + printed + "\n```");
        return CompletableFuture.completedFuture(new Hover(content));
    }

    // -----------------------------------------------------------------------
    // Workspace symbols
    // -----------------------------------------------------------------------

    List<WorkspaceSymbol> workspaceSymbols(String queryLower) {
        var result = new ArrayList<WorkspaceSymbol>();
        for (ParsedDocument doc : documents.values()) {
            for (DocumentSymbol ds : DocumentSymbolProvider.extract(doc.commands(), doc.source())) {
                if (queryLower.isEmpty() || ds.getName().toLowerCase().contains(queryLower)) {
                    var ws = new WorkspaceSymbol();
                    ws.setName(ds.getName());
                    ws.setKind(ds.getKind());
                    ws.setLocation(Either.forRight(new WorkspaceSymbolLocation(doc.uri())));
                    result.add(ws);
                }
            }
        }
        return result;
    }

    // -----------------------------------------------------------------------
    // Reparse from disk (for watched-file changes)
    // -----------------------------------------------------------------------

    void reparseFromDisk(String uri) {
        try {
            Path path = Path.of(URI.create(uri));
            String text = Files.readString(path);
            scheduleReparse(uri, text);
        } catch (IOException e) {
            ServerLog.serverLog("Failed to read " + uri + " from disk: " + e.getMessage());
        }
    }

    // -----------------------------------------------------------------------
    // Shutdown
    // -----------------------------------------------------------------------

    public void shutdown() {
        executor.shutdownNow();
    }

    // -----------------------------------------------------------------------
    // Internal helpers
    // -----------------------------------------------------------------------

    private void scheduleReparse(String uri, String text) {
        cancelPending(uri);
        ScheduledFuture<?> future = executor.schedule(
                () -> doReparse(uri, text), DEBOUNCE_MS, TimeUnit.MILLISECONDS);
        pending.put(uri, future);
    }

    private void cancelPending(String uri) {
        ScheduledFuture<?> old = pending.remove(uri);
        if (old != null) old.cancel(false);
    }

    private void doReparse(String uri, String text) {
        pending.remove(uri);
        ParsedDocument doc = DocumentParser.parse(uri, text);
        documents.put(uri, doc);
        if (client != null) {
            client.publishDiagnostics(new PublishDiagnosticsParams(uri, doc.diagnostics()));
        }
    }

    /**
     * Finds the innermost command whose position contains the given LSP cursor position.
     * Falls back to the first command if none contains the position exactly.
     */
    private ICommand commandAt(ParsedDocument doc, Position pos) {
        if (doc.source() == null) return null;
        ICommand best = null;
        for (ICommand cmd : doc.commands()) {
            if (cmd instanceof IPos.IPosable p) {
                IPos ipos = p.pos();
                if (ipos != null) {
                    Range r = PositionUtils.toRange(ipos);
                    if (containsPosition(r, pos)) {
                        best = cmd;
                    }
                }
            }
        }
        return best;
    }

    private static boolean containsPosition(Range range, Position pos) {
        Position s = range.getStart();
        Position e = range.getEnd();
        if (pos.getLine() < s.getLine() || pos.getLine() > e.getLine()) return false;
        if (pos.getLine() == s.getLine() && pos.getCharacter() < s.getCharacter()) return false;
        if (pos.getLine() == e.getLine() && pos.getCharacter() > e.getCharacter()) return false;
        return true;
    }

}
