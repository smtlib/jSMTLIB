package org.smtlib.lsp.test;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.eclipse.lsp4j.launch.LSPLauncher;
import org.junit.After;
import org.junit.Before;
import org.smtlib.lsp.SMTLanguageServer;

import java.io.PipedInputStream;
import java.io.PipedOutputStream;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.assertNotNull;

/**
 * Base class for over-the-wire SMT-LIB LSP protocol tests.
 *
 * Sets up a full in-process server/client pair connected via {@link java.io.PipedInputStream} /
 * {@link java.io.PipedOutputStream}.  All JSON-RPC Content-Length framing, serialization, and
 * deserialization is exercised on every message — the communication mechanisms are tested
 * alongside the LSP functionality.
 *
 * Each test method gets a fresh server via {@code @Before} / {@code @After}.
 */
public abstract class ProtocolTestBase {

    /** Timeout for operations that complete quickly (initialize, symbol lookup, etc.). */
    protected static final long SHORT_TIMEOUT = 5;

    /** Timeout for operations that involve a parse+debounce cycle. */
    protected static final long PARSE_TIMEOUT = 3;

    protected SMTLanguageServer server;
    protected RawLspClient      client;

    @Before
    public void setUp() throws Exception {
        startServer();
    }

    @After
    public void tearDown() {
        if (client != null) client.stop();
    }

    // -----------------------------------------------------------------------
    // Server lifecycle
    // -----------------------------------------------------------------------

    /**
     * Create a server/client pipe pair and complete the LSP initialize handshake.
     * Call this from {@code setUp()} or at the start of a test that needs to
     * control initialization options.
     */
    protected void startServer() throws Exception {
        PipedInputStream  serverIn  = new PipedInputStream(65536);
        PipedOutputStream clientOut = new PipedOutputStream(serverIn);
        PipedInputStream  clientIn  = new PipedInputStream(65536);
        PipedOutputStream serverOut = new PipedOutputStream(clientIn);

        server = new SMTLanguageServer();
        var launcher = LSPLauncher.createServerLauncher(server, serverIn, serverOut);
        server.connect(launcher.getRemoteProxy());
        launcher.startListening();

        client = new RawLspClient(clientOut, clientIn);
        client.sendRequest("initialize",
                "{\"processId\":null,\"rootUri\":null,\"capabilities\":{}}");
        assertNotNull("Server must respond to initialize",
                client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS));
        client.sendNotification("initialized", "{}");
    }

    // -----------------------------------------------------------------------
    // JSON helpers
    // -----------------------------------------------------------------------

    /** Escape a Java string for embedding as a JSON string value. */
    protected static String jsonEscape(String s) {
        return s.replace("\\", "\\\\").replace("\"", "\\\"").replace("\n", "\\n");
    }

    /** Build a didOpen params JSON string for a .smt2 document. */
    protected static String didOpenParams(String uri, String text) {
        return "{\"textDocument\":{\"uri\":\"" + uri
                + "\",\"languageId\":\"smt2\",\"version\":1,"
                + "\"text\":\"" + jsonEscape(text) + "\"}}";
    }

    // -----------------------------------------------------------------------
    // Document lifecycle notifications
    // -----------------------------------------------------------------------

    protected void didOpen(String uri, String text) throws Exception {
        client.sendNotification("textDocument/didOpen", didOpenParams(uri, text));
    }

    protected void didChange(String uri, int version, String text) throws Exception {
        client.sendNotification("textDocument/didChange",
                "{\"textDocument\":{\"uri\":\"" + uri + "\",\"version\":" + version + "},"
                + "\"contentChanges\":[{\"text\":\"" + jsonEscape(text) + "\"}]}");
    }

    protected void didSave(String uri) throws Exception {
        client.sendNotification("textDocument/didSave",
                "{\"textDocument\":{\"uri\":\"" + uri + "\"}}");
    }

    protected void didClose(String uri) throws Exception {
        client.sendNotification("textDocument/didClose",
                "{\"textDocument\":{\"uri\":\"" + uri + "\"}}");
    }

    // -----------------------------------------------------------------------
    // publishDiagnostics helpers
    // -----------------------------------------------------------------------

    /**
     * Wait for the next {@code textDocument/publishDiagnostics} notification for
     * any URI that contains {@code uriFragment}.
     */
    protected JsonObject nextDiagsFor(String uriFragment, long timeoutSec)
            throws InterruptedException {
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(timeoutSec);
        while (true) {
            long remaining = deadline - System.nanoTime();
            if (remaining <= 0) return null;
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", remaining, TimeUnit.NANOSECONDS);
            if (msg == null) return null;
            if (msg.getAsJsonObject("params").get("uri").getAsString().contains(uriFragment))
                return msg;
        }
    }

    /**
     * Wait for the next {@code textDocument/publishDiagnostics} for an exact URI.
     */
    protected JsonObject nextDiagsForUri(String uri, long timeoutSec)
            throws InterruptedException {
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(timeoutSec);
        while (true) {
            long remaining = deadline - System.nanoTime();
            if (remaining <= 0) return null;
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", remaining, TimeUnit.NANOSECONDS);
            if (msg == null) return null;
            if (uri.equals(msg.getAsJsonObject("params").get("uri").getAsString()))
                return msg;
        }
    }

    /**
     * Poll until a {@code publishDiagnostics} arrives for the given URI that
     * has at least one diagnostic.  Skips empty notifications.
     */
    protected JsonObject nextNonEmptyDiagsForUri(String uri, long timeoutSec)
            throws InterruptedException {
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(timeoutSec);
        while (true) {
            long remaining = deadline - System.nanoTime();
            if (remaining <= 0) return null;
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", remaining, TimeUnit.NANOSECONDS);
            if (msg == null) return null;
            JsonObject params = msg.getAsJsonObject("params");
            if (!uri.equals(params.get("uri").getAsString())) continue;
            if (!params.getAsJsonArray("diagnostics").isEmpty()) return msg;
        }
    }

    // -----------------------------------------------------------------------
    // Diagnostic inspection
    // -----------------------------------------------------------------------

    /** True if any diagnostic in {@code diags} has an error message containing {@code fragment}. */
    protected static boolean hasMessageContaining(JsonArray diags, String fragment) {
        for (int i = 0; i < diags.size(); i++) {
            JsonObject d = diags.get(i).getAsJsonObject();
            if (d.has("message") && d.get("message").getAsString().contains(fragment))
                return true;
        }
        return false;
    }

    /** Return the diagnostic array from a {@code publishDiagnostics} notification. */
    protected static JsonArray diagsFrom(JsonObject notification) {
        return notification.getAsJsonObject("params").getAsJsonArray("diagnostics");
    }

    /** Return the zero-based start line of the first diagnostic, or -1. */
    protected static int firstDiagLine(JsonArray diags) {
        if (diags == null || diags.isEmpty()) return -1;
        return diags.get(0).getAsJsonObject()
                .getAsJsonObject("range")
                .getAsJsonObject("start")
                .get("line").getAsInt();
    }
}
