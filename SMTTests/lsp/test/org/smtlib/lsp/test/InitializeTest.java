package org.smtlib.lsp.test;

import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Tests the LSP initialize / initialized handshake over the wire.
 *
 * Verifies that the server:
 * - responds to initialize with the expected capabilities
 * - accepts the initialized notification without error
 * - responds to shutdown with null result
 * - terminates cleanly after exit
 */
public class InitializeTest extends ProtocolTestBase {

    @Test
    public void initializeReturnsCapabilities() throws Exception {
        // The handshake is already done in setUp() via startServer().
        // Start a fresh exchange to inspect the raw initialize response.
        client.stop();

        var serverIn  = new java.io.PipedInputStream(65536);
        var clientOut = new java.io.PipedOutputStream(serverIn);
        var clientIn  = new java.io.PipedInputStream(65536);
        var serverOut = new java.io.PipedOutputStream(clientIn);

        var freshServer = new org.smtlib.lsp.SMTLanguageServer();
        var launcher = org.eclipse.lsp4j.launch.LSPLauncher.createServerLauncher(
                freshServer, serverIn, serverOut);
        freshServer.connect(launcher.getRemoteProxy());
        launcher.startListening();

        var freshClient = new RawLspClient(clientOut, clientIn);
        freshClient.sendRequest("initialize",
                "{\"processId\":null,\"rootUri\":null,\"capabilities\":{}}");

        JsonObject resp = freshClient.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        assertNotNull("Expected initialize response", resp);

        // Must be a successful result (no "error" field)
        assertFalse("Initialize must not return an error", resp.has("error"));
        assertTrue("Initialize must return a result", resp.has("result"));

        JsonObject caps = resp.getAsJsonObject("result").getAsJsonObject("capabilities");
        assertNotNull("Capabilities must be present", caps);

        // textDocumentSync: 1 = Full
        assertEquals("textDocumentSync should be Full (1)",
                1, caps.get("textDocumentSync").getAsInt());

        assertTrue("hoverProvider must be true",
                caps.get("hoverProvider").getAsBoolean());
        assertTrue("documentSymbolProvider must be true",
                caps.get("documentSymbolProvider").getAsBoolean());
        assertTrue("workspaceSymbolProvider must be true",
                caps.get("workspaceSymbolProvider").getAsBoolean());

        freshClient.stop();
    }

    @Test
    public void shutdownReturnsNull() throws Exception {
        client.sendRequest("shutdown", null);
        JsonObject resp = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        assertNotNull("Expected shutdown response", resp);
        assertFalse("Shutdown must not return an error", resp.has("error"));
        // result must be null (JSON null)
        assertTrue("Shutdown result must be null",
                resp.has("result") && resp.get("result").isJsonNull());
    }

    @Test
    public void unknownRequestReturnsMethodNotFound() throws Exception {
        client.sendRequest("smtlib/nonExistentMethod", "{}");
        JsonObject resp = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        assertNotNull("Expected a response to unknown method", resp);
        // LSP4J returns an error with code -32601 (MethodNotFound)
        assertTrue("Unknown method must return an error", resp.has("error"));
        assertEquals("Error code must be MethodNotFound (-32601)",
                -32601, resp.getAsJsonObject("error").get("code").getAsInt());
    }
}
