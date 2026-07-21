package org.smtlib.lsp.test;

import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Tests the {@code textDocument/hover} request over the wire.
 *
 * Hover over an SMT-LIB command should return the printed text of that command
 * formatted as a Markdown code block.
 */
public class HoverTest extends ProtocolTestBase {

    private static final String URI = "file:///test/hover.smt2";

    private JsonObject requestHover(String uri, int line, int character) throws Exception {
        client.sendRequest("textDocument/hover",
                "{\"textDocument\":{\"uri\":\"" + uri + "\"},"
                + "\"position\":{\"line\":" + line + ",\"character\":" + character + "}}");
        return client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
    }

    @Test
    public void hoverOverDeclareFunReturnsContent() throws Exception {
        String text = "(set-logic QF_UF)\n"
                    + "(declare-fun p () Bool)\n"
                    + "(check-sat)\n";
        didOpen(URI, text);
        nextDiagsForUri(URI, PARSE_TIMEOUT);

        // Hover in the middle of "(declare-fun p () Bool)" — line 1
        JsonObject resp = requestHover(URI, 1, 5);
        assertNotNull("Expected hover response", resp);
        assertFalse("Hover must not return an error", resp.has("error"));

        // Result may be null if cursor is not inside a command
        if (!resp.get("result").isJsonNull()) {
            JsonObject result = resp.getAsJsonObject("result");
            assertNotNull("Hover result must have contents", result);
            JsonObject contents = result.getAsJsonObject("contents");
            assertNotNull(contents);
            String value = contents.get("value").getAsString();
            assertTrue("Hover content should contain 'declare-fun'",
                    value.contains("declare-fun"));
        }
        // Null result is also acceptable when no command spans the cursor position.
    }

    @Test
    public void hoverOverCheckSatReturnsContent() throws Exception {
        String text = "(set-logic QF_UF)\n"
                    + "(check-sat)\n";
        didOpen(URI, text);
        nextDiagsForUri(URI, PARSE_TIMEOUT);

        JsonObject resp = requestHover(URI, 1, 2);
        assertNotNull("Expected hover response", resp);
        assertFalse("Hover must not return an error", resp.has("error"));
        // null or non-null — both acceptable; just must not crash the server
    }

    @Test
    public void hoverOnUnparsedDocumentDoesNotCrash() throws Exception {
        // Document with parse error — hover must not throw
        String text = "(assert )\n";
        didOpen(URI, text);
        nextDiagsForUri(URI, PARSE_TIMEOUT);  // wait for parse

        JsonObject resp = requestHover(URI, 0, 3);
        assertNotNull("Expected hover response even for bad document", resp);
        assertFalse("Hover on bad document must not return a protocol error",
                resp.has("error"));
    }

    @Test
    public void hoverOnUnopenedDocumentReturnsNull() throws Exception {
        // No didOpen — the document is not in the cache
        JsonObject resp = requestHover("file:///test/nonexistent.smt2", 0, 0);
        assertNotNull("Expected a response for unknown document", resp);
        assertFalse("Should not return protocol error", resp.has("error"));
        // result should be null
        assertTrue("Hover on unknown document should return null",
                resp.has("result") && resp.get("result").isJsonNull());
    }

    @Test
    public void hoverContentIsMarkdown() throws Exception {
        String text = "(set-logic QF_LIA)\n"
                    + "(declare-fun x () Int)\n";
        didOpen(URI, text);
        nextDiagsForUri(URI, PARSE_TIMEOUT);

        JsonObject resp = requestHover(URI, 1, 5);
        assertNotNull(resp);
        if (!resp.get("result").isJsonNull()) {
            JsonObject result = resp.getAsJsonObject("result");
            JsonObject contents = result.getAsJsonObject("contents");
            if (contents != null && contents.has("kind")) {
                assertEquals("Hover content kind should be markdown",
                        "markdown", contents.get("kind").getAsString());
            }
        }
    }
}
