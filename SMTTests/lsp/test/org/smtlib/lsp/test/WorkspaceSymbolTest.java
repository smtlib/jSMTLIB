package org.smtlib.lsp.test;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.HashSet;
import java.util.Set;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Tests the {@code workspace/symbol} request over the wire.
 *
 * Verifies cross-document symbol search: after opening multiple documents, a
 * workspace/symbol query should find declarations from all open files.
 */
public class WorkspaceSymbolTest extends ProtocolTestBase {

    private static final String URI_A = "file:///test/a.smt2";
    private static final String URI_B = "file:///test/b.smt2";

    private JsonArray requestWorkspaceSymbols(String query) throws Exception {
        client.sendRequest("workspace/symbol",
                "{\"query\":\"" + query + "\"}");
        JsonObject resp = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        assertNotNull("Expected workspace/symbol response", resp);
        assertFalse("workspace/symbol must not return an error", resp.has("error"));
        // LSP4J serializes Either.forRight(List<WorkspaceSymbol>) as a plain JSON array.
        // If the result is an array, return it directly.
        if (resp.get("result").isJsonArray()) {
            return resp.getAsJsonArray("result");
        }
        // Fallback: wrapped {"right": [...]} form (not currently produced but safe).
        JsonObject resultObj = resp.getAsJsonObject("result");
        if (resultObj != null && resultObj.has("right")) {
            return resultObj.getAsJsonArray("right");
        }
        return new JsonArray();
    }

    private Set<String> symbolNames(JsonArray syms) {
        Set<String> names = new HashSet<>();
        if (syms == null) return names;
        for (int i = 0; i < syms.size(); i++) {
            JsonObject sym = syms.get(i).getAsJsonObject();
            names.add(sym.get("name").getAsString());
        }
        return names;
    }

    @Test
    public void emptyQueryReturnsAllSymbols() throws Exception {
        didOpen(URI_A, "(set-logic QF_UF)\n(declare-fun alpha () Bool)\n");
        didOpen(URI_B, "(set-logic QF_UF)\n(declare-fun beta () Bool)\n");
        nextDiagsForUri(URI_A, PARSE_TIMEOUT);
        nextDiagsForUri(URI_B, PARSE_TIMEOUT);

        JsonArray syms = requestWorkspaceSymbols("");
        Set<String> names = symbolNames(syms);
        assertTrue("'alpha' should be in workspace symbols", names.contains("alpha"));
        assertTrue("'beta' should be in workspace symbols",  names.contains("beta"));
    }

    @Test
    public void queryFiltersResults() throws Exception {
        didOpen(URI_A, "(set-logic QF_UF)\n(declare-fun foo () Bool)\n(declare-fun bar () Bool)\n");
        nextDiagsForUri(URI_A, PARSE_TIMEOUT);

        JsonArray syms = requestWorkspaceSymbols("foo");
        Set<String> names = symbolNames(syms);
        assertTrue("'foo' should match query 'foo'", names.contains("foo"));
        assertFalse("'bar' should not match query 'foo'", names.contains("bar"));
    }

    @Test
    public void queryIsCaseInsensitive() throws Exception {
        didOpen(URI_A, "(set-logic QF_UF)\n(declare-fun MyFunc () Bool)\n");
        nextDiagsForUri(URI_A, PARSE_TIMEOUT);

        JsonArray syms = requestWorkspaceSymbols("myfunc");
        Set<String> names = symbolNames(syms);
        assertTrue("Case-insensitive query 'myfunc' should match 'MyFunc'",
                names.contains("MyFunc"));
    }

    @Test
    public void symbolsFromClosedDocumentAreGone() throws Exception {
        didOpen(URI_A, "(declare-fun temp () Bool)\n");
        nextDiagsForUri(URI_A, PARSE_TIMEOUT);

        // Confirm it's present before close
        JsonArray before = requestWorkspaceSymbols("temp");
        assertTrue("'temp' should be present before close",
                symbolNames(before).contains("temp"));

        // Close the document — diagnostics are cleared, document removed from cache
        didClose(URI_A);

        JsonArray after = requestWorkspaceSymbols("temp");
        assertFalse("'temp' should be absent after the document is closed",
                symbolNames(after).contains("temp"));
    }

    @Test
    public void partialQueryMatchesSubstring() throws Exception {
        didOpen(URI_A, "(set-logic QF_LIA)\n(declare-fun myLongFunctionName () Int)\n");
        nextDiagsForUri(URI_A, PARSE_TIMEOUT);

        JsonArray syms = requestWorkspaceSymbols("long");
        assertTrue("Substring 'long' should match 'myLongFunctionName'",
                symbolNames(syms).contains("myLongFunctionName"));
    }
}
