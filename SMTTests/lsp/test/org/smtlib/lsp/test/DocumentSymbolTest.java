package org.smtlib.lsp.test;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.HashSet;
import java.util.Set;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Tests the {@code textDocument/documentSymbol} request over the wire.
 *
 * Verifies that declarations extracted from parsed SMT-LIB commands are returned
 * with the correct name and kind through the full JSON-RPC framing path.
 */
public class DocumentSymbolTest extends ProtocolTestBase {

    private static final String URI = "file:///test/symbols.smt2";

    private JsonArray requestDocumentSymbols(String uri) throws Exception {
        client.sendRequest("textDocument/documentSymbol",
                "{\"textDocument\":{\"uri\":\"" + uri + "\"}}");
        JsonObject resp = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        assertNotNull("Expected documentSymbol response", resp);
        assertFalse("documentSymbol must not return an error", resp.has("error"));
        return resp.getAsJsonArray("result");
    }

    @Test
    public void declareFunAppearsAsFunction() throws Exception {
        didOpen(URI, "(set-logic QF_UF)\n(declare-fun p () Bool)\n");
        nextDiagsForUri(URI, PARSE_TIMEOUT);  // wait for parse to complete

        JsonArray syms = requestDocumentSymbols(URI);
        assertNotNull("Expected symbol list", syms);

        boolean found = false;
        for (int i = 0; i < syms.size(); i++) {
            JsonObject sym = syms.get(i).getAsJsonObject();
            // DocumentSymbol is in forRight slot of Either
            JsonObject ds = sym.has("right") ? sym.getAsJsonObject("right") : sym;
            if ("p".equals(ds.get("name").getAsString())) {
                found = true;
                // SymbolKind.Function = 12
                assertEquals("declare-fun should have kind Function (12)",
                        12, ds.get("kind").getAsInt());
            }
        }
        assertTrue("Symbol 'p' should appear in document symbols", found);
    }

    @Test
    public void declareSortAppearsAsClass() throws Exception {
        didOpen(URI, "(set-logic QF_UF)\n(declare-sort MySort 0)\n");
        nextDiagsForUri(URI, PARSE_TIMEOUT);

        JsonArray syms = requestDocumentSymbols(URI);
        assertNotNull(syms);

        boolean found = false;
        for (int i = 0; i < syms.size(); i++) {
            JsonObject sym = syms.get(i).getAsJsonObject();
            JsonObject ds = sym.has("right") ? sym.getAsJsonObject("right") : sym;
            if ("MySort".equals(ds.get("name").getAsString())) {
                found = true;
                // SymbolKind.Class = 5
                assertEquals("declare-sort should have kind Class (5)",
                        5, ds.get("kind").getAsInt());
            }
        }
        assertTrue("Symbol 'MySort' should appear in document symbols", found);
    }

    @Test
    public void defineFunAppearsAsFunction() throws Exception {
        didOpen(URI, "(set-logic QF_UF)\n(define-fun double ((x Int)) Int (* 2 x))\n");
        nextDiagsForUri(URI, PARSE_TIMEOUT);

        JsonArray syms = requestDocumentSymbols(URI);
        assertNotNull(syms);

        boolean found = false;
        for (int i = 0; i < syms.size(); i++) {
            JsonObject sym = syms.get(i).getAsJsonObject();
            JsonObject ds = sym.has("right") ? sym.getAsJsonObject("right") : sym;
            if ("double".equals(ds.get("name").getAsString())) {
                found = true;
                assertEquals("define-fun should have kind Function (12)",
                        12, ds.get("kind").getAsInt());
            }
        }
        assertTrue("Symbol 'double' should appear in document symbols", found);
    }

    @Test
    public void multipleDeclarationsAllAppear() throws Exception {
        String text = "(set-logic QF_UF)\n"
                    + "(declare-fun f () Bool)\n"
                    + "(declare-fun g () Bool)\n"
                    + "(declare-sort S 0)\n";
        didOpen(URI, text);
        nextDiagsForUri(URI, PARSE_TIMEOUT);

        JsonArray syms = requestDocumentSymbols(URI);
        assertNotNull(syms);

        Set<String> names = new HashSet<>();
        for (int i = 0; i < syms.size(); i++) {
            JsonObject sym = syms.get(i).getAsJsonObject();
            JsonObject ds = sym.has("right") ? sym.getAsJsonObject("right") : sym;
            names.add(ds.get("name").getAsString());
        }
        assertTrue("Symbol 'f' should be present", names.contains("f"));
        assertTrue("Symbol 'g' should be present", names.contains("g"));
        assertTrue("Symbol 'S' should be present", names.contains("S"));
    }

    @Test
    public void emptyDocumentReturnsEmptyList() throws Exception {
        didOpen(URI, "");
        nextDiagsForUri(URI, PARSE_TIMEOUT);

        JsonArray syms = requestDocumentSymbols(URI);
        assertNotNull(syms);
        assertEquals("Empty document should return empty symbol list", 0, syms.size());
    }

    @Test
    public void setLogicAppearsAsModule() throws Exception {
        didOpen(URI, "(set-logic QF_BV)\n");
        nextDiagsForUri(URI, PARSE_TIMEOUT);

        JsonArray syms = requestDocumentSymbols(URI);
        assertNotNull(syms);

        boolean found = false;
        for (int i = 0; i < syms.size(); i++) {
            JsonObject sym = syms.get(i).getAsJsonObject();
            JsonObject ds = sym.has("right") ? sym.getAsJsonObject("right") : sym;
            String name = ds.get("name").getAsString();
            if (name.contains("QF_BV")) {
                found = true;
                // SymbolKind.Module = 2
                assertEquals("set-logic should have kind Module (2)",
                        2, ds.get("kind").getAsInt());
            }
        }
        assertTrue("set-logic QF_BV should appear as a module symbol", found);
    }
}
