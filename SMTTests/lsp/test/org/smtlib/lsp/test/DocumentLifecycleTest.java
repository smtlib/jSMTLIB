package org.smtlib.lsp.test;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Tests the open / change / save / close document lifecycle over the wire.
 *
 * Verifies that:
 * - didOpen triggers a parse and diagnostics publication
 * - didChange with corrected content clears diagnostics
 * - didChange with new errors reports them
 * - didClose clears diagnostics for the closed URI
 * - didSave triggers a re-parse
 */
public class DocumentLifecycleTest extends ProtocolTestBase {

    private static final String URI = "file:///test/lifecycle.smt2";

    @Test
    public void didOpenTriggersDiagnostics() throws Exception {
        didOpen(URI, "(assert )\n");  // parse error
        JsonObject notif = nextNonEmptyDiagsForUri(URI, PARSE_TIMEOUT);
        assertNotNull("didOpen must trigger publishDiagnostics", notif);
        assertFalse("Should have diagnostics for bad document",
                diagsFrom(notif).isEmpty());
    }

    @Test
    public void didChangeFixesError() throws Exception {
        // Open with an error
        didOpen(URI, "(assert )\n");
        nextNonEmptyDiagsForUri(URI, PARSE_TIMEOUT);

        // Fix the error via didChange
        didChange(URI, 2, "(set-logic QF_UF)\n(declare-fun p () Bool)\n(assert p)\n");
        JsonObject notif = nextDiagsForUri(URI, PARSE_TIMEOUT);
        assertNotNull("didChange must trigger publishDiagnostics", notif);
        assertEquals("Fixed document should have no diagnostics",
                0, diagsFrom(notif).size());
    }

    @Test
    public void didChangeIntroducesError() throws Exception {
        // Open with valid content
        didOpen(URI, "(set-logic QF_UF)\n(check-sat)\n");
        nextDiagsForUri(URI, PARSE_TIMEOUT);

        // Introduce an error via didChange
        didChange(URI, 2, "(assert )\n");
        JsonObject notif = nextNonEmptyDiagsForUri(URI, PARSE_TIMEOUT);
        assertNotNull("didChange with error must trigger publishDiagnostics", notif);
        assertFalse("Should have diagnostics after introducing error",
                diagsFrom(notif).isEmpty());
    }

    @Test
    public void didCloseClearsDiagnostics() throws Exception {
        // Open with an error to ensure diagnostics are published
        didOpen(URI, "(assert )\n");
        nextNonEmptyDiagsForUri(URI, PARSE_TIMEOUT);

        // Close the document
        didClose(URI);

        // Server should publish empty diagnostics to clear them
        JsonObject notif = nextDiagsForUri(URI, PARSE_TIMEOUT);
        assertNotNull("didClose must trigger publishDiagnostics([])", notif);
        assertEquals("Closed document diagnostics should be cleared",
                0, diagsFrom(notif).size());
    }

    @Test
    public void didSaveReparses() throws Exception {
        // Open valid content
        didOpen(URI, "(set-logic QF_UF)\n(check-sat)\n");
        nextDiagsForUri(URI, PARSE_TIMEOUT);

        // Save should trigger a reparse and new publishDiagnostics
        didSave(URI);
        JsonObject notif = nextDiagsForUri(URI, PARSE_TIMEOUT);
        assertNotNull("didSave must trigger publishDiagnostics", notif);
        assertEquals("Saved clean document should have no diagnostics",
                0, diagsFrom(notif).size());
    }

    @Test
    public void multipleRapidChangesAllGetDiagnostics() throws Exception {
        // Each change should eventually produce a publishDiagnostics, though
        // debouncing may collapse rapid consecutive changes into one.
        didOpen(URI, "(check-sat)\n");
        nextDiagsForUri(URI, PARSE_TIMEOUT);

        didChange(URI, 2, "(assert )\n");
        didChange(URI, 3, "(check-sat)\n");
        // At least one publishDiagnostics must arrive (for the final state)
        JsonObject notif = nextDiagsForUri(URI, PARSE_TIMEOUT);
        assertNotNull("At least one publishDiagnostics must arrive after changes", notif);
    }

    @Test
    public void twoDocumentsAreIndependent() throws Exception {
        String uri1 = "file:///test/a.smt2";
        String uri2 = "file:///test/b.smt2";

        didOpen(uri1, "(assert )\n");           // error in doc1
        didOpen(uri2, "(check-sat)\n");         // clean doc2

        JsonObject diags1 = nextNonEmptyDiagsForUri(uri1, PARSE_TIMEOUT);
        JsonObject diags2 = nextDiagsForUri(uri2, PARSE_TIMEOUT);

        assertNotNull("doc1 should have error diagnostics", diags1);
        assertNotNull("doc2 should have clean diagnostics", diags2);
        assertFalse("doc1 should have errors", diagsFrom(diags1).isEmpty());
        assertEquals("doc2 should have no errors", 0, diagsFrom(diags2).size());
    }
}
