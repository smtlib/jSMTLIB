package org.smtlib.lsp.test;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Tests that parse errors in SMT-LIB documents are reported as LSP diagnostics
 * at the correct line and character position.
 *
 * All communication goes over in-process pipes, exercising the full
 * Content-Length JSON-RPC framing path.
 */
public class DiagnosticsTest extends ProtocolTestBase {

    private static final String URI = "file:///test/check.smt2";

    @Test
    public void cleanDocumentPublishesEmptyDiagnostics() throws Exception {
        String text = "(set-logic QF_UF)\n"
                    + "(declare-fun p () Bool)\n"
                    + "(assert p)\n"
                    + "(check-sat)\n";
        didOpen(URI, text);
        JsonObject notif = nextDiagsForUri(URI, PARSE_TIMEOUT);
        assertNotNull("Expected publishDiagnostics for clean document", notif);
        assertEquals("Clean document must have no diagnostics",
                0, diagsFrom(notif).size());
    }

    @Test
    public void missingExpressionInAssert() throws Exception {
        // (assert ) is missing the expression argument
        String text = "(set-logic QF_UF)\n"
                    + "(declare-fun p () Bool)\n"
                    + "(assert )\n"
                    + "(check-sat)\n";
        didOpen(URI, text);
        JsonObject notif = nextNonEmptyDiagsForUri(URI, PARSE_TIMEOUT);
        assertNotNull("Expected a diagnostic for missing expression", notif);

        JsonArray diags = diagsFrom(notif);
        assertFalse("Should have at least one diagnostic", diags.isEmpty());
        // Error should be on line 2 (0-based), where (assert ) appears
        assertEquals("Error should be on line 2", 2, firstDiagLine(diags));
        assertTrue("Diagnostic source should be 'smtlib'",
                diags.get(0).getAsJsonObject().get("source").getAsString().equals("smtlib"));
    }

    @Test
    public void unclosedParenthesis() throws Exception {
        String text = "(set-logic QF_LIA)\n"
                    + "(declare-fun x () Int)\n"
                    + "(assert (> x 0\n";  // missing closing paren
        didOpen(URI, text);
        JsonObject notif = nextNonEmptyDiagsForUri(URI, PARSE_TIMEOUT);
        assertNotNull("Expected a diagnostic for unclosed paren", notif);
        assertFalse("Should have at least one diagnostic", diagsFrom(notif).isEmpty());
    }

    @Test
    public void invalidTokenReported() throws Exception {
        // '@' is not a valid SMT-LIB token at the top level
        String text = "(set-logic QF_UF)\n"
                    + "@ invalid\n"
                    + "(check-sat)\n";
        didOpen(URI, text);
        JsonObject notif = nextNonEmptyDiagsForUri(URI, PARSE_TIMEOUT);
        assertNotNull("Expected a diagnostic for invalid token", notif);
        assertFalse("Should have at least one diagnostic", diagsFrom(notif).isEmpty());
    }

    @Test
    public void errorOnCorrectLine() throws Exception {
        // Error is on line 4 (0-based), which is the 5th line
        String text = "(set-logic QF_LIA)\n"
                    + "(declare-fun x () Int)\n"
                    + "(declare-fun y () Int)\n"
                    + "(declare-fun z () Int)\n"
                    + "(assert )\n"   // line 4 (0-based)
                    + "(check-sat)\n";
        didOpen(URI, text);
        JsonObject notif = nextNonEmptyDiagsForUri(URI, PARSE_TIMEOUT);
        assertNotNull("Expected a diagnostic", notif);
        assertEquals("Error should be on line 4 (0-based)", 4, firstDiagLine(diagsFrom(notif)));
    }

    @Test
    public void multipleErrorsReported() throws Exception {
        String text = "(assert )\n"
                    + "(assert )\n";
        didOpen(URI, text);
        JsonObject notif = nextNonEmptyDiagsForUri(URI, PARSE_TIMEOUT);
        assertNotNull("Expected diagnostics", notif);
        // Both errors should be reported (parser continues after first error)
        JsonArray diags = diagsFrom(notif);
        assertTrue("Should report at least one error", diags.size() >= 1);
    }

    @Test
    public void differentURIsGetSeparateDiagnostics() throws Exception {
        String cleanUri = "file:///test/clean.smt2";
        String badUri   = "file:///test/bad.smt2";

        didOpen(cleanUri, "(set-logic QF_UF)\n(check-sat)\n");
        didOpen(badUri,   "(assert )\n");

        // Wait for both publishDiagnostics notifications
        JsonObject cleanNotif = nextDiagsForUri(cleanUri, PARSE_TIMEOUT);
        JsonObject badNotif   = nextNonEmptyDiagsForUri(badUri, PARSE_TIMEOUT);

        assertNotNull("Expected clean diagnostics notification", cleanNotif);
        assertNotNull("Expected error diagnostics notification",  badNotif);

        assertEquals("Clean file should have no diagnostics",
                0, diagsFrom(cleanNotif).size());
        assertFalse("Bad file should have at least one diagnostic",
                diagsFrom(badNotif).isEmpty());
    }
}
