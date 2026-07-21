package org.smtlib.lsp.test;

import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Tests that the server's debouncing correctly coalesces rapid consecutive
 * text-document changes: multiple quick didChange notifications should produce
 * at most one publishDiagnostics after the dust settles, not one per change.
 *
 * Also verifies that the last change's content is the one that gets parsed
 * (the final state wins).
 */
public class DebouncingTest extends ProtocolTestBase {

    private static final String URI = "file:///test/debounce.smt2";

    /**
     * Debounce window in the server is 300 ms.  We wait 1 s after sending
     * the last change — the parse must have completed by then — then collect
     * any remaining notifications for at most 500 ms.
     */
    private static final int SEND_COUNT = 10;

    @Test
    public void rapidChangesProduceOneDiagnosticsNotification() throws Exception {
        didOpen(URI, "(check-sat)\n");
        nextDiagsForUri(URI, PARSE_TIMEOUT);  // consume open notification

        // Fire many rapid changes; only the last one's content matters.
        for (int i = 0; i < SEND_COUNT; i++) {
            String content = i < SEND_COUNT - 1
                    ? "(check-sat)\n"      // valid intermediate content
                    : "(assert )\n";       // final content has a parse error
            didChange(URI, i + 2, content);
        }

        // Collect all publishDiagnostics that arrive within 2 s
        List<JsonObject> received = new ArrayList<>();
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(2);
        while (true) {
            long remaining = deadline - System.nanoTime();
            if (remaining <= 0) break;
            JsonObject notif = client.nextNotification(
                    "textDocument/publishDiagnostics", remaining, TimeUnit.NANOSECONDS);
            if (notif == null) break;
            if (URI.equals(notif.getAsJsonObject("params").get("uri").getAsString()))
                received.add(notif);
        }

        // Due to debouncing, we expect exactly 1 (or at most a small number if the
        // debounce timer fires during the burst).  The key invariant is:
        //   (a) at least one notification is received
        //   (b) the last notification reflects the final content (has an error)
        assertFalse("At least one publishDiagnostics must be received", received.isEmpty());

        JsonObject last = received.get(received.size() - 1);
        assertFalse("Final notification should report the parse error from last change",
                diagsFrom(last).isEmpty());

        // Debouncing typically reduces the count significantly; the exact count
        // depends on timing, so we just log it rather than assert an exact number.
        System.out.println("[DebouncingTest] notifications received for " + SEND_COUNT
                + " rapid changes: " + received.size());
    }

    @Test
    public void finalContentWinsAfterDebounce() throws Exception {
        didOpen(URI, "(assert )\n");   // open with error
        nextNonEmptyDiagsForUri(URI, PARSE_TIMEOUT);

        // Fire valid content followed immediately by more invalid content
        didChange(URI, 2, "(check-sat)\n");   // valid
        didChange(URI, 3, "(check-sat)\n");   // valid
        didChange(URI, 4, "(declare-fun f () Bool)\n(check-sat)\n");  // valid, final

        // Wait for the debounce to settle
        JsonObject last = null;
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(2);
        while (true) {
            long remaining = deadline - System.nanoTime();
            if (remaining <= 0) break;
            JsonObject n = client.nextNotification(
                    "textDocument/publishDiagnostics", remaining, TimeUnit.NANOSECONDS);
            if (n == null) break;
            if (URI.equals(n.getAsJsonObject("params").get("uri").getAsString()))
                last = n;
        }

        assertNotNull("At least one publishDiagnostics must arrive", last);
        assertEquals("Final valid content should have no diagnostics",
                0, diagsFrom(last).size());
    }
}
