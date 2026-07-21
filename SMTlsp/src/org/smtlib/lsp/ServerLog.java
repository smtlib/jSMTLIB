package org.smtlib.lsp;

/**
 * Minimal logging to stderr (not stdout, which carries the LSP wire stream).
 */
public class ServerLog {

    private ServerLog() {}

    public static void serverLog(String message) {
        System.err.println("[smtlib-lsp] " + message);
    }
}
