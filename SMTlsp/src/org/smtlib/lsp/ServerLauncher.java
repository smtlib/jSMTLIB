package org.smtlib.lsp;

import org.eclipse.lsp4j.launch.LSPLauncher;
import org.eclipse.lsp4j.services.LanguageClient;

import java.io.PrintStream;
import java.util.concurrent.ExecutionException;

/**
 * Entry point for the SMT-LIB LSP server jar.
 *
 * Captures real stdout before redirecting System.out to stderr so that
 * library output never corrupts the LSP wire stream, then blocks until
 * the client disconnects.
 */
public class ServerLauncher {

    private static final String VERSION = "0.1";

    private static final String HELP =
            "smtlib-lsp " + VERSION + "\n"
            + "Usage: smtlib-lsp [--version] [--help]\n"
            + "  Starts an SMT-LIB 2 LSP server communicating via stdin/stdout.\n"
            + "  Intended to be launched by an LSP client (VS Code, Neovim, etc.).\n"
            + "  No other options are recognized.";

    public static void main(String[] args) throws ExecutionException, InterruptedException {
        for (String arg : args) {
            switch (arg) {
                case "--version" -> { System.out.println("smtlib-lsp " + VERSION); return; }
                case "--help"    -> { System.out.println(HELP); return; }
                default -> {
                    if (arg.startsWith("-"))
                        System.err.println("smtlib-lsp: unknown option '" + arg + "' (ignored)");
                }
            }
        }

        // Capture the real stdout BEFORE redirecting so LSP wire traffic is not
        // mixed with any library output that goes to System.out.
        PrintStream lspOut = System.out;
        System.setOut(System.err);

        var server   = new SMTLanguageServer();
        var launcher = LSPLauncher.createServerLauncher(server, System.in, lspOut, false, null);
        LanguageClient client = launcher.getRemoteProxy();
        server.connect(client);

        launcher.startListening().get();
    }
}
