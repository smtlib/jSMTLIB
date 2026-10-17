package org.smtlib.test;

import java.io.InputStreamReader;
import java.io.Reader;
import java.nio.file.Files;
import java.nio.file.Paths;

/** A stand-in solver for FileTests' .stub tests (#145): its argument is a plain-text file of
 *  replies, one line per command received (including any priming command the adapter sends
 *  first), in order. An empty line is an empty reply; {@code <<stderr>> text} writes the text
 *  to standard error instead; {@code <<exit N>>} ends the process with code N right after the
 *  reply before it (or at once, as the first line). The process also ends after replying to
 *  (exit), or when the replies run out.
 *
 *  Not a JUnit test itself (see EchoProcess on why that annotation is not named here). */
public class StubSolver {
    public static void main(String[] args) throws Exception {
        java.util.List<String> replies = Files.readAllLines(Paths.get(args[0]));
        int next = exitIfAt(replies, 0);
        Reader in = new InputStreamReader(System.in);
        StringBuilder command = new StringBuilder();
        int depth = 0;
        char quote = 0;
        int c;
        while ((c = in.read()) != -1) {
            if (depth == 0 && c != '(') {
                if (c == ';') while ((c = in.read()) != -1 && c != '\n') {}
                continue;
            }
            command.append((char)c);
            if (quote != 0) {
                if (c == quote) quote = 0;
            } else if (c == '"' || c == '|') {
                quote = (char)c;
            } else if (c == '(') {
                depth++;
            } else if (c == ')' && --depth == 0) {
                if (next >= replies.size()) return;
                reply(replies.get(next));
                next = exitIfAt(replies, next + 1);
                if (command.toString().startsWith("(exit")) return;
                command.setLength(0);
            }
        }
    }

    /** Ends the process if line i is an exit directive; else returns i */
    private static int exitIfAt(java.util.List<String> replies, int i) {
        if (i < replies.size()) {
            String line = replies.get(i);
            if (line.startsWith("<<exit ") && line.endsWith(">>")) {
                System.out.flush();
                System.err.flush();
                System.exit(Integer.parseInt(line.substring(7, line.length() - 2).trim()));
            }
        }
        return i;
    }

    private static void reply(String line) {
        if (line.startsWith("<<stderr>>")) {
            System.err.println(line.substring(10).trim());
            System.err.flush();
        } else {
            System.out.print(line + "\n");
            System.out.flush();
        }
    }
}
