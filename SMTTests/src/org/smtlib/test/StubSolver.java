package org.smtlib.test;

import java.io.InputStreamReader;
import java.io.Reader;
import java.nio.file.Files;
import java.nio.file.Paths;

/** A stand-in solver for FileTests' .stub tests (#145): its argument is a plain-text file of
 *  replies, one line per command received (including any priming command the adapter sends
 *  first), in order. An empty line is an empty reply; {@code <<stderr>> text} writes the text
 *  to standard error instead. Directive lines act right after the reply before them (or at once,
 *  as the first lines) and answer no command: {@code <<exit N>>} ends the process with code N,
 *  {@code <<close-stdout>>} closes standard output, {@code <<sleep N>>} pauses N milliseconds.
 *  The process also ends after replying to (exit), or when the replies run out.
 *
 *  Not a JUnit test itself (see EchoProcess on why that annotation is not named here). */
public class StubSolver {
    public static void main(String[] args) throws Exception {
        java.util.List<String> replies = Files.readAllLines(Paths.get(args[0]));
        int next = directives(replies, 0);
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
                next = directives(replies, next + 1);
                if (command.toString().startsWith("(exit")) return;
                command.setLength(0);
            }
        }
    }

    /** Carries out the directives starting at line i; returns the index of the next reply */
    private static int directives(java.util.List<String> replies, int i) throws InterruptedException {
        for (; i < replies.size(); i++) {
            String line = replies.get(i);
            if (line.startsWith("<<exit ") && line.endsWith(">>")) {
                System.out.flush();
                System.err.flush();
                System.exit(Integer.parseInt(line.substring(7, line.length() - 2).trim()));
            } else if (line.equals("<<close-stdout>>")) {
                System.out.close();
            } else if (line.startsWith("<<sleep ") && line.endsWith(">>")) {
                Thread.sleep(Long.parseLong(line.substring(8, line.length() - 2).trim()));
            } else {
                break;
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
