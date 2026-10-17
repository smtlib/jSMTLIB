package org.smtlib.test;

import java.io.InputStreamReader;
import java.io.Reader;

/** Standalone helper process, launched by FlatResponseTests, that acts as an SMT-LIB solver
 *  whose structured commands get flat replies: get-assertions "success", get-value an empty
 *  line, get-assignment and get-unsat-assumptions "unsupported", get-unsat-core "success".
 *  check-sat answers its argument (sat or unsat), get-option "true", every other command
 *  "success". Commands are read as balanced parenthesized text.
 *
 *  Not a JUnit test itself (see EchoProcess on why that annotation is not named here). */
public class FlatAnswerProcess {
    public static void main(String[] args) throws Exception {
        String checkSat = args.length > 0 ? args[0] : "sat";
        Reader in = new InputStreamReader(System.in);
        StringBuilder command = new StringBuilder();
        int depth = 0;
        int c;
        while ((c = in.read()) != -1) {
            if (depth == 0 && c != '(') continue;
            command.append((char)c);
            if (c == '(') depth++;
            else if (c == ')' && --depth == 0) {
                String text = command.toString();
                command.setLength(0);
                if (text.startsWith("(exit")) break;
                String answer = text.startsWith("(check-sat") ? checkSat
                        : text.startsWith("(get-option") ? "true"
                        : text.startsWith("(get-value") ? ""
                        : text.startsWith("(get-assignment") || text.startsWith("(get-unsat-assumptions") ? "unsupported"
                        : "success";
                System.out.print(answer + "\n");
                System.out.flush();
            }
        }
    }
}
