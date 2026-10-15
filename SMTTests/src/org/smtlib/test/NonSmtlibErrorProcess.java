package org.smtlib.test;

import java.io.InputStreamReader;
import java.io.Reader;

/** Standalone helper process, launched by NonSmtlibResponseBugTest, that acts as an SMT-LIB solver
 *  except that it answers an assert with an error in bitwuzla's non-SMT-LIB form
 *  ("[error] ..."), check-sat with "sat", and every other command with "success". Commands are
 *  read as balanced parenthesized text, since they need not end in a newline.
 *
 *  Not a JUnit test itself (see EchoProcess on why that annotation is not named here). */
public class NonSmtlibErrorProcess {
    public static void main(String[] args) throws Exception {
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
                String answer = text.startsWith("(assert") ? "[error] <stdin>:2:9: expected Bool term"
                        : text.startsWith("(check-sat") ? "sat" : "success";
                System.out.print(answer + "\n");
                System.out.flush();
            }
        }
    }
}
