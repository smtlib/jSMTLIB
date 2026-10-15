package org.smtlib.test;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.io.PrintStream;

/** Standalone helper process, launched by SolverProcessLateCommentBugTest, that mimics z3's
 *  diagnostic comment lines written after a response, but late. Answers each input line
 *  "ask" with "unsupported", and any other line with "success". After "unsupported":
 *  with --stderr-split, writes a comment line to stderr in two parts, the second after a
 *  delay; with --stdout-late, writes comment lines to stdout after a delay.
 *
 *  Not a JUnit test itself (see EchoProcess on why that annotation is not named here). */
public class LateCommentProcess {

    public static final long DELAY_MILLIS = 300;

    public static void main(String[] args) throws Exception {
        boolean stderrSplit = args.length > 0 && args[0].equals("--stderr-split");
        PrintStream out = System.out;
        PrintStream err = System.err;
        BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
        String line;
        int n = 0;
        while ((line = in.readLine()) != null) {
            n++;
            if (!line.equals("ask")) {
                out.print("success\n");
                out.flush();
                continue;
            }
            out.print("unsupported\n");
            out.flush();
            Thread.sleep(DELAY_MILLIS);
            if (stderrSplit) {
                err.print("; :all-statistics line: " + n + " position: ");
                err.flush();
                Thread.sleep(DELAY_MILLIS);
                err.print("0\n");
                err.flush();
            } else {
                out.print("; Supported get-info parameters:\n; (get-info :status)\n");
                out.flush();
            }
        }
    }
}
