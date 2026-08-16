package org.smtlib.test;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;

/** Standalone helper process, launched as a child process by SolverProcessCharsetTest, that
 *  echoes stdin to stdout byte-for-byte with no charset interpretation of its own -- this
 *  isolates SolverProcess's own encode/decode behavior in the test rather than conflating it
 *  with the behavior of the child. Launched via the current JVM ({@code java.home}/bin/java)
 *  and the current classpath rather than an OS utility like `cat`, so the test does not
 *  depend on what shell utilities happen to be installed on a given OS.
 *
 *  Not a JUnit test itself (declares no test methods): runjunits compiles it, since it lives
 *  under src/org/smtlib/test, but should not be picked up as a runnable test class. (Avoid
 *  writing the JUnit test annotation's name literally in this comment -- runjunits' own
 *  discovery step is a plain grep for that string in each source file, and a doc comment
 *  that merely mentions it by name is enough to trigger a false match, which is exactly
 *  what happened here before this rewording.)
 *
 *  Usage: java org.smtlib.test.EchoProcess [--malformed-stdout] [--malformed-stderr]
 *  Either flag writes a single invalid UTF-8 byte (0x80, a lone continuation byte with no
 *  leading byte) to the named stream, immediately before the first echoed chunk, so tests can
 *  check that SolverProcess's decoding survives malformed input without throwing or hanging.
 */
public class EchoProcess {
    public static void main(String[] args) throws IOException {
        boolean malformedStdout = false;
        boolean malformedStderr = false;
        for (String a : args) {
            if ("--malformed-stdout".equals(a)) malformedStdout = true;
            else if ("--malformed-stderr".equals(a)) malformedStderr = true;
        }
        InputStream in = System.in;
        OutputStream out = System.out;
        OutputStream err = System.err;
        byte[] buf = new byte[8192];
        boolean first = true;
        int n;
        while ((n = in.read(buf)) != -1) {
            if (first) {
                if (malformedStdout) { out.write(0x80); out.flush(); }
                if (malformedStderr) { err.write(0x80); err.flush(); }
                first = false;
            }
            out.write(buf, 0, n);
            out.flush();
        }
    }
}
