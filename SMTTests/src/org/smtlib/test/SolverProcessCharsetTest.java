package org.smtlib.test;

import java.io.File;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

import org.junit.After;
import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.SolverProcess;

/** Tests for SolverProcess's charset handling and for the robustness of its stdout/stderr
 *  gobbler threads against malformed input. Talks to {@link EchoProcess}, a byte-transparent
 *  echo child, rather than a real solver, so these tests isolate SolverProcess's own
 *  encode/decode machinery instead of depending on a solver being installed or on a solver's
 *  own encoding quirks. */
public class SolverProcessCharsetTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    private SolverProcess sp;

    @After
    public void tearDown() {
        if (sp != null) sp.exit();
    }

    /** Command line that launches EchoProcess via the current JVM and classpath, so the test
     *  does not depend on `cat` or any other OS-specific utility being available. */
    private static String[] echoCmd(String... flags) {
        String javaBin = System.getProperty("java.home") + File.separator + "bin" + File.separator + "java";
        List<String> cmd = new ArrayList<String>();
        cmd.add(javaBin);
        cmd.add("-cp");
        cmd.add(System.getProperty("java.class.path"));
        cmd.add("org.smtlib.test.EchoProcess");
        for (String f : flags) cmd.add(f);
        return cmd.toArray(new String[0]);
    }

    // A payload mixing 1-byte (ASCII), 2-byte (e-acute), 3-byte (CJK), and 4-byte
    // (surrogate-pair astral emoji) UTF-8 sequences, per the SMT-LIB standard's own
    // description of source text as "Unicode characters in any 8-bit encoding, such as UTF-8".
    private static final String MIXED_UNICODE_PAYLOAD = "hello café 中 🙂";

    // -----------------------------------------------------------------------
    // Charset defaulting / plumbing
    // -----------------------------------------------------------------------

    @Test
    public void defaultCharset_isJvmPlatformDefault() {
        sp = new SolverProcess(echoCmd(), "\n", null);
        Assert.assertEquals(Charset.defaultCharset(), sp.getCharset());
    }

    /** Uses UTF-16, not UTF-8, deliberately: plain ASCII (or content that happens to match the
     *  platform default) would round-trip correctly even if the charset parameter were silently
     *  ignored on a CI box whose platform default is already UTF-8. UTF-16 is byte-incompatible
     *  enough that a round trip only succeeds if the parameter is genuinely wired into both the
     *  outbound writer and the inbound reader. */
    @Test
    public void explicitCharset_isUsedNotIgnored() throws Exception {
        sp = new SolverProcess(echoCmd(), "\n", null, StandardCharsets.UTF_16);
        sp.start(false);
        String heard = sp.sendAndListen(MIXED_UNICODE_PAYLOAD + "\n");
        Assert.assertEquals(MIXED_UNICODE_PAYLOAD, heard);
    }

    @Test
    public void utf8RoundTrip_multibyteContent() throws Exception {
        sp = new SolverProcess(echoCmd(), "\n", null, StandardCharsets.UTF_8);
        sp.start(false);
        String heard = sp.sendAndListen(MIXED_UNICODE_PAYLOAD + "\n");
        Assert.assertEquals(MIXED_UNICODE_PAYLOAD, heard);
    }

    // -----------------------------------------------------------------------
    // Robustness against malformed (non-UTF-8) bytes
    // -----------------------------------------------------------------------

    /** A stray invalid UTF-8 byte ahead of the recognized end marker on stdout must not throw
     *  or hang the listener -- it should decode to the Unicode replacement character and the
     *  rest of the response should still be recognized normally. This is the regression test
     *  for relying on the default CodingErrorAction.REPLACE (rather than REPORT), which is what
     *  lets a single bad byte from a solver never crash or wedge the gobbler thread. */
    @Test
    public void malformedBytesOnStdout_doNotHangOrThrow() throws Exception {
        sp = new SolverProcess(echoCmd("--malformed-stdout"), "\n", null, StandardCharsets.UTF_8);
        sp.start(false);
        String heard = sp.sendAndListen("ping\n");
        Assert.assertTrue("expected a Unicode replacement character in: " + heard,
                heard.indexOf('�') >= 0);
        Assert.assertTrue("expected the rest of the response to still be recognized: " + heard,
                heard.endsWith("ping"));
    }

    /** Same malformed-byte injection, but on stderr. Unlike the stdout case, there is no
     *  end-marker on stderr, and no guarantee the malformed byte's error-stream chunk has been
     *  queued by the time listen() drains it (that correlation is a documented best-effort
     *  heuristic, not something either SolverProcess or this test can guarantee) -- so this
     *  does not assert on the malformed byte appearing in any particular response. What it does
     *  assert is the thing that actually matters: an invalid byte on stderr must not throw or
     *  hang, and the session must remain fully usable for subsequent, unrelated commands
     *  afterward -- i.e. the stderr gobbler thread was not silently killed by an uncaught
     *  decoding exception. */
    @Test
    public void malformedBytesOnStderr_doesNotKillGobblerThread() throws Exception {
        sp = new SolverProcess(echoCmd("--malformed-stderr"), "\n", null, StandardCharsets.UTF_8);
        sp.start(false);
        sp.sendAndListen("ping\n");
        String heard2 = sp.sendAndListen("pong\n");
        Assert.assertEquals("pong", heard2);
    }
}
