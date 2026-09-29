package org.smtlib.test;

import java.io.File;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.lang.reflect.Method;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.HashSet;
import java.util.Set;

import org.junit.runner.Description;
import org.junit.runner.Result;
import org.junit.runner.notification.Failure;
import org.junit.runner.notification.RunListener;

/** JUnit RunListener that splits JaCoCo coverage by test case: each test's own coverage is
 *  written to its own .exec file under a per-test directory, instead of everything
 *  accumulating into one destfile for the whole run (what `make cov-test` does).
 *
 *  Mechanism: JaCoCo's runtime API ({@code org.jacoco.agent.rt.RT.getAgent()}) exposes
 *  {@code getExecutionData(reset)} and {@code dump(reset)}, which read out -- and zero --
 *  the probe counters of the running JVM. So:
 *  <ul>
 *  <li>at testStarted, whatever ran since the previous test (class loading, static
 *      initializers, @Parameters/@BeforeClass methods) is dumped, with a reset, to the
 *      agent's own destfile (setup-coverage points that at _outside-tests.exec);</li>
 *  <li>at testFinished, the counters -- now exactly this one test's coverage -- are
 *      read out, with a reset, and appended to that test's own file.</li>
 *  </ul>
 *  Anything left after the last test is written to _outside-tests.exec by the agent's own
 *  shutdown hook, as usual.
 *
 *  Child JVMs (ScriptTests' $SMT_CMD/$SMT_DRIVER invocations, via runscript) can't be
 *  reset from here. Instead, this listener writes the current test's file stem to
 *  {@code <dir>/.current-test}; runscript substitutes it into the child agent's destfile,
 *  so each child JVM appends its own session to the same per-test file. JaCoCo's exec
 *  format is a sequence of blocks, so several sessions appended to one file read back
 *  (and merge) as a single data set.
 *
 *  An index.tsv alongside the .exec files maps each file back to its test (class, JUnit
 *  display name, outcome, wall-clock ms), since the file stems are sanitized names.
 *
 *  JaCoCo is reached only reflectively, so this class compiles and loads without the
 *  agent jar on the classpath; if no agent is attached it disables itself with a warning.
 *  Requires tests to run sequentially in this JVM -- the counters are per-JVM, so
 *  concurrently running tests would be credited with each other's coverage (see the
 *  CAUTION in README.md; RunAll runs the classes sequentially).
 */
public class PerTestCoverageListener extends RunListener {

    /** Agent session id used for everything that runs outside any test. */
    static final String OUTSIDE_TESTS = "_outside-tests";

    private final File dir;
    private final PrintWriter index;
    private final Object agent;
    private final Method getExecutionData;
    private final Method dump;
    private final Method setSessionId;

    private final String cwdPrefix = new File(System.getProperty("user.dir")).getAbsolutePath() + File.separator;
    private final Set<String> usedStems = new HashSet<String>();
    private String currentStem;
    private String currentStatus;
    private long startMillis;

    /** Returns a listener writing under [dir], or null if no JaCoCo agent is attached. */
    public static PerTestCoverageListener create(File dir) throws IOException {
        Object agent;
        try {
            Class<?> rt = Class.forName("org.jacoco.agent.rt.RT");
            agent = rt.getMethod("getAgent").invoke(null);
        } catch (ReflectiveOperationException | LinkageError e) {
            System.err.println("WARNING: per-test coverage requested but no JaCoCo agent is attached ("
                    + e + "); per-test coverage disabled");
            return null;
        }
        return new PerTestCoverageListener(dir, agent);
    }

    private PerTestCoverageListener(File dir, Object agent) throws IOException {
        this.dir = dir;
        this.agent = agent;
        try {
            // Looked up on the public interface, not agent.getClass(): the agent's
            // implementation class is package-private, so its own Method objects
            // aren't invocable from here.
            Class<?> iAgent = Class.forName("org.jacoco.agent.rt.IAgent");
            getExecutionData = iAgent.getMethod("getExecutionData", boolean.class);
            dump = iAgent.getMethod("dump", boolean.class);
            setSessionId = iAgent.getMethod("setSessionId", String.class);
        } catch (ReflectiveOperationException e) {
            throw new IllegalStateException("unexpected JaCoCo agent API", e);
        }
        dir.mkdirs();
        index = new PrintWriter(new FileWriter(new File(dir, "index.tsv")), true);
        index.println("file\tclass\tdisplayName\tstatus\tmillis");
        setSession(OUTSIDE_TESTS);
    }

    @Override
    public void testStarted(Description d) throws Exception {
        invoke(dump, true); // everything since the previous test goes to _outside-tests.exec
        currentStem = uniqueStem(d);
        currentStatus = "PASS";
        startMillis = System.currentTimeMillis();
        writeCurrentTest(currentStem);
        setSession(currentStem);
    }

    @Override
    public void testFailure(Failure f) {
        currentStatus = "FAIL";
    }

    /** Fires for Assume.assumeTrue(false) -- how FileTests.checkSkip() implements a skip. */
    @Override
    public void testAssumptionFailure(Failure f) {
        currentStatus = "SKIP";
    }

    @Override
    public void testFinished(Description d) throws Exception {
        long millis = System.currentTimeMillis() - startMillis;
        byte[] data = (byte[]) invoke(getExecutionData, true);
        String file = currentStem + ".exec";
        // Append, not overwrite: this test's child JVMs (if any) have already written
        // their own sessions to this same file.
        try (OutputStream out = new FileOutputStream(new File(dir, file), true)) {
            out.write(data);
        }
        index.println(file + "\t" + d.getClassName() + "\t" + d.getDisplayName()
                + "\t" + currentStatus + "\t" + millis);
        writeCurrentTest(OUTSIDE_TESTS);
        setSession(OUTSIDE_TESTS);
        currentStem = null;
    }

    @Override
    public void testRunFinished(Result result) {
        index.close();
    }

    /** A file stem for [d], unique within this run: the test class's simple name plus the
     *  method/parameter part of JUnit's display name, reduced to filename-safe characters.
     *  Parameterized tests often carry an absolute path in their parameters (e.g.
     *  ScriptTests' .scr path); the working-directory prefix is dropped so stems are the
     *  same on every machine and checkout. Two display names that sanitize to the same
     *  stem get a numeric suffix. */
    private String uniqueStem(Description d) {
        String cls = d.getTestClass() != null ? d.getTestClass().getSimpleName() : d.getClassName();
        String method = d.getMethodName() != null ? d.getMethodName() : d.getDisplayName();
        method = method.replace(cwdPrefix, "");
        String base = sanitize(cls + "." + method);
        String stem = base;
        for (int n = 2; !usedStems.add(stem); n++) {
            stem = base + "~" + n;
        }
        return stem;
    }

    static String sanitize(String s) {
        String r = s.replaceAll("[^A-Za-z0-9._-]+", "_");
        // Keep stems comfortably under common 255-byte filename limits.
        return r.length() > 180 ? r.substring(0, 180) : r;
    }

    private void writeCurrentTest(String stem) throws IOException {
        Files.write(new File(dir, ".current-test").toPath(), stem.getBytes(StandardCharsets.UTF_8));
    }

    private void setSession(String id) {
        invoke(setSessionId, id);
    }

    private Object invoke(Method m, Object arg) {
        try {
            return m.invoke(agent, arg);
        } catch (ReflectiveOperationException e) {
            throw new IllegalStateException("JaCoCo agent call " + m.getName() + " failed", e);
        }
    }
}
