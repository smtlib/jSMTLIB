package org.smtlib.test;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import org.junit.Assert;
import org.junit.Assume;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.ParameterizedWithNames;
import org.junit.runners.Parameterized.Parameters;
import org.smtlib.SMT;

@RunWith(ParameterizedWithNames.class)
public class FileTests extends LogicTests {

    // Per-test timeout is inherited from LogicTests (shared with InfoOptions/LogicsBadPath,
    // the other solver-talking subclasses).

    // Platform strings matching the bash setup script conventions
    private static final String PLATFORM;
    private static final String PLATFORM_ARCH;

    static {
        String os = System.getProperty("os.name").toLowerCase();
        String platform;
        if (os.contains("win"))      platform = "windows";
        else if (os.contains("mac")) platform = "macos";
        else                         platform = "linux";
        PLATFORM = platform;

        String arch = System.getProperty("os.arch").toLowerCase();
        String archTag = (arch.contains("aarch64") || arch.contains("arm64")) ? "arm64" : "x64";
        PLATFORM_ARCH = platform + "-" + archTag;
    }

    // -----------------------------------------------------------------------
    // Parameter discovery
    // -----------------------------------------------------------------------

    @Parameters
    public static Collection<String[]> datax() {
        Collection<String[]> data = new ArrayList<String[]>();
        File testsDir = findTestsFolder();
        List<File> tstFiles = new ArrayList<File>();
        collectTstFiles(testsDir, tstFiles);
        for (File f : tstFiles) {
            for (String solver : solvers) {
                data.add(new String[]{solver, f.getAbsolutePath()});
            }
        }
        return data;
    }

    private static File findTestsFolder() {
        try {
            String resource = FileTests.class.getClassLoader().getResource("err_array.tst").getPath();
            return new File(resource).getParentFile();
        } catch (Exception e) {
            return new File("tests");
        }
    }

    private static void collectTstFiles(File dir, List<File> result) {
        File[] entries = dir.listFiles();
        if (entries == null) return;
        Arrays.sort(entries);
        for (File entry : entries) {
            if (entry.isDirectory()) {
                collectTstFiles(entry, result);
            } else if (entry.getName().endsWith(".tst")) {
                result.add(entry);
            }
        }
    }

    // -----------------------------------------------------------------------
    // Constructor and setup
    // -----------------------------------------------------------------------

    private final File tstFile;

    public FileTests(String solvername, String tstFilePath) {
        this.solvername = solvername;
        this.tstFile = new File(tstFilePath);
    }

    @Override
    public void init() {
        smt = new SMT();
        smt.props = readPropertiesAndAddDefaults(smt);
        smt.smtConfig.solvername = solvername;
        // solver is started lazily by exec()
    }

    @Override
    public void teardown() {
        if (smt != null) smt.cleanup();
    }

    // -----------------------------------------------------------------------
    // Test body
    // -----------------------------------------------------------------------

    @Test
    public void checkFile() {
        checkSkip();

        ByteArrayOutputStream outBuf = new ByteArrayOutputStream();
        ByteArrayOutputStream errBuf = new ByteArrayOutputStream();
        PrintStream outPs = new PrintStream(outBuf);
        PrintStream errPs = new PrintStream(errBuf);
        smt.smtConfig.log.out = outPs;
        smt.smtConfig.log.diag = errPs;
        smt.smtConfig.stdout = outPs;
        smt.smtConfig.stderr = errPs;

        // Use text mode so error position messages carry no file path,
        // matching the format of existing golden files.
        try {
            smt.smtConfig.text = new String(Files.readAllBytes(tstFile.toPath()));
        } catch (IOException e) {
            Assert.fail("Cannot read test file: " + tstFile + ": " + e);
            return;
        }

        smt.exec();
        outPs.flush();
        errPs.flush();

        String actualOut = outBuf.toString().replace("\r\n", "\n");
        String actualErr = errBuf.toString().replace("\r\n", "\n");

        // stdout: filter (:memory lines (memory usage varies between runs)
        compareOutput(".out", findGoldenFile(".out"), actualOut, true);
        // stderr: exact match
        compareOutput(".err", findGoldenFile(".err"), actualErr, false);
    }

    // -----------------------------------------------------------------------
    // Skip logic
    // -----------------------------------------------------------------------

    /** A "family" fallback lets several versions of the same solver (e.g. z3-4.8.12,
     *  z3-4.10.2) share one golden file instead of duplicating identical content per
     *  exact version: strips a trailing "-N..." or "_N..." version suffix (e.g.
     *  "z3-4.8.12" -&gt; "z3", "z3-4.3" -&gt; "z3", "cvc5-1.3.2" -&gt; "cvc5"). Returns null
     *  if the name has no such suffix (e.g. "yices2", "test") -- family is only used
     *  when it differs from the exact solver name.
     *  IMPORTANT: this must stay in sync with the "family=..." computation in
     *  SMTTests/runtest. If you change the rule here, change it there too, and vice versa. */
    private static String family(String name) {
        String f = name.replaceAll("[_-][0-9].*$", "");
        return f.equals(name) ? null : f;
    }

    private void checkSkip() {
        String base = tstFile.getAbsolutePath();
        String family = family(solvername);
        List<String> suffixes = new ArrayList<String>(Arrays.asList(
            ".skip." + solvername + "." + PLATFORM_ARCH,
            ".skip." + solvername + "." + PLATFORM,
            ".skip." + solvername
        ));
        if (family != null) {
            suffixes.add(".skip." + family + "." + PLATFORM_ARCH);
            suffixes.add(".skip." + family + "." + PLATFORM);
            suffixes.add(".skip." + family);
        }
        suffixes.add(".skip." + PLATFORM_ARCH);
        suffixes.add(".skip." + PLATFORM);
        suffixes.add(".skip");
        for (String suffix : suffixes) {
            File skipFile = new File(base + suffix);
            if (skipFile.exists()) {
                Assume.assumeTrue("Skip (" + suffix + "): " + readFirstLine(skipFile), false);
            }
        }
    }

    // -----------------------------------------------------------------------
    // Golden file lookup
    // IMPORTANT: this priority order must stay in sync with the two 'for f in ...'
    // loops in SMTTests/runtest (one for .err, one for .out).  If you change the
    // order here, change it there too, and vice versa.
    // -----------------------------------------------------------------------

    private File findGoldenFile(String ext) {
        String base = tstFile.getAbsolutePath();
        String family = family(solvername);
        List<String> candidates = new ArrayList<String>(Arrays.asList(
            base + ext + "." + solvername + "." + PLATFORM_ARCH,
            base + ext + "." + solvername + "." + PLATFORM,
            base + ext + "." + solvername,
            base + ext + "." + solvername + ".bad"
        ));
        if (family != null) {
            candidates.add(base + ext + "." + family);
            candidates.add(base + ext + "." + family + ".bad");
        }
        candidates.add(base + ext + "." + PLATFORM_ARCH);
        candidates.add(base + ext + "." + PLATFORM);
        candidates.add(base + ext);
        for (String c : candidates) {
            File f = new File(c);
            if (f.exists()) return f;
        }
        return null;
    }

    // -----------------------------------------------------------------------
    // Comparison
    // -----------------------------------------------------------------------

    private void compareOutput(String ext, File golden, String actual, boolean normalize) {
        // No golden file: OK only if actual output is empty (matches runtest .err behaviour;
        // for .out an absent golden file is always a failure).
        if (golden == null || !golden.exists()) {
            if (!actual.trim().isEmpty()) {
                writeActual(ext, actual);
                Assert.fail("No golden " + ext + " file for " + tstFile.getName()
                        + " but actual output is:\n" + actual);
            }
            return;
        }

        String expected;
        try {
            expected = new String(Files.readAllBytes(golden.toPath())).replace("\r\n", "\n");
        } catch (IOException e) {
            Assert.fail("Cannot read golden file " + golden + ": " + e);
            return;
        }

        String cmpExpected = normalize ? filterMemoryLines(expected) : expected;
        String cmpActual   = normalize ? filterMemoryLines(actual)   : actual;
        cmpExpected = filterIOExceptionLines(cmpExpected);
        cmpActual   = filterIOExceptionLines(cmpActual);

        if (!cmpExpected.equals(cmpActual)) {
            writeActual(ext, actual);
            Assert.assertEquals(
                tstFile.getName() + " / " + solvername + " " + ext,
                cmpExpected, cmpActual);
        }
        // On success: do not write .actual (and delete any stale one)
        new File(actualPath(ext)).delete();
    }

    /** Drops lines containing {@code java.io.IOException:} -- these appear in an "Error
     *  writing to solver: ..." response when a script keeps sending commands to a solver
     *  process that has already exited/closed its pipe (e.g. after an unsupported
     *  construct kills it). The exact message text ("Stream closed", "Broken pipe",
     *  etc.) depends on OS-level timing of the underlying pipe failure and is not
     *  reproducible run to run, even for the identical script against the identical
     *  solver binary -- same non-determinism, same "drop the line" treatment as
     *  {@link #filterMemoryLines}. */
    private static String filterIOExceptionLines(String s) {
        StringBuilder sb = new StringBuilder();
        for (String line : s.split("\n", -1)) {
            if (!line.contains("java.io.IOException:")) sb.append(line).append('\n');
        }
        return sb.toString();
    }

    /** Drops lines containing {@code (:memory} or {@code (:max-memory} — memory usage varies between runs. */
    private static String filterMemoryLines(String s) {
        StringBuilder sb = new StringBuilder();
        for (String line : s.split("\n", -1)) {
            if (!line.contains("(:memory") && !line.contains("(:max-memory")) sb.append(line).append('\n');
        }
        return sb.toString();
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /** Path for the actual-output capture file for this (test, solver, ext) combination --
     *  named the same way a custom golden file would be (base + ext + "." + solvername),
     *  plus ".actual", so that distinct solvers tested against the same .tst file never
     *  share (and clobber) one another's capture file. */
    private String actualPath(String ext) {
        return tstFile.getAbsolutePath() + ext + "." + solvername + ".actual";
    }

    private void writeActual(String ext, String content) {
        File out = new File(actualPath(ext));
        try (BufferedWriter w = new BufferedWriter(new FileWriter(out))) {
            w.write(content);
        } catch (IOException ignored) {}
    }

    private static String readFirstLine(File f) {
        try (BufferedReader r = new BufferedReader(new FileReader(f))) {
            String line = r.readLine();
            return line != null ? line : "";
        } catch (IOException e) {
            return f.getName();
        }
    }
}
