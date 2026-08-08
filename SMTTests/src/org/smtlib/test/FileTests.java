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
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Assume;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.junit.runner.RunWith;
import org.junit.runners.ParameterizedWithNames;
import org.junit.runners.Parameterized.Parameters;
import org.smtlib.SMT;

@RunWith(ParameterizedWithNames.class)
public class FileTests extends LogicTests {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

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

    private static final String[] SOLVERS = { "test", "z3_4_3" };

    @Parameters
    public static Collection<String[]> datax() {
        Collection<String[]> data = new ArrayList<String[]>();
        File testsDir = findTestsFolder();
        List<File> tstFiles = new ArrayList<File>();
        collectTstFiles(testsDir, tstFiles);
        for (File f : tstFiles) {
            for (String solver : SOLVERS) {
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

    private void checkSkip() {
        String base = tstFile.getAbsolutePath();
        String[] suffixes = {
            ".skip." + solvername + "." + PLATFORM_ARCH,
            ".skip." + solvername + "." + PLATFORM,
            ".skip." + solvername,
            ".skip." + PLATFORM_ARCH,
            ".skip." + PLATFORM,
            ".skip"
        };
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
        String[] candidates = {
            base + ext + "." + solvername + "." + PLATFORM_ARCH,
            base + ext + "." + solvername + "." + PLATFORM,
            base + ext + "." + solvername,
            base + ext + "." + solvername + ".bad",
            base + ext + "." + PLATFORM_ARCH,
            base + ext + "." + PLATFORM,
            base + ext,
        };
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

        if (!cmpExpected.equals(cmpActual)) {
            writeActual(ext, actual);
            Assert.assertEquals(
                tstFile.getName() + " / " + solvername + " " + ext,
                cmpExpected, cmpActual);
        }
        // On success: do not write .actual (and delete any stale one)
        new File(tstFile.getAbsolutePath() + ext + ".actual").delete();
    }

    /** Drops lines containing {@code (:memory} — memory usage varies between runs. */
    private static String filterMemoryLines(String s) {
        StringBuilder sb = new StringBuilder();
        for (String line : s.split("\n", -1)) {
            if (!line.contains("(:memory")) sb.append(line).append('\n');
        }
        return sb.toString();
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    private void writeActual(String ext, String content) {
        File out = new File(tstFile.getAbsolutePath() + ext + ".actual");
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
