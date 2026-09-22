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

    // Per-test timeout is inherited from LogicTests (shared with LogicsBadPath,
    // the other solver-talking subclass).

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
        smt.smtConfig.props = readPropertiesAndAddDefaults(smt);
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
        smt.smtConfig.log.setChannels(outPs, errPs);
        smt.smtConfig.stdout = outPs;
        smt.smtConfig.stderr = errPs;
        // Scrubs known non-deterministic content (elapsed-time, memory usage) out of
        // get-info responses -- see AbstractSolver#normalizeForTesting() -- so goldens are
        // reproducible across machines and runs. Set directly rather than via a "--testing"
        // command-line argument: exec(String[]) is a plain instance method operating on this
        // SMT instance's own smtConfig, so a field set here is exactly as safe/scoped as
        // parsing a flag would be, without the plain-text default path (below) needing to
        // route through the argument parser just for this one setting.
        smt.smtConfig.testing = true;

        String text;
        try {
            text = new String(Files.readAllBytes(tstFile.toPath()));
        } catch (IOException e) {
            Assert.fail("Cannot read test file: " + tstFile + ": " + e);
            return;
        }

        List<String> options = optionsDirectiveArgs(text);
        if (options == null) {
            // Use text mode so error position messages carry no file path, matching the
            // format of existing golden files.
            smt.smtConfig.text = text;
            smt.exec();
        } else {
            // A "; OPTIONS: <flags>" directive is present: run through the real
            // SMT.exec(String[]) / processCommandLine() argument parser instead of setting
            // fields by hand here, so a .tst test exercises the same parsing path a real
            // invocation would, and gets any future flag for free. The directive is an
            // ordinary ';' comment, so the parser already ignores it on its own -- the
            // original .tst file is passed straight through, unmodified.
            options.add(tstFile.getAbsolutePath());
            smt.exec(options.toArray(new String[0]));
        }
        outPs.flush();
        errPs.flush();

        String actualOut = outBuf.toString().replace("\r\n", "\n");
        String actualErr = errBuf.toString().replace("\r\n", "\n");

        compareOutput(".out", findGoldenFile(".out"), actualOut);
        compareOutput(".err", findGoldenFile(".err"), actualErr);
    }

    /** Without a directive, checkFile() feeds a .tst file's raw content to SMT.exec()
     *  directly (via smtConfig.text), bypassing parseCommandLine()/processCommandLine()
     *  entirely -- so a plain .tst file has no way to ask for a command-line-only setting
     *  like --relax. A leading "; OPTIONS: &lt;flags&gt;" line (an ordinary SMT-LIB comment,
     *  so the parser ignores it on its own either way) lets a .tst file request that
     *  checkFile() instead route it through the real SMT.exec(String[])/
     *  processCommandLine() argument parser -- so that .tst test exercises the same
     *  parsing path a real invocation would, with no per-flag logic duplicated here, and
     *  the original file is passed straight through unmodified. Returns null (meaning:
     *  use the normal text-mode path, still bypassing processCommandLine()) if there's no
     *  directive; otherwise the flag tokens, not yet including the file argument
     *  checkFile() appends. This is a plain splitter with no per-flag knowledge -- every
     *  flag is just handed to the real parser unexamined.
     *  <p>
     *  Note for anyone writing a "; OPTIONS:" line: avoid --verbose/-v. It works
     *  mechanically, but processCommandLine() always calls readProperties() itself after
     *  parsing --verbose, so that second readProperties() call emits its own
     *  "#reading properties ..." diagnostic -- which embeds this checkout's absolute jar
     *  path, making an exact-match golden non-portable across machines. A .tst test
     *  needing --verbose belongs as a .scr script instead, where runscript's $INSTALL
     *  substitution already handles this. */
    private List<String> optionsDirectiveArgs(String text) {
        if (!text.startsWith("; OPTIONS:")) return null;
        int eol = text.indexOf('\n');
        String directiveLine = eol < 0 ? text : text.substring(0, eol);
        List<String> args = new ArrayList<String>();
        for (String flag : directiveLine.substring("; OPTIONS:".length()).trim().split("\\s+")) {
            if (!flag.isEmpty()) args.add(flag);
        }
        return args;
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
        // At the two platform-specific tiers, .bad is checked *before* the plain file --
        // unlike the bare-solvername tier below it, where plain is deliberately checked
        // before .bad (see feedback_family_golden_represents_newest /
        // feedback_test_solver_default_golden_restructuring in memory: the bare file is
        // the trusted, promoted golden there, with .bad only a last-resort fallback). At
        // the platform tier there is no such promoted/default file to defer to -- a
        // platform-specific .bad documents a real, solver-own bug specific to that
        // platform's binary (e.g. a Windows-only miscompiled sort width), and should not
        // be silently shadowed by a same-tier plain file that isn't expected to coexist
        // with it for the same test/solver/platform anyway.
        List<String> candidates = new ArrayList<String>(Arrays.asList(
            base + ext + "." + solvername + "." + PLATFORM_ARCH + ".bad",
            base + ext + "." + solvername + "." + PLATFORM_ARCH,
            base + ext + "." + solvername + "." + PLATFORM + ".bad",
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

    private void compareOutput(String ext, File golden, String actual) {
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

        String cmpExpected = filterIOExceptionLines(expected);
        String cmpActual   = filterIOExceptionLines(actual);

        if (!cmpExpected.equals(cmpActual)) {
            writeActual(ext, actual);
            Assert.assertEquals(
                tstFile.getName() + " / " + solvername + " " + ext,
                cmpExpected, cmpActual);
        }
        // On success: do not write .actual (and delete any stale one)
        new File(actualPath(ext)).delete();
    }

    /** Drops lines containing {@code java.io.IOException:} or
     *  {@code SolverProcess$NoResponseException:} -- these appear in an "Error writing to
     *  solver: ..." response when a script keeps sending commands to a solver process that
     *  has already exited/closed its pipe (e.g. after an unsupported construct kills it).
     *  Which of a script's remaining commands land inside that race window (and so surface
     *  one of these) depends on OS-level timing of the underlying pipe failure and is not
     *  reproducible run to run, even for the identical script against the identical solver
     *  binary -- unlike the get-info non-determinism handled by
     *  AbstractSolver#normalizeForTesting(), this can't be scrubbed at the source, since
     *  it's not response content at all -- it's the *absence* of a response, racing against
     *  however many of a script's remaining commands land after the solver has already
     *  exited. */
    private static String filterIOExceptionLines(String s) {
        StringBuilder sb = new StringBuilder();
        for (String line : s.split("\n", -1)) {
            if (!line.contains("java.io.IOException:") && !line.contains("SolverProcess$NoResponseException:")) sb.append(line).append('\n');
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
