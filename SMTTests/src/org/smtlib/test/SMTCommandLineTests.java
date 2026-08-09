package org.smtlib.test;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.PrintStream;
import java.lang.reflect.Field;
import java.nio.file.Files;
import java.util.Properties;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.smtlib.ISolver;
import org.smtlib.SMT;

/**
 * Tests command-line error handling in SMT.exec(String[]).
 * Each test captures stdout (where both error responses and usage text are written)
 * and asserts both the non-zero return code and the expected error phrase.
 *
 * Error messages are formatted as SMT-LIB responses: (error "...").
 * usage() output follows immediately on the same stream.
 */
public class SMTCommandLineTests {

    private SMT smt;
    private ByteArrayOutputStream outBuf;
    private PrintStream outPs;

    @Before
    public void setUp() {
        smt = new SMT();
        outBuf = new ByteArrayOutputStream();
        outPs = new PrintStream(outBuf);
        smt.smtConfig.log.out = outPs;
        smt.smtConfig.log.diag = outPs;
    }

    @After
    public void tearDown() {
        if (smt != null) smt.cleanup();
    }

    private int run(String... args) {
        int ret = smt.exec(args);
        outPs.flush();
        return ret;
    }

    private String output() {
        return outBuf.toString();
    }

    private void assertError(int ret, String expectedPhrase) {
        Assert.assertNotEquals("Expected non-zero return code", 0, ret);
        Assert.assertTrue(
            "Expected phrase not found in output.\nExpected: " + expectedPhrase
                + "\nActual output:\n" + output(),
            output().contains(expectedPhrase));
    }

    // -----------------------------------------------------------------------
    // Missing argument for each option
    // -----------------------------------------------------------------------

    @Test public void solverMissingArg() {
        assertError(run("--solver"), "The --solver option expects an argument");
    }

    @Test public void execMissingArg() {
        assertError(run("--exec"), "The --exec option expects an argument");
    }

    @Test public void logicsMissingArg() {
        assertError(run("--logics"), "The --logics option expects an argument");
    }

    @Test public void logicsNullArg() {
        // Programmatic API: null element → logicPath stays null (the != null guard short-circuits)
        int ret = run("-L", null, "--solver", "test", "--text", "(exit)");
        outPs.flush();
        Assert.assertEquals("Expected success when -L argument is null", 0, ret);
        Assert.assertFalse("Expected no error when -L argument is null", output().contains("(error"));
    }

    @Test public void logicsEmptyArg() {
        // Empty string → trim check fires, logicPath is nulled out, execution continues normally
        int ret = run("-L", "", "--solver", "test", "--text", "(exit)");
        outPs.flush();
        Assert.assertEquals("Expected success when -L argument is empty", 0, ret);
        Assert.assertFalse("Expected no error when -L argument is empty", output().contains("(error"));
    }

    @Test public void logicsFromClasspath() {
        // When org.smtlib.logic_path is absent from properties, getProperty returns null,
        // options.logicPath stays null, and the logicFinder falls back to ClassLoader resource
        // lookup — the .smt2 files are packaged at the root of jSMTLIB.jar.
        SMT smtNoLogicPath = new SMT() {
            @Override public Properties readProperties() { return new Properties(); }
        };
        smtNoLogicPath.smtConfig.log.out = outPs;
        int ret = smtNoLogicPath.exec(new String[]{
            "--solver", "test", "--text", "(set-logic QF_UF)(exit)"});
        outPs.flush();
        Assert.assertEquals("Expected success loading logic from classpath", 0, ret);
        Assert.assertFalse("Expected no error", output().contains("(error"));
    }

    // Helper: write a minimal logic file in dir; version is a raw SMT-LIB token (e.g. 2.7 or "2.6")
    private void writeTempLogic(File dir, String name, String version, String theories) throws Exception {
        try (java.io.PrintWriter pw = new java.io.PrintWriter(new File(dir, name + ".smt2"))) {
            pw.println("(logic " + name);
            pw.println(" :smt-lib-version " + version);
            pw.println(" :theories (" + theories + ")");
            pw.println(" :language \"test\"");
            pw.println(")");
        }
    }

    // Helper: write a minimal theory file in dir; version is a raw SMT-LIB token
    private void writeTempTheory(File dir, String name, String version) throws Exception {
        try (java.io.PrintWriter pw = new java.io.PrintWriter(new File(dir, name + ".smt2"))) {
            pw.println("(theory " + name);
            pw.println(" :smt-lib-version " + version);
            pw.println(" :sorts ()");
            pw.println(" :funs ()");
            pw.println(" :definition \"test theory\"");
            pw.println(")");
        }
    }

    // Helper: delete all .smt2 files in dir and the dir itself
    private void cleanTmpDir(File dir) {
        File[] files = dir.listFiles();
        if (files != null) for (File f : files) f.delete();
        dir.delete();
    }

    @Test public void logicVersionNotDecimal() throws Exception {
        File tmpDir = Files.createTempDirectory("smtlogics").toFile();
        try {
            writeTempLogic(tmpDir, "BADVER", "\"2.6\"", ""); // string literal, not decimal
            assertError(run("-L", tmpDir.getAbsolutePath(),
                            "--solver", "test", "--text", "(set-logic BADVER)"),
                "is not a decimal number");
        } finally { cleanTmpDir(tmpDir); }
    }

    @Test public void logicVersionUnknown() throws Exception {
        File tmpDir = Files.createTempDirectory("smtlogics").toFile();
        try {
            writeTempLogic(tmpDir, "FUTVER", "9.9", ""); // decimal but not a known version
            assertError(run("-L", tmpDir.getAbsolutePath(),
                            "--solver", "test", "--text", "(set-logic FUTVER)"),
                "unrecognized SMT-LIB version");
        } finally { cleanTmpDir(tmpDir); }
    }

    @Test public void logicNameMismatch() throws Exception {
        // Logic file declares a different name than the filename
        File tmpDir = Files.createTempDirectory("smtlogics").toFile();
        try {
            try (java.io.PrintWriter pw = new java.io.PrintWriter(new File(tmpDir, "MYLOGIC.smt2"))) {
                pw.println("(logic WRONGNAME :smt-lib-version 2.7 :theories () :language \"test\")");
            }
            assertError(run("-L", tmpDir.getAbsolutePath(),
                            "--solver", "test", "--text", "(set-logic MYLOGIC)"),
                "declares logic name 'WRONGNAME'");
        } finally { cleanTmpDir(tmpDir); }
    }

    @Test public void logicParseError() throws Exception {
        // Malformed logic file — parser should report an error
        File tmpDir = Files.createTempDirectory("smtlogics").toFile();
        try {
            try (java.io.PrintWriter pw = new java.io.PrintWriter(new File(tmpDir, "BADPARSE.smt2"))) {
                pw.println("(logic BADPARSE :smt-lib-version 2.7 :theories ( UNCLOSED");
            }
            assertError(run("-L", tmpDir.getAbsolutePath(),
                            "--solver", "test", "--text", "(set-logic BADPARSE)"),
                "Failed to");
        } finally { cleanTmpDir(tmpDir); }
    }

    @Test public void theoryVersionNotDecimal() throws Exception {
        // Theory file has a non-decimal :smt-lib-version
        File tmpDir = Files.createTempDirectory("smtlogics").toFile();
        try {
            writeTempLogic(tmpDir, "TLOGIC", "2.7", "BADTHVER");
            writeTempTheory(tmpDir, "BADTHVER", "\"2.6\""); // string, not decimal
            assertError(run("-L", tmpDir.getAbsolutePath(),
                            "--solver", "test", "--text", "(set-logic TLOGIC)"),
                "is not a decimal number");
        } finally { cleanTmpDir(tmpDir); }
    }

    @Test public void theoryVersionUnknown() throws Exception {
        // Theory file has a decimal :smt-lib-version that is not a known version
        File tmpDir = Files.createTempDirectory("smtlogics").toFile();
        try {
            writeTempLogic(tmpDir, "TLOGIC2", "2.7", "FUTTHVER");
            writeTempTheory(tmpDir, "FUTTHVER", "9.9"); // unrecognized version
            assertError(run("-L", tmpDir.getAbsolutePath(),
                            "--solver", "test", "--text", "(set-logic TLOGIC2)"),
                "unrecognized SMT-LIB version");
        } finally { cleanTmpDir(tmpDir); }
    }

    @Test public void theoryNameMismatch() throws Exception {
        // Theory file declares a different name than the filename
        File tmpDir = Files.createTempDirectory("smtlogics").toFile();
        try {
            writeTempLogic(tmpDir, "TLOGIC3", "2.7", "MYTHEO");
            writeTempTheory(tmpDir, "MYTHEO", "2.7"); // theory file says "MYTHEO" — correct
            // Overwrite with wrong internal name
            try (java.io.PrintWriter pw = new java.io.PrintWriter(new File(tmpDir, "MYTHEO.smt2"))) {
                pw.println("(theory WRONGTHEO :smt-lib-version 2.7 :sorts () :funs () :definition \"t\")");
            }
            assertError(run("-L", tmpDir.getAbsolutePath(),
                            "--solver", "test", "--text", "(set-logic TLOGIC3)"),
                "declares theory name 'WRONGTHEO'");
        } finally { cleanTmpDir(tmpDir); }
    }

    @Test public void theoryParseError() throws Exception {
        // Malformed theory file
        File tmpDir = Files.createTempDirectory("smtlogics").toFile();
        try {
            writeTempLogic(tmpDir, "TLOGIC4", "2.7", "BADTHPARSE");
            try (java.io.PrintWriter pw = new java.io.PrintWriter(new File(tmpDir, "BADTHPARSE.smt2"))) {
                pw.println("(theory BADTHPARSE :smt-lib-version 2.7 :sorts ( UNCLOSED");
            }
            assertError(run("-L", tmpDir.getAbsolutePath(),
                            "--solver", "test", "--text", "(set-logic TLOGIC4)"),
                "Failed to");
        } finally { cleanTmpDir(tmpDir); }
    }

    @Test public void diagMissingArg() {
        assertError(run("--diag"), "The --diag option expects an argument");
    }

    @Test public void outMissingArg() {
        assertError(run("--out"), "The --out option expects an argument");
    }

    @Test public void portMissingArg() {
        assertError(run("--port"), "The --port option expects an argument");
    }

    @Test public void textMissingArg() {
        assertError(run("--text"), "The --text option expects an argument");
    }

    @Test public void verboseMissingArg() {
        assertError(run("--verbose"), "The --verbose option expects an integer argument");
    }

    @Test public void seedMissingArg() {
        assertError(run("--seed"), "The --seed option expects an argument");
    }

    // -----------------------------------------------------------------------
    // Bad argument values
    // -----------------------------------------------------------------------

    @Test public void verboseNonInteger() {
        assertError(run("--verbose", "fast"), "The --verbose option expects an integer argument");
    }

    @Test public void verboseNegative() {
        assertError(run("--verbose", "-1"), "The argument to --verbose must be non-negative");
    }

    @Test public void seedNonInteger() {
        assertError(run("--seed", "fast"), "The --seed option expects an integer value: fast");
    }

    // -----------------------------------------------------------------------
    // Unknown option
    // -----------------------------------------------------------------------

    @Test public void unknownOption() {
        assertError(run("--nosuchoption"), "Unknown option: --nosuchoption");
    }

    // -----------------------------------------------------------------------
    // Conflicting or incompatible options
    // -----------------------------------------------------------------------

    @Test public void portAndFileConflict() {
        assertError(run("--port", "8080", "somefile.smt2"),
            "You may not specify both a port and file input");
    }

    @Test public void execWithoutSolver() {
        assertError(run("--exec", "/some/path"),
            "If you specify an executable, you must also specify a solver");
    }

    // -----------------------------------------------------------------------
    // Runtime errors triggered after command-line parsing
    // -----------------------------------------------------------------------

    @Test public void fileNotFound() {
        assertError(run("--solver", "test", "/nonexistent/path/no_such_file.smt2"),
            "Could not find file");
    }

    @Test public void solverNoExecutable() {
        // "nosuchsolver" has no Solver_nosuchsolver class and no properties entry,
        // so startSolver cannot find an executable or command for it.
        assertError(run("--solver", "nosuchsolver", "--text", "(exit)"),
            "Neither an executable nor a command specified for a solver named nosuchsolver");
    }

    // -----------------------------------------------------------------------
    // Short-form aliases (-s, -e, -L) for options that require an argument
    // -----------------------------------------------------------------------

    @Test public void solverShortFormMissingArg() {
        assertError(run("-s"), "The --solver option expects an argument");
    }

    @Test public void execShortFormMissingArg() {
        assertError(run("-e"), "The --exec option expects an argument");
    }

    @Test public void logicsShortFormMissingArg() {
        assertError(run("-L"), "The --logics option expects an argument");
    }

    // -----------------------------------------------------------------------
    // --help and --version: return 0 (exec maps processCommandLine's -1 to 0)
    // but must produce output on the log stream
    // -----------------------------------------------------------------------

    @Test public void helpOption() {
        int ret = run("--help");
        outPs.flush();
        Assert.assertEquals(0, ret);
        Assert.assertTrue("Expected usage text in --help output", output().contains("--solver"));
    }

    @Test public void helpShortForm() {
        int ret = run("-h");
        outPs.flush();
        Assert.assertEquals(0, ret);
        Assert.assertTrue("Expected usage text in -h output", output().contains("--solver"));
    }

    @Test public void versionOption() {
        int ret = run("--version");
        outPs.flush();
        Assert.assertEquals(0, ret);
        Assert.assertFalse("Expected version string in --version output", output().trim().isEmpty());
    }

    // -----------------------------------------------------------------------
    // --out / --diag with an unwritable path: IOException is caught and logged,
    // but processCommandLine does NOT return early -- execution continues.
    // Return code comes from the subsequent exec() call, not the file-open failure.
    // -----------------------------------------------------------------------

    @Test public void outBadPath() {
        // processCommandLine logs the error but continues; test solver runs cleanly.
        int ret = run("--out", "/nonexistent/dir/file.txt",
                      "--solver", "test", "--text", "(exit)");
        outPs.flush();
        Assert.assertTrue("Expected open-failure message in output",
            output().contains("Failed to open output stream on /nonexistent/dir/file.txt"));
    }

    @Test public void diagBadPath() {
        int ret = run("--diag", "/nonexistent/dir/file.txt",
                      "--solver", "test", "--text", "(exit)");
        outPs.flush();
        Assert.assertTrue("Expected open-failure message in output",
            output().contains("Failed to open output stream on /nonexistent/dir/file.txt"));
    }

    @Test public void outValidPath() throws Exception {
        File tmp = File.createTempFile("smtout", ".txt");
        tmp.deleteOnExit();
        // --out redirects log.out to the file; "success" from set-logic goes there, not to outPs
        int ret = run("--out", tmp.getAbsolutePath(),
                      "--solver", "test", "--text", "(set-logic QF_UF)");
        outPs.flush();
        Assert.assertEquals("Expected success with valid --out path", 0, ret);
        Assert.assertFalse("Expected no open-failure with valid --out path",
            output().contains("Failed to open output stream"));
        String fileContent = new String(Files.readAllBytes(tmp.toPath()));
        Assert.assertTrue("Expected 'success' written to --out file", fileContent.contains("success"));
    }

    @Test public void diagValidPath() throws Exception {
        File tmp = File.createTempFile("smtdiag", ".txt");
        tmp.deleteOnExit();
        // --diag redirects log.diag; --verbose 1 ensures diagnostic lines are emitted
        int ret = run("--diag", tmp.getAbsolutePath(), "--verbose", "1",
                      "--solver", "test", "--text", "(exit)");
        outPs.flush();
        Assert.assertEquals("Expected success with valid --diag path", 0, ret);
        Assert.assertFalse("Expected no open-failure with valid --diag path",
            output().contains("Failed to open output stream"));
        Assert.assertTrue("Expected diagnostic output written to --diag file", tmp.length() > 0);
    }

    // -----------------------------------------------------------------------
    // --seed with a valid value: should be accepted without error
    // -----------------------------------------------------------------------

    @Test public void seedValid() {
        int ret = run("--seed", "42", "--solver", "test", "--text", "(exit)");
        outPs.flush();
        Assert.assertEquals("Expected success with valid seed", 0, ret);
        Assert.assertFalse("Expected no error in output", output().contains("(error"));
    }

    // -----------------------------------------------------------------------
    // --nosuccess / -q: suppress 'success' responses
    // -----------------------------------------------------------------------

    @Test public void nosuccess() {
        int ret = run("--nosuccess", "--solver", "test", "--text", "(set-logic QF_UF)");
        outPs.flush();
        Assert.assertEquals(0, ret);
        Assert.assertFalse("Expected 'success' to be suppressed by --nosuccess",
            output().contains("success"));
    }

    @Test public void nosuccessShortForm() {
        int ret = run("-q", "--solver", "test", "--text", "(set-logic QF_UF)");
        outPs.flush();
        Assert.assertEquals(0, ret);
        Assert.assertFalse("Expected 'success' to be suppressed by -q",
            output().contains("success"));
    }

    // -----------------------------------------------------------------------
    // cleanup() with an active solver.
    //
    // doParser() always calls solver.forceExit() + solver = null before returning,
    // so tearDown()'s cleanup() always finds solver == null.  To cover the
    // if (solver != null) branch we inject a live solver via reflection.
    // -----------------------------------------------------------------------

    @Test public void cleanupWithActiveSolver() throws Exception {
        SMT s = new SMT();
        s.props = s.readProperties();
        ISolver solver = s.startSolver(s.smtConfig, "test", null);
        Assert.assertNotNull("startSolver should succeed for 'test'", solver);

        Field f = SMT.class.getDeclaredField("solver");
        f.setAccessible(true);
        f.set(s, solver);

        s.cleanup();

        Assert.assertNull("cleanup() should null the solver field", f.get(s));
    }
}
