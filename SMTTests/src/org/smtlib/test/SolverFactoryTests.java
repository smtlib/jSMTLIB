package org.smtlib.test;

import java.io.File;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Assume;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.ISolver;
import org.smtlib.SMT;

/**
 * Covers {@code SMT.Configuration#createSolver}'s executable-path handling. In particular,
 * regression coverage for issue #122's zapi.scr failure: createSolver's executable-resolution
 * (shared with startSolver, see SMT#resolveExecutablePath) must leave an already-absolute
 * caller-supplied path alone rather than re-prefixing it with SMT_SOLVER_DIR a second time --
 * APIExample.java used to pass an executable it had already resolved itself this way, and got
 * a doubled, nonexistent path back.
 */
public class SolverFactoryTests {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    /** z3-4.3's real executable name and adapter (see jsmtlib.properties): z3-4.3.1 on every
     *  platform except Windows, which ships 4.3.2 under that same solver name. */
    private static String z3Exe() {
        String dir = System.getenv("SMT_SOLVER_DIR");
        if (dir == null) return null;
        String base = System.getProperty("os.name", "").toLowerCase().contains("win") ? "z3-4.3.2" : "z3-4.3.1";
        String exe = new File(dir, base).getPath();
        return new File(exe).isFile() || new File(exe + ".exe").isFile() ? exe : null;
    }

    @Test
    public void createSolverAcceptsAbsoluteExecutablePath() throws Exception {
        String exe = z3Exe();
        Assume.assumeTrue("z3-4.3 executable not available on this platform", exe != null);

        String absoluteExe = new File(exe).getAbsolutePath();
        Assert.assertTrue("test executable path must actually be absolute: " + absoluteExe,
                new File(absoluteExe).isAbsolute());

        SMT.Configuration config = new SMT.Configuration();
        ISolver solver = config.createSolver("z3-4.3", absoluteExe);
        try {
            Assert.assertFalse("solver.start() should not report an error for a valid absolute path",
                    solver.start().isError());
        } finally {
            solver.exit();
        }
    }

    // SMT.resolveExecutablePath: simple names are found in the solver folder (else on the PATH);
    // relative paths with a directory part are relative to the current directory.

    private static boolean onWindows() {
        return System.getProperty("os.name", "").toLowerCase().contains("win");
    }

    /** A new temporary folder containing an empty file with each of the given names */
    private static File folderWith(String... names) throws Exception {
        File dir = java.nio.file.Files.createTempDirectory("solverdir").toFile();
        dir.deleteOnExit();
        for (String n: names) {
            File f = new File(dir, n);
            Assert.assertTrue(f.createNewFile());
            f.deleteOnExit();
        }
        return dir;
    }

    @Test
    public void resolveSimpleNameInSolverDir() throws Exception {
        File dir = folderWith("fake-solver-1.0");
        Assert.assertEquals(dir.getPath() + "/fake-solver-1.0", SMT.resolveExecutablePath("fake-solver-1.0", dir.getPath()));
    }

    @Test
    public void resolveSimpleNameWithExeInSolverDirOnWindows() throws Exception {
        Assume.assumeTrue("only on Windows", onWindows());
        File dir = folderWith("fake-solver-1.0.exe");
        Assert.assertEquals(dir.getPath() + "/fake-solver-1.0", SMT.resolveExecutablePath("fake-solver-1.0", dir.getPath()));
    }

    @Test
    public void resolveSimpleNameOnPath() throws Exception {
        // a program that is on the PATH but not in the solver folder is left to the PATH lookup
        String onPath = onWindows() ? "cmd" : "sh";
        File dir = folderWith();
        Assert.assertEquals(onPath, SMT.resolveExecutablePath(onPath, dir.getPath()));
    }

    @Test
    public void resolveSimpleNameFoundNowhere() throws Exception {
        // not found: the solver-folder path, so that the error names the expected file
        File dir = folderWith();
        String name = "no-such-solver-9.9.9";
        Assert.assertEquals(dir.getPath() + "/" + name, SMT.resolveExecutablePath(name, dir.getPath()));
        Assert.assertEquals(name, SMT.resolveExecutablePath(name, null));
    }

    @Test
    public void resolveRelativePathIsRelativeToCurrentDirectory() throws Exception {
        // even with a solver folder, and even if that folder has a file at the same relative path
        File dir = folderWith();
        Assert.assertTrue(new File(dir, "sub").mkdir());
        Assert.assertTrue(new File(dir, "sub/z3").createNewFile());
        String rel = "sub" + File.separator + "z3";
        Assert.assertEquals(new File(rel).getAbsolutePath(), SMT.resolveExecutablePath(rel, dir.getPath()));
        Assert.assertEquals(new File("../x/z3").getAbsolutePath(), SMT.resolveExecutablePath("../x/z3", dir.getPath()));
        new File(dir, "sub/z3").delete(); new File(dir, "sub").delete();
    }

    @Test
    public void resolveAbsolutePathUnchanged() throws Exception {
        String abs = new File("some/solver").getAbsolutePath();
        Assert.assertEquals(abs, SMT.resolveExecutablePath(abs, "/elsewhere"));
        Assert.assertNull(SMT.resolveExecutablePath(null, "/elsewhere"));
    }

    /** An adapter that does not name itself is named by its class (#140); creating it starts nothing */
    @Test
    public void defaultSolverNameIsTheAdapterClass() throws Exception {
        org.smtlib.ISolver solver = new SMT.Configuration().createSolver("no-such-solver", "/no/such/solver");
        Assert.assertEquals("org.smtlib.solvers.Solver_smt", solver.solverName());
    }
}
