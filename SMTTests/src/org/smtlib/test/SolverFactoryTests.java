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
}
