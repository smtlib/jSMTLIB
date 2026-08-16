package org.smtlib.test;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.ParameterizedWithNames;
import org.junit.runners.Parameterized.Parameters;

/** Parallel to FileTests, but for typechecks/ (a sibling of tests/, not a subdirectory of
 *  it) -- .tst files that exercise jSMTLIB's own client-side TypeChecker. Fixed to the
 *  built-in "test" solver only, not parameterized by SMT_TEST_SOLVERS: Solver_test.assertExpr()
 *  is the only ISolver implementation that calls TypeChecker.checkAssertion() at all --
 *  every real-solver adapter inherits AbstractSolver.assertExpr(), which forwards the
 *  asserted text straight to the solver process and never invokes TypeChecker -- so running
 *  these against a real solver would not be exercising the same code this class exists to
 *  check. (A later phase may deliberately run this same file corpus against real solvers
 *  to see how their own native type-checking compares; that is a different, separate
 *  question from this class's, and would capture its own real per-solver goldens rather
 *  than reusing these.)
 *
 *  Reuses FileTests' checkFile()/checkSkip()/findGoldenFile()/compareOutput() machinery
 *  as-is (goldens, .bad handling, platform-specific variants, memory-line filtering, .skip
 *  markers -- all identical conventions to tests/), overriding only where the tests live
 *  and which solver(s) to pair them with. */
@RunWith(ParameterizedWithNames.class)
public class TypeCheckTests extends FileTests {

    public TypeCheckTests(String solvername, String tstFilePath) {
        super(solvername, tstFilePath);
    }

    // Re-declared (not just inherited) so runjunits' own class-discovery, which greps
    // source text for the literal "@Test" rather than doing real reflection, actually
    // picks this class up as a test class to hand to JUnitCore.
    @Test
    @Override
    public void checkFile() {
        super.checkFile();
    }

    @Parameters
    public static Collection<String[]> datax() {
        Collection<String[]> data = new ArrayList<>();
        File dir = new File("typechecks");
        List<File> tstFiles = new ArrayList<>();
        collectTstFiles(dir, tstFiles);
        for (File f : tstFiles) {
            data.add(new String[]{"test", f.getAbsolutePath()});
        }
        return data;
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
}
