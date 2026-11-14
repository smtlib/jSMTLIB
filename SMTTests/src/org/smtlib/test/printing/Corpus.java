package org.smtlib.test.printing;

import java.io.File;

/** Locates the SMTTests folders and the SMT logics folder for the printing tests */
final class Corpus {

    private Corpus() {}

    /** An SMTTests folder (beside the test classes' folder, or in the working directory) */
    static File folder(String name) {
        File inWorkingDir = new File(name).getAbsoluteFile();
        if (inWorkingDir.isDirectory()) return inWorkingDir;
        try {
            File classes = new File(Corpus.class.getProtectionDomain().getCodeSource().getLocation().toURI());
            File beside = new File(classes.getParentFile(), name);
            if (beside.isDirectory()) return beside;
        } catch (Exception e) {
            // fall through
        }
        throw new IllegalStateException("Cannot find the SMTTests " + name + " folder");
    }

    /** The logic and theory definitions, SMT/logics */
    static File logics() {
        return new File(folder("tests").getParentFile().getParentFile(), "SMT/logics");
    }

    /** The pretty-printing corpus */
    static File prettyprint() {
        return new File(folder("tests"), "prettyprint");
    }
}
