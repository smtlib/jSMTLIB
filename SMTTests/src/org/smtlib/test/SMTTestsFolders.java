package org.smtlib.test;

import java.io.File;

/** Locates folders of the SMTTests project (tests/, scripts/) independently of the working
 *  directory, so the test classes also run from an IDE (#153). */
final class SMTTestsFolders {

    private SMTTestsFolders() {}

    /** The named folder of SMTTests: found next to the folder these classes were loaded from
     *  (SMTTests/bin), else in the working directory; throws if neither has it. */
    static File find(String name) {
        File besideClasses = null;
        try {
            File classes = new File(SMTTestsFolders.class.getProtectionDomain().getCodeSource().getLocation().toURI());
            besideClasses = new File(classes.getParentFile(), name);
            if (besideClasses.isDirectory()) return besideClasses;
        } catch (Exception e) {
            // no usable code source; try the working directory
        }
        File inWorkingDir = new File(name).getAbsoluteFile();
        if (inWorkingDir.isDirectory()) return inWorkingDir;
        throw new IllegalStateException("Cannot find the SMTTests " + name + " folder; looked for "
                + (besideClasses == null ? "" : besideClasses + " and ") + inWorkingDir);
    }
}
