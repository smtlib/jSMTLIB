package org.smtlib.test.printing;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.junit.runners.ParameterizedWithNames;

/**
 * The printing properties (PrintProperties) on every script of the test suites, the logic and theory
 * files, and the pretty-printing corpus (#222). Most of these scripts have few comments and nearly
 * pretty whitespace: a baseline; PrettyPrintStressTests and the corpus stress the printers.
 */
@RunWith(ParameterizedWithNames.class)
public class ScriptTextPropertyTests {

    private final File file;

    public ScriptTextPropertyTests(String name, File file) {
        this.file = file;
    }

    @Parameters
    public static Collection<Object[]> data() {
        List<File> files = new ArrayList<>();
        collect(Corpus.folder("tests"), files, ".tst", ".smt2");
        collect(Corpus.folder("scripts"), files, ".smt2");
        collect(Corpus.logics(), files, ".smt2");
        Collection<Object[]> data = new ArrayList<>();
        for (File f : files) data.add(new Object[] { f.getPath(), f });
        return data;
    }

    static void collect(File dir, List<File> result, String... extensions) {
        File[] entries = dir.listFiles();
        if (entries == null) return;
        Arrays.sort(entries);
        for (File e : entries) {
            if (e.isDirectory()) collect(e, result, extensions);
            else for (String ext : extensions) if (e.getName().endsWith(ext)) result.add(e);
        }
    }

    @Test
    public void properties() throws IOException {
        PrintProperties.check(new String(Files.readAllBytes(file.toPath()), StandardCharsets.UTF_8), file.getPath());
    }
}
