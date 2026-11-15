package org.smtlib.test.printing;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.junit.runners.ParameterizedWithNames;
import org.smtlib.SMT;
import org.smtlib.sexpr.PrettyPrinter;
import org.smtlib.sexpr.ScriptText;

/**
 * Golden layouts for the pretty-printing corpus, tests/prettyprint (#222): each {@code <name>.smt2} is
 * pretty-printed in width 80 with its comments ({@code <name>.smt2.pretty}) and without
 * ({@code <name>.smt2.nocomments}). A mismatch writes {@code .actual} beside the golden file.
 */
@RunWith(ParameterizedWithNames.class)
public class PrettyPrintTests {

    private final File file;

    public PrettyPrintTests(String name, File file) {
        this.file = file;
    }

    @Parameters
    public static Collection<Object[]> data() {
        List<File> files = new ArrayList<>();
        ScriptTextPropertyTests.collect(Corpus.prettyprint(), files, ".smt2");
        Collection<Object[]> data = new ArrayList<>();
        for (File f : files) data.add(new Object[] { f.getName(), f });
        return data;
    }

    @Test
    public void withComments() throws IOException {
        compare(true, ".pretty");
    }

    @Test
    public void withoutComments() throws IOException {
        compare(false, ".nocomments");
    }

    private void compare(boolean comments, String ext) throws IOException {
        String text = new String(Files.readAllBytes(file.toPath()), StandardCharsets.UTF_8);
        String actual = PrettyPrinter.print(ScriptText.of(new SMT().smtConfig, text), comments, 80);
        File golden = new File(file.getPath() + ext);
        File actualFile = new File(golden.getPath() + ".actual");
        String expected = golden.exists()
                ? new String(Files.readAllBytes(golden.toPath()), StandardCharsets.UTF_8).replace("\r\n", "\n") : null;
        if (actual.equals(expected)) {
            Files.deleteIfExists(actualFile.toPath());
            return;
        }
        Files.write(actualFile.toPath(), actual.getBytes(StandardCharsets.UTF_8));
        if (expected == null) Assert.fail("No golden " + golden + "; output written to " + actualFile);
        Assert.assertEquals(golden.getName(), expected, actual);
    }
}
