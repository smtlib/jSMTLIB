package org.smtlib.test.printing;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.junit.runners.ParameterizedWithNames;
import org.smtlib.SMT;
import org.smtlib.sexpr.ScriptText;

/**
 * Generated stress cases for the printers (#222): from each seed script, variants with a comment, odd
 * whitespace, or no whitespace (where none is needed) at each token boundary in turn, each checked for
 * the printing properties (PrintProperties). Seeds: the pretty-printing corpus and every 25th test script.
 */
@RunWith(ParameterizedWithNames.class)
public class PrettyPrintStressTests {

    /** At most this many boundaries of a seed are varied (evenly spread) */
    private static final int MAX_BOUNDARIES = 200;

    /** What is put at a boundary, replacing the whitespace and comments there */
    private static final String[] INSERTS = { " ; gen\n", "\n\t ; gen\r\n\r\n  ", "\t\r\n", "" };

    private final File seed;

    public PrettyPrintStressTests(String name, File seed) {
        this.seed = seed;
    }

    @Parameters
    public static Collection<Object[]> data() {
        List<File> seeds = new ArrayList<>();
        ScriptTextPropertyTests.collect(Corpus.prettyprint(), seeds, ".smt2");
        List<File> tests = new ArrayList<>();
        ScriptTextPropertyTests.collect(Corpus.folder("tests"), tests, ".tst");
        for (int i = 0; i < tests.size(); i += 25) seeds.add(tests.get(i));
        Collection<Object[]> data = new ArrayList<>();
        for (File f : seeds) data.add(new Object[] { f.getPath(), f });
        return data;
    }

    @Test
    public void variants() throws IOException {
        String text = new String(Files.readAllBytes(seed.toPath()), StandardCharsets.UTF_8);
        ScriptText st = ScriptText.of(new SMT().smtConfig, text);
        if (PrintProperties.hasLexicalError(st)) return;
        List<ScriptText.Token> tokens = st.tokens();
        int step = Math.max(1, tokens.size() / MAX_BOUNDARIES);
        for (int b = 0; b < tokens.size(); b += step) {
            for (String insert : INSERTS) {
                if (insert.isEmpty() && !mayTouch(tokens, b)) continue;
                StringBuilder sb = new StringBuilder();
                for (int i = 0; i < tokens.size(); i++) {
                    sb.append(i == b ? insert : tokens.get(i).leading()).append(tokens.get(i).text());
                }
                PrintProperties.check(sb.toString(), seed.getName() + " with " + quote(insert) + " before token " + b);
            }
        }
    }

    /** Whether token b may follow token b-1 with nothing between them: one of them is a parenthesis, or b
     *  is the end of input (a comment there would need its line break kept) */
    private static boolean mayTouch(List<ScriptText.Token> tokens, int b) {
        if (b == 0) return true;
        ScriptText.Kind prev = tokens.get(b - 1).kind();
        ScriptText.Kind cur = tokens.get(b).kind();
        return prev == ScriptText.Kind.LP || prev == ScriptText.Kind.RP
                || cur == ScriptText.Kind.LP || cur == ScriptText.Kind.RP || cur == ScriptText.Kind.EOD;
    }

    private static String quote(String s) {
        return "\"" + s.replace("\n", "\\n").replace("\r", "\\r").replace("\t", "\\t") + "\"";
    }
}
