package org.smtlib.test.printing;

import java.util.ArrayList;
import java.util.List;

import org.junit.Assert;
import org.smtlib.SMT;
import org.smtlib.sexpr.PrettyPrinter;
import org.smtlib.sexpr.ScriptText;

/**
 * The properties every script must have under ScriptText and PrettyPrinter (#222): the exact text is
 * reproduced; trivia holds only whitespace and comments; and, for a script without lexical errors, each
 * pretty printer keeps the tokens (re-read from its output), is idempotent, and keeps every comment in
 * order (or, without comments, prints none).
 */
final class PrintProperties {

    static final int[] WIDTHS = { 80, 20 };

    private PrintProperties() {}

    static void check(String text, String label) {
        SMT.Configuration config = new SMT().smtConfig;
        ScriptText st = ScriptText.of(config, text);
        Assert.assertEquals(label + ": exact text", text, st.exact());
        if (hasLexicalError(st)) {
            for (boolean comments : new boolean[] { true, false }) {
                Assert.assertEquals(label + ": a script with a lexical error is printed unchanged",
                        text, PrettyPrinter.print(st, comments, 80));
            }
            return;
        }
        for (int width : WIDTHS) {
            for (boolean comments : new boolean[] { true, false }) {
                String what = label + " (" + (comments ? "with" : "without") + " comments, width " + width + ")";
                String out = PrettyPrinter.print(st, comments, width);
                ScriptText again = ScriptText.of(config, out);
                Assert.assertEquals(what + ": tokens\n" + out, tokens(st), tokens(again));
                Assert.assertEquals(what + ": idempotent", out, PrettyPrinter.print(again, comments, width));
                Assert.assertEquals(what + ": comments\n" + out, comments ? st.comments() : List.of(), again.comments());
                Assert.assertFalse(what + ": starts with a line break\n" + out, out.startsWith("\n"));
                Assert.assertTrue(what + ": trailing white space between tokens\n" + out, noTrailingSpace(again));
            }
        }
    }

    /** Whether the script has a lexical error: an error token, or something other than whitespace and
     *  comments between tokens (PrettyPrinter then leaves it unchanged) */
    static boolean hasLexicalError(ScriptText st) {
        for (ScriptText.Token t : st.tokens()) {
            if (t.kind() == ScriptText.Kind.ERROR || !isTrivia(t.leading())) return true;
        }
        return false;
    }

    /** Whether the text is SMT-LIB whitespace (space, tab, CR, LF) and comments only */
    static boolean isTrivia(String s) {
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            if (c == ';') {
                while (i + 1 < s.length() && s.charAt(i + 1) != '\n' && s.charAt(i + 1) != '\r') i++;
            } else if (c != ' ' && c != '\t' && c != '\r' && c != '\n') {
                return false;
            }
        }
        return true;
    }

    /** Whether no line of the trivia between tokens ends with spaces or tabs (comments may) */
    static boolean noTrailingSpace(ScriptText st) {
        for (ScriptText.Token t : st.tokens()) {
            String[] lines = t.leading().split("\\r\\n|\\r|\\n", -1);
            for (int i = 0; i < lines.length - 1; i++) {
                if (!lines[i].contains(";") && !lines[i].isEmpty()) return false;
            }
        }
        return true;
    }

    static List<String> tokens(ScriptText st) {
        List<String> list = new ArrayList<>();
        for (ScriptText.Token t : st.tokens()) list.add(t.kind() + " " + t.text());
        return list;
    }
}
