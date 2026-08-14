package org.smtlib.test;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.IResponse;
import org.smtlib.Log;
import org.smtlib.SMT;
import org.smtlib.Utils;

/** Unit tests for Log listener management and Utils.quote / Utils.unescape. */
public class UnitTests {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    private SMT.Configuration config;
    private Log log;

    @Before
    public void setUp() {
        config = new SMT.Configuration();
        log = config.log;
        log.clearListeners();
    }

    @After
    public void tearDown() {
    }

    // -----------------------------------------------------------------------
    // Log listener lifecycle
    // -----------------------------------------------------------------------

    /** Minimal listener that records every call for later assertions. */
    static class RecordingListener implements Log.IListener {
        final List<String> outStrings = new ArrayList<>();
        final List<String> errorStrings = new ArrayList<>();
        final List<String> diagStrings = new ArrayList<>();

        @Override public void logOut(String msg)           { outStrings.add(msg); }
        @Override public void logOut(IResponse r)          {}
        @Override public void logError(String msg)         { errorStrings.add(msg); }
        @Override public void logError(IResponse.IError r) {}
        @Override public void logDiag(String msg)          { diagStrings.add(msg); }
        @Override public void indent(String chars)         {}
    }

    /** Full listener lifecycle: add two, dispatch to both; remove one, dispatch to remaining;
     *  clear all, dispatch to neither. */
    @Test
    public void listenerLifecycle_addBothRemoveOneClearAll() {
        RecordingListener l1 = new RecordingListener();
        RecordingListener l2 = new RecordingListener();

        // Both listeners registered — each receives the message.
        log.addListener(l1);
        log.addListener(l2);
        log.logOut("both");
        Assert.assertEquals(1, l1.outStrings.size());
        Assert.assertEquals("both", l1.outStrings.get(0));
        Assert.assertEquals(1, l2.outStrings.size());
        Assert.assertEquals("both", l2.outStrings.get(0));

        // Remove l1 only — l2 still receives, l1 does not.
        boolean removed = log.removeListener(l1);
        Assert.assertTrue(removed);
        log.logOut("l2 only");
        Assert.assertEquals(1, l1.outStrings.size()); // unchanged
        Assert.assertEquals(2, l2.outStrings.size());
        Assert.assertEquals("l2 only", l2.outStrings.get(1));

        // Removing an already-removed listener returns false.
        Assert.assertFalse(log.removeListener(l1));

        // Clear all listeners — neither receives further messages.
        log.clearListeners();
        log.logOut("nobody");
        Assert.assertEquals(1, l1.outStrings.size()); // still unchanged
        Assert.assertEquals(2, l2.outStrings.size()); // still unchanged
    }

    // -----------------------------------------------------------------------
    // Utils.quote / Utils.unescape helpers
    // -----------------------------------------------------------------------

    /** Creates a Utils configured for the requested version.
     *  V2.0: only \" and \\ are escape sequences.
     *  V2.5: only "" is an escape sequence; backslash is not special. */
    private Utils makeUtils(boolean v20) {
        SMT.Configuration cfg = new SMT.Configuration();
        cfg.smtlib = v20 ? "V2.0" : null; // null → default V2.5
        return new Utils(cfg);
    }

    /** Creates a Utils with a RecordingListener attached to its log (StandardListener removed).
     *  Use this when the test needs to verify that errors are or are not reported. */
    private Utils makeUtilsWithListener(boolean v20, RecordingListener listener) {
        SMT.Configuration cfg = new SMT.Configuration();
        cfg.smtlib = v20 ? "V2.0" : null;
        cfg.log.clearListeners();
        cfg.log.addListener(listener);
        return new Utils(cfg);
    }

    // -----------------------------------------------------------------------
    // Utils.quote — V2.0
    // SMT-LIB 2.0: " → \"   \ → \\   all other chars pass through unchanged
    // -----------------------------------------------------------------------

    @Test
    public void quote_v20() {
        Utils u = makeUtils(true);

        // empty string
        Assert.assertEquals("\"\"", u.quote(""));

        // plain ASCII — no escaping needed
        Assert.assertEquals("\"hello\"", u.quote("hello"));

        // double-quote → backslash-quote  (\" inside the literal)
        Assert.assertEquals("\"say \\\"hi\\\"\"", u.quote("say \"hi\""));

        // backslash → double-backslash
        Assert.assertEquals("\"a\\\\b\"", u.quote("a\\b"));

        // both: a\"b  →  a\\"b  (\ → \\ , " → \")
        Assert.assertEquals("\"a\\\\\\\"b\"", u.quote("a\\\"b"));

        // two-char sequence \n (backslash + n, NOT newline): \ → \\, n passes
        Assert.assertEquals("\"\\\\n\"", u.quote("\\n"));

        // actual newline character — not printable ASCII per the spec but the
        // code passes it through unchanged (no special handling)
        Assert.assertEquals("\"\n\"", u.quote("\n"));

        // unicode: latin extension é (U+00E9) — passes through in implementation
        Assert.assertEquals("\"café\"", u.quote("café"));

        // unicode: CJK 中文 (U+4E2D U+6587) — passes through in implementation
        Assert.assertEquals("\"中文\"", u.quote("中文"));
    }

    // -----------------------------------------------------------------------
    // Utils.quote — V2.5
    // SMT-LIB 2.5: " → ""   all other chars (including \) pass through unchanged
    // -----------------------------------------------------------------------

    @Test
    public void quote_v25() {
        Utils u = makeUtils(false);

        // empty string
        Assert.assertEquals("\"\"", u.quote(""));

        // plain ASCII — no escaping needed
        Assert.assertEquals("\"hello\"", u.quote("hello"));

        // double-quote → doubled-quote  ("" inside the literal)
        Assert.assertEquals("\"say \"\"hi\"\"\"", u.quote("say \"hi\""));

        // backslash — NOT an escape character in V2.5, passes through unchanged
        Assert.assertEquals("\"a\\b\"", u.quote("a\\b"));

        // both: a\"b → a\""b  (\ passes, " → "")
        Assert.assertEquals("\"a\\\"\"b\"", u.quote("a\\\"b"));

        // two-char sequence \n (backslash + n): both pass through unchanged
        Assert.assertEquals("\"\\n\"", u.quote("\\n"));

        // actual newline — whitespace chars are allowed inside V2.5 string literals
        Assert.assertEquals("\"\n\"", u.quote("\n"));

        // unicode: latin extension é
        Assert.assertEquals("\"café\"", u.quote("café"));

        // unicode: CJK 中文
        Assert.assertEquals("\"中文\"", u.quote("中文"));
    }

    // -----------------------------------------------------------------------
    // Utils.unescape — V2.0
    // Input must include the enclosing double-quote delimiters.
    // \" → "   \\ → \   \x (other) → \x (backslash is kept)
    // -----------------------------------------------------------------------

    @Test
    public void unescape_v20() {
        Utils u = makeUtils(true);

        // empty quoted string
        Assert.assertEquals("", u.unescape("\"\""));

        // plain text — no escapes, no backslashes
        Assert.assertEquals("hello", u.unescape("\"hello\""));

        // escaped double-quote  \"  →  "
        Assert.assertEquals("say \"hi\"", u.unescape("\"say \\\"hi\\\"\""));

        // escaped backslash  \\  →  \
        Assert.assertEquals("a\\b", u.unescape("\"a\\\\b\""));

        // sequence \\\" → \ then "  (two escape sequences back to back)
        Assert.assertEquals("a\\\"b", u.unescape("\"a\\\\\\\"b\""));

        // unrecognised escape \n (backslash + n) — backslash is preserved
        Assert.assertEquals("a\\nb", u.unescape("\"a\\nb\""));

        // unicode latin extension é — passes through unchanged
        Assert.assertEquals("café", u.unescape("\"café\""));

        // unicode CJK — passes through unchanged
        Assert.assertEquals("中文", u.unescape("\"中文\""));
    }

    // -----------------------------------------------------------------------
    // Utils.unescape — V2.5
    // Input must include the enclosing double-quote delimiters.
    // "" → "   all other chars (including \) pass through unchanged
    // -----------------------------------------------------------------------

    @Test
    public void unescape_v25() {
        Utils u = makeUtils(false);

        // empty quoted string
        Assert.assertEquals("", u.unescape("\"\""));

        // plain text — no escape sequences
        Assert.assertEquals("hello", u.unescape("\"hello\""));

        // doubled-quote  ""  →  "
        Assert.assertEquals("say \"hi\"", u.unescape("\"say \"\"hi\"\"\""));

        // backslash is NOT an escape character in V2.5 — passes through
        Assert.assertEquals("a\\b", u.unescape("\"a\\b\""));

        // sequence \""  →  \" (backslash passes, "" → ")
        Assert.assertEquals("a\\\"b", u.unescape("\"a\\\"\"b\""));

        // unicode latin extension é
        Assert.assertEquals("café", u.unescape("\"café\""));

        // unicode CJK
        Assert.assertEquals("中文", u.unescape("\"中文\""));
    }

    // -----------------------------------------------------------------------
    // Utils.unescape — V2.5 edge / malformed cases (branch coverage)
    // -----------------------------------------------------------------------

    @Test
    public void unescape_v25_edgeCases() {
        RecordingListener rl = new RecordingListener();
        Utils u = makeUtilsWithListener(false, rl);

        // k == kk branch: the first content char is immediately a '"'.
        // Input """  (3 quotes: open, "", close).  The "" pair is at positions 1-2;
        // position 2 is consumed as the second char of the "" escape, content is '"'.
        Assert.assertEquals("\"", u.unescape("\"\"\""));
        Assert.assertTrue("no error expected for \"\"\"", rl.errorStrings.isEmpty());

        // kk == -1 branch: no '"' found after k — malformed, missing closing quote.
        // Defensive behaviour: appends substring(k, endPos), excluding the last char.
        rl.errorStrings.clear();
        Assert.assertEquals("ab", u.unescape("\"abc"));
        Assert.assertFalse("expected error for missing closing quote", rl.errorStrings.isEmpty());

        // c != '"' branch: lone '"' mid-string not followed by another '"'.
        // Defensive behaviour: the lone quote is dropped (only content before it is kept).
        rl.errorStrings.clear();
        Assert.assertEquals("a", u.unescape("\"a\"b\""));
        Assert.assertFalse("expected error for lone quote mid-string", rl.errorStrings.isEmpty());
    }

    // -----------------------------------------------------------------------
    // Utils.unescape — error cases that cannot be triggered via normal Lexer scanning
    // -----------------------------------------------------------------------

    @Test
    public void unescape_errorsReported_v20() {
        RecordingListener rl = new RecordingListener();
        Utils u = makeUtilsWithListener(true, rl);

        // (a) backslash is the last character — no closing quote follows.
        //     Previously threw StringIndexOutOfBoundsException; now logs an error.
        //     Java literal "\"abc\\" represents the 5-char string: "abc\
        u.unescape("\"abc\\");
        Assert.assertFalse("expected error for backslash-at-end (a)", rl.errorStrings.isEmpty());
        rl.errorStrings.clear();

        // (b) string ends with \" — the closing quote is consumed by the escape sequence,
        //     leaving the string unterminated.
        //     Java literal "\"abc\\\"" represents the 6-char string: "abc\"
        u.unescape("\"abc\\\"");
        Assert.assertFalse("expected error for closing-quote-consumed (b)", rl.errorStrings.isEmpty());
        rl.errorStrings.clear();

        // (d) no opening quote — argument does not start with a double-quote.
        u.unescape("abc");
        Assert.assertFalse("expected error for no opening quote (d)", rl.errorStrings.isEmpty());
    }

    @Test
    public void unescape_errorsReported_v25() {
        RecordingListener rl = new RecordingListener();
        Utils u = makeUtilsWithListener(false, rl);

        // missing closing quote — same FIXME path tested in unescape_v25_edgeCases
        u.unescape("\"abc");
        Assert.assertFalse("expected error for missing closing quote", rl.errorStrings.isEmpty());
        rl.errorStrings.clear();

        // lone quote mid-string — same FIXME path tested in unescape_v25_edgeCases
        u.unescape("\"a\"b\"");
        Assert.assertFalse("expected error for lone quote mid-string", rl.errorStrings.isEmpty());
        rl.errorStrings.clear();

        // (d) no opening quote
        u.unescape("abc");
        Assert.assertFalse("expected error for no opening quote (d)", rl.errorStrings.isEmpty());
    }

    // -----------------------------------------------------------------------
    // Round-trip: unescape(quote(s)) == s  for both versions
    // -----------------------------------------------------------------------

    @Test
    public void roundTrip_v20() {
        Utils u = makeUtils(true);
        String[] inputs = {
            "",                  // empty
            "hello",             // plain ASCII
            "say \"hi\"",        // contains double-quote
            "a\\b",              // contains backslash
            "a\\\"b",            // backslash immediately followed by double-quote
            "café",         // latin extension unicode
            "中文",      // CJK unicode
        };
        for (String s : inputs) {
            Assert.assertEquals("round-trip failed for: " + s, s, u.unescape(u.quote(s)));
        }
    }

    @Test
    public void roundTrip_v25() {
        Utils u = makeUtils(false);
        String[] inputs = {
            "",                  // empty
            "hello",             // plain ASCII
            "say \"hi\"",        // contains double-quote
            "a\\b",              // contains backslash (not an escape in V2.5)
            "a\\\"b",            // backslash immediately followed by double-quote
            "line1\nline2",      // actual newline (whitespace allowed in V2.5)
            "café",         // latin extension unicode
            "中文",      // CJK unicode
        };
        for (String s : inputs) {
            Assert.assertEquals("round-trip failed for: " + s, s, u.unescape(u.quote(s)));
        }
    }
}
