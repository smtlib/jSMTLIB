package org.smtlib.test.bugs;

import java.io.StringReader;
import java.util.concurrent.TimeUnit;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.CharSequenceReader;
import org.smtlib.IParser;
import org.smtlib.ISource;
import org.smtlib.SMT;
import org.smtlib.sexpr.Lexer;

/**
 * Pins down (and, now, confirms the fix for) sexpr/Lexer.java's {@code abortLine()}, which
 * originally read:
 *
 * <pre>public void abortLine() {
 *     int i = matcher.regionStart();
 *     char c;
 *     while ((c=csr.charAt(i))!= '\r' && c != '\n') ++i; // FIXME  - what about end of input?
 *     matcher.region(i,csr.length());
 * }</pre>
 *
 * Scanning forward for {@code \r}/{@code \n} with no end-of-input check -- flagged by the
 * author's own FIXME on the same line. A final line with no trailing newline walked
 * {@code i} past the end of the buffer.
 * <p>
 * {@code abortLine()} is called from {@code SMT.java}'s interactive-mode error recovery
 * (after a parse error, to skip to the next line and keep going) -- reachable any time the
 * last line of interactive input has a parse error and no trailing newline.
 * <p>
 * Fixed by re-checking {@code i < csr.length()} fresh on every iteration (rather than
 * snapshotting the bound once) and explicitly checking for
 * {@code CharSequenceInfinite.endChar}. Both matter: a plain, fixed CharSequence (a real
 * String) throws immediately past its length with no such sentinel, so it needs the bounds
 * check; a growing/interactive CharSequence ({@code CharSequenceReader}, as real interactive
 * stdin input uses) reports {@code Integer.MAX_VALUE} from {@code length()} until
 * {@code charAt()} itself lazily discovers true end-of-input, at which point it returns
 * {@code endChar} forever -- a stale/snapshotted bound never catches that case, and it would
 * otherwise loop forever rather than throw.
 * <p>
 * Three tests, one per failure mode fixed: a direct, minimal call to
 * {@code Lexer.abortLine()} on a fixed CharSequence; the same but on a growing
 * {@code CharSequenceReader} at real end-of-input (previously hung rather than threw); and a
 * third, stronger reproduction driven through the real reachable path --
 * {@code SMT.doParser()} with {@code --abort} and interactive mode, given a command that
 * fails to parse on the last line of input with no trailing newline -- confirming this was
 * not just a unit-level construction but an actual crash of the whole run.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/72">issue #72</a>.
 */
public class LexerAbortLineBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    @Test
    public void abortLineAtEndOfInputWithNoTrailingNewlineDoesNotThrow() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        // No trailing '\r'/'\n' anywhere in this input.
        ISource source = config.smtFactory.createSource("(foo", null);
        Lexer lexer = new Lexer(config, source);

        lexer.abortLine();
    }

    /** {@code doParser} is protected, so this subclass exists purely to call it from the
     *  test package -- it adds no behavior of its own. */
    static class TestSMT extends SMT {
        int run(IParser p) { return doParser(p); }
    }

    /** Same bug, driven through the real, reachable end-to-end path described above (rather
     *  than calling Lexer.abortLine() directly): --abort mode, interactive mode, a command
     *  that fails to parse, on the last (and only) line of input with no trailing newline.
     *  Confirmed to crash through this exact path before a fix: SMT.doParser() ->
     *  IParser.abortLine() -> Lexer.abortLine() -> StringIndexOutOfBoundsException. */
    @Test
    public void unparseableFinalLineWithNoTrailingNewlineDoesNotCrashTheWholeRun() throws Exception {
        TestSMT smt = new TestSMT();
        smt.props = smt.readProperties();
        smt.smtConfig.solvername = "test";
        smt.smtConfig.abort = true;
        smt.smtConfig.interactive = true;
        // "foo" is not a recognized command, so parseCommand() fails -- and there is no
        // trailing newline for abortLine() to find.
        ISource source = smt.smtConfig.smtFactory.createSource("(foo", null);
        IParser p = smt.smtConfig.smtFactory.createParser(smt.smtConfig, source);

        smt.run(p);
    }

    /** A third, distinct failure mode: for a growing/interactive source
     *  (CharSequenceReader, as real interactive stdin input uses), csr.length() reports
     *  Integer.MAX_VALUE until charAt() itself lazily discovers true end-of-input -- so a
     *  fix that only adds a bound snapshotted once at the top (e.g. {@code int len =
     *  csr.length();} checked against a stale value) does not actually stop the scan here.
     *  Unfixed, this hangs (an unbounded loop re-reading true EOF and appending one
     *  CharSequenceInfinite.endChar sentinel after another) rather than throwing --
     *  the class's 1-minute Timeout rule would eventually fail this test, but a correct fix
     *  completes essentially instantly. */
    @Test
    public void abortLineOnAGrowingSourceAtRealEndOfInputDoesNotHang() throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        StringReader rdr = new StringReader("(foo"); // no trailing newline; reader hits real EOF
        CharSequenceReader csr = new CharSequenceReader(rdr, 100, 0, 2);
        ISource source = config.smtFactory.createSource(csr, null);
        Lexer lexer = new Lexer(config, source);

        lexer.abortLine();
    }
}
