package org.smtlib.test.bugs;

import java.util.concurrent.TimeUnit;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
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
 * Originally three tests, one per failure mode fixed: a direct, minimal call to
 * {@code Lexer.abortLine()} on a fixed CharSequence; the same but on a growing
 * {@code CharSequenceReader} at real end-of-input (previously hung rather than threw); and a
 * third, stronger reproduction driven through the real reachable path --
 * {@code SMT.doParser()} with {@code --abort} and interactive mode, given a command that
 * fails to parse on the last line of input with no trailing newline.
 * <p>
 * The latter two are now covered by {@code scripts/lexer_abort_line_no_trailing_newline.scr},
 * driven through the real CLI (stdin piped with no trailing newline, {@code --abort}) -- a
 * more faithful reproduction than the original in-process versions, since real interactive
 * input is always backed by a growing {@code CharSequenceReader} (confirmed against
 * {@code SMT.exec()}), never a bare, fixed {@code CharSequence}.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/72">issue #72</a>.
 * <p>
 * Stays a JUnit test: the one remaining failure mode (a plain, fixed {@code CharSequence},
 * e.g. a literal Java String) is only reachable via direct {@code Lexer}/{@code ISource} API
 * use -- every real CLI input path (files, stdin, --text) wraps its input in a growing
 * {@code CharSequenceReader} instead (see {@code SMT.exec()}), so this specific case is never
 * what a script test would exercise.
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
}
