package org.smtlib.test.bugs;

import java.io.StringWriter;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.ICommand;
import org.smtlib.ISource;
import org.smtlib.SMT;
import org.smtlib.command.C_comment;
import org.smtlib.sexpr.Parser;

/**
 * Pins down issue #42 point 1: comment-forwarding to the solver
 * ({@code solver.comment(...)}) used to happen for only 5 of 32 command classes
 * ({@code C_get_info}, {@code C_get_option}, {@code C_set_info}, {@code C_set_logic},
 * {@code C_set_option}), via a {@code prefixText} field each of those five checked in its own
 * {@code execute()} -- with no stated rule for why those five and not the other 27.
 * <p>
 * Fixed by modeling a comment that appears immediately before a command as its own synthetic
 * {@link C_comment} pseudo-command, interleaved into the parsed command stream by
 * {@code Parser.parseCommand()} (using the lexer's existing lookahead -- {@code isEOD()}
 * already calls {@code peekToken()}, which populates {@code prefixCommentText} for the
 * upcoming token as a side effect, before that token is actually consumed). Every real
 * command-dispatch path just calls {@code command.execute(solver)} on whatever the parser
 * hands it, so a {@code C_comment} forwards itself to any solver uniformly, with no
 * per-command-class or per-dispatch-loop code needed -- and the old {@code prefixText}
 * field/mechanism is gone entirely.
 * <p>
 * A comment between a command's arguments is deliberately still not turned into its own
 * command and remains unforwarded, exactly as before -- but a trailing comment at the very
 * end of a script (with no following command) now is, since it turns out to fall out of the
 * same mechanism for free: {@code isEOD()} peeks the upcoming token before returning, which
 * populates {@code prefixCommentText} even when that upcoming token is the end-of-data marker
 * itself. The lexer's leading-content capturing group combines whitespace and comments
 * together, so plain whitespace with no actual comment must be (and is) excluded explicitly --
 * otherwise every command in a script would get a spurious, empty comment command in front of
 * it.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/42">issue #42</a>.
 * <p>
 * Most of this bug's observable behavior (a comment before a command being forwarded/echoed,
 * a mid-argument comment being ignored, a real multi-line comment echoing back verbatim, and
 * plain whitespace not becoming a spurious comment) is now covered by
 * {@code tests/bugs/comment_as_command.tst} (using {@code --echo} via its
 * {@code "; OPTIONS:"} directive).
 * <p>
 * The two tests remaining here stay JUnit tests because they are not reachable through the
 * real driver loop at all: a trailing comment at true end-of-script is never actually fetched
 * by {@code SMT.java}'s own command loop (its {@code while (!isEOD())} check short-circuits
 * before ever calling {@code parseCommand()} once more for it, even though the parser itself
 * would hand it back if asked directly -- confirmed by testing this exact scenario against the
 * real CLI, where the trailing comment's text never appears in --echo output), and a
 * {@code C_comment} built directly via its public constructor (as opposed to parsed from real
 * script text) is only reachable via direct API use.
 */
public class CommentAsCommandBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    private Parser parserFor(String text) {
        SMT.Configuration config = new SMT.Configuration();
        ISource source = config.smtFactory.createSource(text, null);
        return new Parser(config, source);
    }

    @Test
    public void trailingCommentAtEndOfScriptBecomesItsOwnCommentCommandToo() throws Exception {
        Parser p = parserFor("(exit)\n; trailing, nothing follows");

        ICommand first = p.parseCommand();
        Assert.assertTrue(first instanceof ICommand.Iexit);

        ICommand second = p.parseCommand();
        Assert.assertTrue("expected a trailing comment to become its own comment command, got: "
                + second, second instanceof C_comment);

        ICommand third = p.parseCommand();
        Assert.assertNull("nothing must remain after the trailing comment itself", third);

        // The source text has no trailing newline after "follows" -- write() must still
        // guarantee one, since whatever might print right after this comment must never risk
        // landing on the same line and being silently swallowed by it.
        StringWriter sw = new StringWriter();
        org.smtlib.sexpr.Printer.write(new SMT.Configuration(), sw, second);
        Assert.assertTrue("a printed comment must always end with a newline, got: " + sw,
                sw.toString().endsWith("\n"));
    }

    @Test
    public void programmaticallyConstructedMultiLineCommentGetsASemicolonOnEveryLine() throws Exception {
        // A comment built directly via the public constructor (not parsed) might have an
        // embedded newline with no leading ';' on the continuation line -- printing that
        // verbatim would silently end the comment early and let the continuation be
        // re-parsed as code, so write() must add one. It also has no trailing newline at all
        // here -- write() must add that too (see the trailing-comment case above for why).
        C_comment comment = new C_comment("line one\nline two");

        StringWriter sw = new StringWriter();
        org.smtlib.sexpr.Printer.write(new SMT.Configuration(), sw, comment);
        Assert.assertEquals(";line one\n;line two\n", sw.toString());
    }
}
