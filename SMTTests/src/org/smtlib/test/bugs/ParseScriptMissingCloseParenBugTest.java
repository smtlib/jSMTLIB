package org.smtlib.test.bugs;

import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.ICommand;
import org.smtlib.SMT;

/**
 * Pins down (and confirms the fix for) Parser.parseScript() looping forever at the end of
 * input when the script's closing parenthesis is missing. parseScript() expects the commands
 * enclosed in one pair of parentheses; its loop ran "while (!isRP())", and at the end of input
 * parseCommand() returns null without consuming anything, so a script lacking the final ')'
 * -- including one written without the enclosing ( ... ) at all, whose first command's '('
 * is then taken as the script's own -- never terminated. It now reports a parse error.
 */
public class ParseScriptMissingCloseParenBugTest {

    @Rule public Timeout timeout = new Timeout(30, TimeUnit.SECONDS);

    private ICommand.IScript parse(String text) throws Exception {
        SMT.Configuration config = new SMT.Configuration();
        config.log.clearListeners(); // the expected parse error is not of interest here
        var source = config.smtFactory.createSource(text, null);
        return config.smtFactory.createParser(config, source).parseScript();
    }

    @Test
    public void scriptWithoutEnclosingParenthesesTerminates() throws Exception {
        Assert.assertNull(parse("(set-logic ALL)\n(check-sat)\n"));
    }

    @Test
    public void scriptMissingOnlyTheFinalParenthesisTerminates() throws Exception {
        Assert.assertNull(parse("((set-logic ALL)\n(check-sat)\n"));
    }

    @Test
    public void wellFormedScriptStillParses() throws Exception {
        ICommand.IScript script = parse("((set-logic ALL)\n(check-sat))");
        Assert.assertNotNull(script);
        Assert.assertEquals(2, script.commands().size());
    }
}
