package org.smtlib.test;

import org.junit.Assert;
import org.junit.Test;
import org.smtlib.AbstractSolver;

/** Tests for how pipelined reading finds the end of each response in a solver's output
 *  (AbstractSolver.responseEnd): an atom, a string literal, a quoted symbol, or one balanced
 *  S-expression; -1 while the response is not yet complete. */
public class PipelineResponseTests {

    /** The responses in the text, splitting as pipelined reading does */
    private static java.util.List<String> split(String text) {
        java.util.List<String> result = new java.util.ArrayList<>();
        int start = 0;
        while (true) {
            while (start < text.length() && Character.isWhitespace(text.charAt(start))) start++;
            int end = AbstractSolver.responseEnd(text, start);
            if (end < 0) return result;
            result.add(text.substring(start, end));
            start = end;
        }
    }

    @Test
    public void atoms() {
        Assert.assertEquals(java.util.List.of("success", "sat", "unsupported"), split("success\nsat\nunsupported\n"));
    }

    @Test
    public void errorsWithParenthesesAndQuotesInTheirText() {
        Assert.assertEquals(java.util.List.of("(error \"Expecting sort list '(': x\")", "success",
                "(error \"say \"\"hi\"\" (twice\")"),
                split("(error \"Expecting sort list '(': x\")\nsuccess\n(error \"say \"\"hi\"\" (twice\")\n"));
    }

    @Test
    public void multiLineSExpression() {
        Assert.assertEquals(java.util.List.of("((x 1)\n (y |a b)|))", "sat"), split("((x 1)\n (y |a b)|))\nsat\n"));
    }

    @Test
    public void stringAndQuotedSymbol() {
        Assert.assertEquals(java.util.List.of("\"a b\"", "|c d|"), split("\"a b\"\n|c d|\n"));
    }

    @Test
    public void incompleteResponses() {
        Assert.assertEquals(-1, AbstractSolver.responseEnd("(error \"unfinished", 0));
        Assert.assertEquals(-1, AbstractSolver.responseEnd("((x 1)\n", 0));
        // an atom or string at the end of what has arrived may continue
        Assert.assertEquals(-1, AbstractSolver.responseEnd("succ", 0));
        Assert.assertEquals(-1, AbstractSolver.responseEnd("\"ab\"", 0));
        Assert.assertEquals(-1, AbstractSolver.responseEnd("", 0));
    }
}
