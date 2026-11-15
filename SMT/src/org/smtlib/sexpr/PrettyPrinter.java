package org.smtlib.sexpr;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.smtlib.sexpr.ScriptText.Kind;
import org.smtlib.sexpr.ScriptText.Token;

/**
 * Pretty-prints a script from its tokens (#222), with or without its comments. Only whitespace changes:
 * the tokens, with their exact text, stay in order, so the result parses to the same commands.
 * <ul>
 * <li>Each top-level form starts a line; one blank line is kept where the input had any between them.</li>
 * <li>A list that fits in the width, and holds no comment, is printed on one line.</li>
 * <li>Otherwise its head and, depending on the head, some arguments stay on the first line (e.g. the
 *     name, parameters and sort of define-fun; a first argument that is a list starts there even when it
 *     must itself be broken), and each other element starts a line, indented two
 *     columns more than the list's parenthesis; a keyword stays on the line of its value. A list whose
 *     first element is itself a list (bindings, sorted variables) aligns its elements one column in.
 *     Closing parentheses are stacked at the end of the last element.</li>
 * <li>With comments: a comment on its own line in the input is printed on its own line before the token
 *     it preceded; a comment that followed a token on the same line stays at the end of that line.</li>
 * </ul>
 * A script with a lexical error is returned unchanged: added whitespace could change how the erroneous
 * text is read.
 */
public final class PrettyPrinter {

    /** How many arguments stay on the head's line when a list is broken; others default to one */
    private static final Map<String, Integer> KEEP = Map.ofEntries(
            Map.entry("assert", 0), Map.entry("check-sat-assuming", 0), Map.entry("get-value", 0),
            Map.entry("define-fun", 3), Map.entry("define-fun-rec", 3), Map.entry("declare-fun", 3),
            Map.entry("define-sort", 2), Map.entry("declare-const", 2), Map.entry("declare-sort", 2),
            Map.entry("define-const", 2),
            Map.entry("set-option", 2), Map.entry("set-info", 2), Map.entry("set-logic", 1),
            Map.entry("echo", 1), Map.entry("push", 1), Map.entry("pop", 1));

    private final ScriptText script;
    private final List<Token> tokens;
    private final boolean withComments;
    private final int width;
    private final StringBuilder out = new StringBuilder();
    private int column = 0;
    /** Whether the current line ends with a comment, so that nothing more may go on it */
    private boolean lineHasComment = false;

    private PrettyPrinter(ScriptText script, boolean withComments, int width) {
        this.script = script;
        this.tokens = script.tokens();
        this.withComments = withComments;
        this.width = width;
    }

    /** The script pretty-printed in the given width, keeping its comments or not */
    public static String print(ScriptText script, boolean withComments, int width) {
        if (hasLexicalError(script)) return script.text();
        PrettyPrinter p = new PrettyPrinter(script, withComments, width);
        p.printScript();
        return p.out.toString();
    }

    /** Whether the script has a lexical error: an error token, text after an end-of-input character, or
     *  white space that SMT-LIB does not allow (vertical tab, form feed) */
    static boolean hasLexicalError(ScriptText script) {
        for (Token t : script.tokens()) {
            if (t.kind() == Kind.ERROR) return true;
            String lead = t.leading();
            for (int i = 0; i < lead.length(); i++) {
                char c = lead.charAt(i);
                if (c == ';') {
                    while (i + 1 < lead.length() && lead.charAt(i + 1) != '\n' && lead.charAt(i + 1) != '\r') i++;
                } else if (!Character.isWhitespace(c) || c == '\u000B' || c == '\f') {
                    return true;
                }
            }
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // The tree of lists and atoms, built from the parentheses
    // -----------------------------------------------------------------------

    /** An atom (first == last), or a list from its '(' token to its ')' token (last is -1 if unclosed) */
    private static final class Node {
        final int first;
        int last;
        final List<Node> children = new ArrayList<>();

        Node(int first, int last) {
            this.first = first;
            this.last = last;
        }

        boolean isList(List<Token> tokens) {
            return tokens.get(first).kind() == Kind.LP;
        }
    }

    private int next = 0;

    /** The node starting at token 'next', which is not the end-of-input token */
    private Node parseNode() {
        int i = next++;
        Node n = new Node(i, i);
        if (tokens.get(i).kind() != Kind.LP) return n;
        n.last = -1;
        while (tokens.get(next).kind() != Kind.EOD) {
            if (tokens.get(next).kind() == Kind.RP) {
                n.last = next++;
                return n;
            }
            n.children.add(parseNode());
        }
        return n;
    }

    // -----------------------------------------------------------------------
    // Printing
    // -----------------------------------------------------------------------

    private void printScript() {
        while (tokens.get(next).kind() != Kind.EOD) {
            Node n = parseNode();
            trailingComments(tokens.get(n.first));
            boolean blank = leadingComments(tokens.get(n.first), 0, true);
            startLine(0, blank);
            printNode(n, 0);
        }
        Token eod = tokens.get(tokens.size() - 1);
        trailingComments(eod);
        leadingComments(eod, 0, true);
        if (column > 0) out.append('\n');
    }

    /**
     * Prints the node where the output stands, breaking lines at the given indent. The comments before
     * its first token have been printed by the caller.
     */
    private void printNode(Node n, int indent) {
        if (!n.isList(tokens)) {
            token(n.first, indent);
            return;
        }
        if (fits(n)) {
            printFlat(n);
            return;
        }
        int lp = column;
        token(n.first, indent);
        int inner = lp + 2;
        List<Node> cs = n.children;
        int k = 0;
        if (!cs.isEmpty() && !cs.get(0).isList(tokens)) {
            // the head, then the arguments kept on its line
            child(cs.get(0), inner, false);
            k = 1;
            int keep = KEEP.getOrDefault(tokens.get(cs.get(0).first).text(), 1);
            // a first argument that is a list starts on the head's line even when it must be broken
            if (keep >= 1 && k < cs.size() && cs.get(k).isList(tokens) && !hasComment(cs.get(k))) {
                child(cs.get(k), inner, false);
                k++;
            }
            while (k < cs.size() && k <= keep && fitsOnLine(cs.get(k))) {
                child(cs.get(k), inner, false);
                k++;
            }
        } else if (!cs.isEmpty()) {
            inner = lp + 1;
            child(cs.get(0), inner, false);
            k = 1;
        }
        for (; k < cs.size(); k++) {
            Node c = cs.get(k);
            child(c, inner, true);
            if (isKeyword(c) && k + 1 < cs.size() && fitsOnLine(cs.get(k + 1))) {
                child(cs.get(++k), inner, false);
            }
        }
        if (n.last >= 0) {
            Token rp = tokens.get(n.last);
            trailingComments(rp);
            if (withComments && !ScriptText.comments(ownLines(rp.leading())).isEmpty()) {
                leadingComments(rp, inner, false);
                startLine(lp, false);
            }
            token(n.last, lp);
        }
    }

    /**
     * Prints a list element: its same-line comments at the end of the current line; then a line break (if
     * asked, or if a comment was printed) and its own-line comments; then the element, after a space if it
     * continues the line (except straight after the opening parenthesis)
     */
    private void child(Node c, int indent, boolean newLine) {
        Token first = tokens.get(c.first);
        trailingComments(first);
        boolean own = withComments && !ScriptText.comments(ownLines(first.leading())).isEmpty();
        if (newLine || own || lineHasComment) {
            leadingComments(first, indent, false);
            startLine(indent, false);
        } else if (!out.toString().endsWith("(")) {
            space();
        }
        printNode(c, indent);
    }

    /** Prints the node on one line (it fits and holds no comment) */
    private void printFlat(Node n) {
        if (!n.isList(tokens)) {
            emit(tokens.get(n.first).text());
            return;
        }
        emit("(");
        for (int k = 0; k < n.children.size(); k++) {
            if (k > 0) emit(" ");
            printFlat(n.children.get(k));
        }
        if (n.last >= 0) emit(")");
    }

    /** Whether the node, printed flat from the current column, fits and holds no comment */
    private boolean fits(Node n) {
        return column + flatLength(n) <= width && !hasInnerComment(n);
    }

    /** Whether the node, after a separating space, fits on the current line and holds no comment */
    private boolean fitsOnLine(Node n) {
        return column + 1 + flatLength(n) <= width && !hasComment(n);
    }

    private int flatLength(Node n) {
        if (!n.isList(tokens)) return tokens.get(n.first).text().length();
        int len = n.last >= 0 ? 2 : 1;
        for (int k = 0; k < n.children.size(); k++) len += (k > 0 ? 1 : 0) + flatLength(n.children.get(k));
        return len;
    }

    /** Whether a token of the node other than its first is preceded by a comment */
    private boolean hasInnerComment(Node n) {
        if (!withComments) return false;
        int end = n.last >= 0 ? n.last : lastToken(n);
        for (int i = n.first + 1; i <= end; i++) {
            if (!ScriptText.comments(tokens.get(i).leading()).isEmpty()) return true;
        }
        return false;
    }

    /** Whether any token of the node is preceded by a comment */
    private boolean hasComment(Node n) {
        return withComments && (!ScriptText.comments(tokens.get(n.first).leading()).isEmpty() || hasInnerComment(n));
    }

    private int lastToken(Node n) {
        if (n.last >= 0) return n.last;
        return n.children.isEmpty() ? n.first : lastToken(n.children.get(n.children.size() - 1));
    }

    private boolean isKeyword(Node n) {
        return !n.isList(tokens) && tokens.get(n.first).text().startsWith(":");
    }

    /** The part of a token's leading trivia from its first line break on */
    private String ownLines(String lead) {
        int nl = firstLineBreak(lead);
        return nl < 0 ? "" : lead.substring(nl);
    }

    /** Prints the comments that followed the previous token on its line, at the end of the current line */
    private void trailingComments(Token t) {
        if (!withComments || out.length() == 0) return;
        String lead = t.leading();
        int nl = firstLineBreak(lead);
        for (String c : ScriptText.comments(nl < 0 ? lead : lead.substring(0, nl))) {
            emit(" ");
            emit(c);
            lineHasComment = true;
        }
    }

    /**
     * Prints the comments on lines of their own before the given token, each on its own line at the given
     * indent; at top level one blank line is kept before a comment where the input had blank lines. Returns
     * whether blank lines followed the last comment (or, without comments, appeared at all).
     */
    private boolean leadingComments(Token t, int indent, boolean topLevel) {
        String rest = out.length() == 0 ? "\n" + t.leading() : ownLines(t.leading());
        if (rest.isEmpty()) return false;
        // lines[0] ends the previous token's line; the last line starts the token's own line
        String[] lines = rest.split("\\r\\n|\\r|\\n", -1);
        boolean blank = false;
        for (int i = 1; i < lines.length; i++) {
            List<String> cs = ScriptText.comments(lines[i]);
            if (cs.isEmpty()) {
                if (i < lines.length - 1) blank = true;   // a line of white space only
                continue;
            }
            if (!withComments) continue;
            startLine(indent, topLevel && blank);
            blank = false;
            emit(cs.get(0));
            lineHasComment = true;
        }
        return topLevel && blank;
    }

    private static int firstLineBreak(String s) {
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            if (c == '\n' || c == '\r') return i;
        }
        return -1;
    }

    /** Starts a new line at the given indent (reusing the current line if it holds only spaces), after a
     *  blank line if asked and anything has been printed */
    private void startLine(int indent, boolean blankLine) {
        int ls = out.lastIndexOf("\n") + 1;
        if (out.substring(ls).isBlank()) out.setLength(ls);
        else out.append('\n');
        if (blankLine && out.length() > 0) out.append('\n');
        column = 0;
        lineHasComment = false;
        indent(indent);
    }

    /** Prints a token's text, on a new line if the current one ends with a comment */
    private void token(int i, int indent) {
        if (lineHasComment) newline(indent);
        emit(tokens.get(i).text());
    }

    private void space() {
        emit(" ");
    }

    private void newline(int indent) {
        out.append('\n');
        column = 0;
        lineHasComment = false;
        indent(indent);
    }

    private void indent(int n) {
        for (int i = 0; i < n; i++) out.append(' ');
        column = n;
    }

    private void emit(String s) {
        out.append(s);
        int nl = s.lastIndexOf('\n');
        column = nl < 0 ? column + s.length() : s.length() - nl - 1;
    }
}
