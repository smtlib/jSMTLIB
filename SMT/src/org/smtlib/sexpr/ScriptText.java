package org.smtlib.sexpr;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.smtlib.IParser;
import org.smtlib.ISource;
import org.smtlib.SMT;

/**
 * The text of a script as a sequence of tokens, each with the whitespace and comments ("trivia") that
 * precede it, and an end-of-input token holding what follows the last real token (#222). Every character
 * of the text belongs to exactly one token or one trivia stretch, so {@link #exact()} reproduces the text
 * by construction. Tokens are found by jSMTLIB's own lexer, under the given configuration (the SMT-LIB
 * version matters for strings and quoted symbols); lexical errors are tokens too, so any text can be
 * represented.
 */
public final class ScriptText {

    /** The kinds of token */
    public enum Kind { LP, RP, ATOM, ERROR, EOD }

    /**
     * A token: its kind, its text, where it starts, and the trivia before it (from the end of the
     * previous token)
     */
    public record Token(Kind kind, String text, int start, String leading) {}

    /** Whitespace and comments at the start of a string: what the lexer skips before a token */
    private static final Pattern TRIVIA = Pattern.compile("(?:[\\p{Space}]+|;[^\\r\\n]*)*");

    private final String text;
    private final List<Token> tokens;

    private ScriptText(String text, List<Token> tokens) {
        this.text = text;
        this.tokens = Collections.unmodifiableList(tokens);
    }

    /** The text, split into tokens and trivia */
    public static ScriptText of(SMT.Configuration smtConfig, String text) {
        ISource source = smtConfig.smtFactory.createSource(text, null);
        Lexer lexer = new Lexer(smtConfig, source);
        List<Token> tokens = new ArrayList<>();
        int prev = 0;
        while (true) {
            Kind kind;
            try {
                ILexToken t = lexer.getToken();
                kind = t.isEOD() ? Kind.EOD : t.isLP() ? Kind.LP : t.isRP() ? Kind.RP
                        : t.isError() ? Kind.ERROR : Kind.ATOM;
            } catch (IParser.ParserException | IParser.AbortInputException | java.io.IOException e) {
                kind = Kind.ERROR;   // e.g. a control-X: the lexer has consumed it
            }
            int cur = Math.min(lexer.currentPos(), text.length());
            if (kind == Kind.EOD) {
                // what follows: trailing trivia, and any text after an end-of-input character
                tokens.add(new Token(Kind.EOD, "", text.length(), text.substring(prev)));
                break;
            }
            // every token but the end of input consumes at least one character
            if (cur <= prev) throw new IllegalStateException("the lexer did not advance at " + prev);
            Matcher m = TRIVIA.matcher(text).region(prev, cur);
            m.lookingAt();   // always matches (perhaps nothing): the trivia before the token
            int start = m.end();
            tokens.add(new Token(kind, text.substring(start, cur), start, text.substring(prev, start)));
            prev = cur;
        }
        return new ScriptText(text, tokens);
    }

    /** The original text */
    public String text() {
        return text;
    }

    /** The tokens, the last being the end-of-input token */
    public List<Token> tokens() {
        return tokens;
    }

    /** The text reassembled from the tokens and their trivia: always equal to {@link #text()} */
    public String exact() {
        StringBuilder sb = new StringBuilder(text.length());
        for (Token t : tokens) sb.append(t.leading()).append(t.text());
        return sb.toString();
    }

    /** The comments in the given trivia, each without its line terminator, in order */
    public static List<String> comments(String trivia) {
        List<String> list = new ArrayList<>();
        int i = 0;
        while ((i = trivia.indexOf(';', i)) >= 0) {
            int e = i;
            while (e < trivia.length() && trivia.charAt(e) != '\n' && trivia.charAt(e) != '\r') e++;
            list.add(trivia.substring(i, e));
            i = e;
        }
        return list;
    }

    /** All comments of the script, in order */
    public List<String> comments() {
        List<String> list = new ArrayList<>();
        for (Token t : tokens) list.addAll(comments(t.leading()));
        return list;
    }
}
