package org.smtlib;

import java.io.IOException;

import org.smtlib.IParser.ParserException;
import org.smtlib.sexpr.ILexToken;

/** Reading the lexical tokens of a source, one at a time, with one token of lookahead. Lexer
 *  implements it, and IParser extends it. */
public interface ILexer {

    /** Returns the next token, advancing past it */
    ILexToken getToken() throws IOException, ParserException;

    /** Returns the next token without advancing past it; the next getToken() returns it */
    ILexToken peekToken() throws IOException, ParserException;

    /** Returns the next token, advancing past it only if it is an instance of clazz */
    ILexToken getToken(Class<?> clazz) throws IOException, ParserException;

    /** Returns true if the next token is a left parenthesis (without consuming it) */
    boolean isLP() throws IOException, ParserException;

    /** Returns true if the next token is a right parenthesis (without consuming it) */
    boolean isRP() throws IOException, ParserException;

    /** Returns true if the next token is the end of data (without consuming it) */
    boolean isEOD() throws IOException, ParserException;

    /** Skips the rest of the current line, including a token already looked ahead at */
    void abortLine() throws IOException;

    /** Returns the first token in text, read by a parser from config's factory, so positions refer
     *  to text and the parser's lexical checks (which log their errors) apply */
    static ILexToken getToken(SMT.Configuration config, String text) throws IOException, ParserException {
        IParser parser = config.smtFactory.createParser(config, config.smtFactory.createSource(text, null));
        return parser.getToken();
    }
}
