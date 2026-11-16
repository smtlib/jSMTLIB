/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.sexpr;

import java.io.IOException;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.*;

import org.smtlib.*;
import org.smtlib.ICommand.IScript;
import org.smtlib.IExpr.*;
import org.smtlib.impl.*;
import org.smtlib.impl.SMTExpr.Keyword;
import org.smtlib.impl.SMTExpr.StringLiteral;
import org.smtlib.impl.SMTExpr.Symbol;

/** Parses the standard SMT-LIB concrete syntax to produce ASTs of objects that
 * are instances of the org.smtlib.* interfaces.
 */
public class Parser extends Lexer implements IParser {
    /** A handle to the parent SMTConfig object, in order to see command-line options
     * etc. that are fields of smtConfig */
    final private SMT.Configuration smtConfig;

    /** Returns a handle to the parent SMTConfig object, in order to see command-line options
     * etc. that are fields of smtConfig */
    public SMT.Configuration smt() { return smtConfig; }

    /** The most recent error, or null */
    public /*@ Nullable */ IResponse.IError lastError = null;

    public /*@ Nullable */ IResponse.IError lastError() { return lastError; }

    /** Whether the command being parsed (or last returned) had a recoverable syntax error */
    protected boolean commandHasError = false;

    /** Whether any such error was an invalid character, which the type checker does not see */
    protected boolean commandHasLexicalError = false;

    @Override
    public boolean commandHasError() { return commandHasError; }

    @Override
    public boolean commandHasLexicalError() { return commandHasLexicalError; }

    /** The (common) factory used to generate objects */
    final protected IExpr.IFactory factory;

    /** Returns an IPos object for the given character start and end 
     * positions and including a reference to the parser's source object. 
     * @param start the start character position (counting from 0)
     * @param end the end character position (one past the last actual character to be included)
     * @return the IPos object representing the character range within the parser's current source
     */
    public /*@Nullable*//*@ReadOnly*/ IPos pos(/*@Nullable*//*@ReadOnly*/IPos start, /*@Nullable*//*@ReadOnly*/IPos end) { 
        if (start == null || end == null) return null;
        return pos(start.charStart(),end.charEnd()); 
    }

    /** Returns an IPos object for the given character start and end 
     * positions and including a reference to the parser's source object. 
     * @param start the start character position (counting from 0)
     * @param end the end character position (one past the last actual character to be included)
     * @return the IPos object representing the character range within the parser's current source
     */
    public /*@Nullable*/ IPos pos(int start, int end) { 
        return new Pos(start,end,source()); 
    } // FIXME Use factory instead of new Pos?

    /** Creates a Parser using an SMT configuration object and a source for
     * characters; ordinarily use a factory to obtain a parser.
     */
    public Parser(SMT.Configuration smtConfig, ISource src) {
        super(smtConfig, src);
        this.smtConfig = smtConfig;
        this.factory = smtConfig.exprFactory;
    }


    // See the documentation in the interface
    @Override
    public /*@Nullable*/ICommand.IScript parseScript() throws IOException {
        // FIXME - review/fix the following comment
        // NOTE: interactive is set false here because it is only ever used for parsing exec scripts
        // if it is used to parse top-level scripts, we have to pass in the appropriate value
        boolean interactive = smtConfig.interactive;
        IScript scr;
        try {
            StringLiteral filename;
            if (!isLP()) {
                filename = parseStringLiteral();
                    scr = (Script) smtConfig.commandFactory.script(filename, null);
            } else {
                // This loop skips over invalid commands, producing error messages (parseCommand
                // returns null); the resulting script is valid, but misses the invalid entries
                smtConfig.interactive = false;
                ICommand s;
                List<ICommand> res = new LinkedList<ICommand>();
                parseLP();
                boolean anyError = false;
                while (!isRP()) {
                    // Without this, a script lacking its closing parenthesis (e.g. one written
                    // without the enclosing ( ... ), whose first command's '(' was taken as the
                    // script's) loops forever at the end of input: parseCommand() returns null
                    // there without consuming anything.
                    if (isEOD()) {
                        throw new ParserException(pos(currentPos()-1, currentPos()),
                                "Unexpected end of input: the script is missing its closing parenthesis");
                    }
                    s = parseCommand();
                    if (s != null) res.add(s);
                    else anyError = true;
                }
                parseRP();
                if (anyError) return null;
                scr = (Script) smtConfig.commandFactory.script(null, res);
            }
            if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Completed input");
        } catch (ParserException e) {
            if (e.getMessage() != null) {
                smtConfig.log.logError(smt().responseFactory.error(e.pos(), e.getMessage()));
            }
            return null;
        } finally {
            smtConfig.interactive = interactive;
        }
        return scr;
    }

    /** This field is used to communicate the beginning LP while parsing commands */
    public /*@Nullable*/ ILexToken savedlp;

    /** The command most recently returned by parseCommand(), or null once its own
     *  same-line trailing text (if any) has already been attached (see the top of
     *  parseCommand()'s main loop) or it was itself a C_comment/null (neither of which can
     *  have same-line trailing text of their own attached to them). Deliberately attached
     *  retroactively, on the NEXT call's own pre-existing isEOD() lookahead, rather than by
     *  forcing an extra lookahead right when this command finishes parsing -- forcing it
     *  early was tried first and reverted, because it makes the underlying reader look for
     *  more input earlier than before, which shifted interactive-mode prompt timing. This
     *  field is safe to set after the fact because trailingText is purely descriptive
     *  metadata (used only if something later prints this command back out), never
     *  consulted during execution. */
    private Command lastReturnedCommand;

    /** Whether the caller discards the rest of the line after an error (with --abort on interactive
     *  standard input, SMT.doParser calls abortLine), so the parser does not skip ahead itself:
     *  that could consume, or wait for, lines typed after the error */
    private boolean recoverByLine() {
        return smtConfig.abort && smtConfig.interactive;
    }

    /** This field is used only to communicate the position of the name of a command to the command creator
     * (instead of using method arguments).
     */
    public /*@ReadOnly*/ ISymbol commandName;

    /** Parses the next text in the source as a SMT-LIB command; if an error occurs, the error is logged
     * and the method skips through a matching number of right parentheses
     *  @return returns the parsed command, or EOD.eod if the end of input has been reached, 
     *  or null if no valid command could be parsed
     */
    //@ nullable
    /*@Nullable*/
    /*@Mutable*/
    public Command parseCommand() throws IOException {
        boolean savedTopLevel = smtConfig.topLevel;
        commandHasError = false;
        commandHasLexicalError = false;
        Command command = null;
        try {
            while (true) { // The while loop is just so that AbortInputException can cause a retry
                // After an error, the rest of the command is skipped, back to this depth: through the
                // command's closing parenthesis, however deeply nested the error is (#238)
                int commandDepth = depth;
                try {
                    ILexToken rp = null;
                    boolean atEnd = isEOD();
                    // isEOD() (above) already peeked the upcoming token -- even the synthetic
                    // end-of-data marker itself, if that's what's next -- which as a side
                    // effect populates prefixCommentText for it without consuming it. So a
                    // comment immediately before the next command, OR a trailing comment with
                    // no command left to precede, both surface here the same way. Return it as
                    // its own synthetic command now; if it precedes a real command, that
                    // command is still fully unconsumed and parses normally on the next call to
                    // parseCommand(). Comments elsewhere (between a command's arguments) are
                    // deliberately not captured this way and remain unforwarded, as before.
                    // prefixCommentText's capturing group combines whitespace AND comments
                    // (see Lexer.combined's group 1), so it is non-null whenever any
                    // whitespace at all precedes the next token -- not only when a real
                    // comment does. Only genuinely non-blank content (i.e. an actual comment)
                    // should become a C_comment; plain whitespace must not.
                    //
                    // The same isEOD() call also populates sameLineTrailingText, if the
                    // whitespace/comment run it just scanned started on the same physical line
                    // as whatever token preceded it (see Lexer.getNextToken()) -- i.e. it
                    // shares a line with the command this Parser most recently returned, not
                    // with whatever is parsed next. Attach it there now, at exactly the point
                    // this lookahead already happened before this feature existed, so that
                    // nothing about read/prompt timing changes (see lastReturnedCommand's own
                    // doc comment for why this isn't done eagerly right after that command
                    // finishes parsing instead).
                    if (sameLineTrailingText != null) {
                        if (lastReturnedCommand != null) lastReturnedCommand.setTrailingText(sameLineTrailingText);
                        sameLineTrailingText = null;
                    }
                    lastReturnedCommand = null;
                    if (prefixCommentText != null && !prefixCommentText.trim().isEmpty()) {
                        String text = prefixCommentText;
                        int start = prefixCommentStart, end = prefixCommentEnd;
                        prefixCommentText = null;
                        org.smtlib.command.C_comment c = new org.smtlib.command.C_comment(text);
                        setPos(c, pos(start, end));
                        return c;
                    }
                    prefixCommentText = null;
                    if (atEnd) return null;
                    try {
                        savedlp = parseLP();
                    } catch (ParserException e) {
                        // Stray token at command level (e.g. a bare identifier, or a comment
                        // missing its leading ';' so its words are lexed as bare tokens instead);
                        // an earlier bad command was skipped through its end, so this is a fresh
                        // problem, not a leftover of that one. A fresh problem previously wasn't
                        // reported at all unless --verbose was on, which in interactive mode
                        // looked like the parser was just hanging (it was actually blocking on
                        // getToken(), below, waiting for a '(' that was never coming), and in a
                        // file could silently discard everything after the stray token if no
                        // further '(' ever appeared.
                        // peekToken() re-examines the same token parseLP() just failed on
                        // (parseLP() never consumes on failure), so this is safe to call here.
                        ParserException reported = error(
                                peekToken(),
                                "Expected a command (beginning with '(') or a comment (beginning with ';') here, not a #");
                        if (reported.getMessage() != null) smtConfig.log.logError(smtConfig.responseFactory.error(reported.pos(), reported.getMessage()));
                        if (recoverByLine()) return null;
                        // Skip to the next LP, matching old null-return behavior -- but log
                        // how many tokens were skipped, for debuggability.
                        int skipped = 0;
                        do { if (isEOD()) return null; getToken(); ++skipped; } while (!isLP());
                        if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Skipped " + skipped + " stray token(s) while recovering to the next command");
                        return null;
                    }
                    smtConfig.topLevel = false;
                    Symbol sym = parseSymbolOrReservedWord("Expected a symbol here, not a #");
                    if (sym == null) {
                        if (!recoverByLine()) skipToDepth(commandDepth);
                        return null;
                    }
                    commandName = sym;
                    String name = sym.value();
                    try {
                        // To create a command, we invoke the 'parse' method (that has a Parser argument)
                        // in the class corresponding to the given command name.
                        // The parse method is supposed to consume its argument from the parser source;
                        // the method does not parse the final right-parenthesis or check that there is no
                        // extraneous material beyond the last argument parsed - those checks are done here
                        // for all commands. We also set the IPos value for the command here.
                        // If an error occurs in parsing the command, an error message should be logged and
                        // null returned (if null is returned, an error message is expected to have been logged).

                        // This call translates a name to the class that implements the command with that name.
                        // The user can change the lookup behavior by assigning a new command finder object in
                        // the configuration
                        Class<? extends ICommand> clazz = smt().commandFinder.findCommand(name);
                        if (clazz == null) {
                            lastError = smtConfig.log.logError(smtConfig.responseFactory.error(sym.pos(), "Unknown command: " + name));
                            command = null;
                        } else {
                            // Call the static parser method of the command class; that will create an
                            // instance of the appropriate command, initialized according to the parsed data.
                            // If the parse fails, null is returned and an error will have been logged.
                            Method m = clazz.getMethod("parse",Parser.class);
                            command = (Command)m.invoke(null,this);
                            rp = null;
                            if (command != null) {
                                if (!isRP()) {
                                    lastError = smtConfig.log.logError(smtConfig.responseFactory.error(
                                            peekToken().pos(),
                                            "Too many arguments or extraneous material after the command or missing right parenthesis"));
                                } else {
                                    rp = parseRP();
                                }
                            }
                        }
                    } catch (InvocationTargetException ex) {
                        Throwable target = ex.getTargetException();
                        if (target instanceof ParserException) {
                            throw (ParserException) target;
                        }
                        if (target instanceof IParser.AbortInputException) {
                            throw (IParser.AbortInputException) target;
                        }
                        if (target instanceof IOException) {
                            throw (IOException) target;
                        }
                        // Resource exhaustion is reported by its error alone; a stack trace is noise
                        if (target instanceof StackOverflowError) {
                            lastError = smtConfig.log.logError(smtConfig.responseFactory.error(sym.pos(), "Stack overflow occurred while parsing input"));
                            throw new ParserException(null,null);
                        } else if (target instanceof OutOfMemoryError) {
                            lastError = smtConfig.log.logError(smtConfig.responseFactory.error(sym.pos(), "Out of memory error occurred while parsing input"));
                            throw new ParserException(null,null);
                        } else {
                            ex.printStackTrace(smtConfig.log.getDiag());
                            lastError = smtConfig.log.logError(smtConfig.responseFactory.error(sym.pos(), target.toString()));
                            target.printStackTrace(smtConfig.log.getDiag());
                        }
                    }
                    if (command == null || rp == null) {
                        command = null;
                        if (!recoverByLine()) skipToDepth(commandDepth);
                    }
                    if (command != null) {
                        setPos(command,pos(savedlp.pos(),rp.pos()));
                        // Remember this command so that the NEXT parseCommand() call's own
                        // (already-existing, unmoved) isEOD() lookahead -- see the top of this
                        // loop -- can retroactively attach any sameLineTrailingText it finds to
                        // it. Forcing that lookahead early, right here, was tried first and
                        // reverted: it forces the underlying reader to look for more input
                        // before it otherwise would (e.g. before this command's own response is
                        // even processed), which shifted interactive-mode prompt timing.
                        // Attaching it later, at the same point the lookahead already
                        // naturally happens, changes nothing about when anything is read.
                        lastReturnedCommand = command;
                    }
                } catch (IParser.AbortInputException e) {
                    smtConfig.log.logOut("Input aborted");
                    smtConfig.topLevel = true;
                    continue;
                } catch (ParserException e) {
                    // FIXME - is an RP a good recovery token? -- used to be end of line
                    if (e.getMessage() != null) lastError = smtConfig.log.logError(smtConfig.responseFactory.error(e.pos(),e.getMessage()));
                    if (!recoverByLine()) {
                        try { skipToDepth(commandDepth); } catch (ParserException ex) { /* already recovering */ }
                    }
                }
                break;
            }
        } catch (IOException e) {
            throw e; // a failed read, not a parse error
        } catch (Exception e) {
            IPos pos = new Pos(0,0,null);
            lastError = smtConfig.responseFactory.error(pos,"Error while parsing command: " + e);
            e.printStackTrace(smtConfig.log.getDiag());
            smtConfig.log.logError(lastError);
        } finally {
            smtConfig.topLevel = savedTopLevel;
        }
        return command;
    }

    /** A helper check, called by command-specific parse methods in which the commands have no arguments */
    //@ requires savedlp != null && commandName != null;
    public boolean checkNoArg() throws IOException {
        try {
            if (!isRP()) {
                if (isEOD()) {
                    smtConfig.log.logError(smtConfig.responseFactory.error(
                            pos(savedlp.pos(),savedlp.pos()),
                            "The input ends with an unmatched left parenthesis"));
                    return false;
                }
                smtConfig.log.logError(smtConfig.responseFactory.error(
                        peekToken().pos(),
                        "A " + commandName + " command takes no arguments")); 
                return false;
            } else {
                return true;
            }
        } catch (ParserException e) {
            smtConfig.log.logError(smt().responseFactory.error(
                    e.pos(),
                    "A failure occurred while parsing a command: " + e));
            return false;
        }

    }


    /** Parses an Sexpr
     * @return an Sexpr or null if no more input
     * @throws ParserException if a parsing problem occurred, such as an invalid token or mismatched parentheses
     */
    // FIXME - should this log errors and return null instead of throwing an exception?
    /*@Nullable*/
    public ISexpr parseSexpr() throws IOException, ParserException {
        if (isEOD()) return null;
        ILexToken t = getToken();
        if (t.isRP()) {
            throw new ParserException(t.pos(),"Unexpected right parenthesis");
        }
        if (t.isLP()) {
            boolean saved = smtConfig.topLevel;
            try {
                smtConfig.topLevel = false;
                return parseSeq(t);
            } finally {
                smtConfig.topLevel = saved;
            }
        } 
        if (t.isError()) throw new ParserException(t.pos(), lexMessage(t));
        if (!(t instanceof ISexpr)) {
            throw new ParserException(t.pos(),"Token is not an S-expression token: " + t.getClass());
        }
        return (ISexpr)t;
    }

    /** Parses and adds Sexpr to a list until parseSexpr returns null (indicating
     * a RightParen has been seen or end of input or an error)
     * @return a SExpr.Seq containing the sequence of SExpr seen
     * @throws ParserException FIXME - no more of these?
     */
    public Sexpr.Seq parseSeq(ILexToken lp) throws IOException, ParserException {
        // Iterative, with explicit stacks of open lists and their left parentheses, since
        // solver output such as a z3 proof can nest deeper than the Java stack allows
        java.util.ArrayDeque<Sexpr.Seq> open = new java.util.ArrayDeque<>();
        java.util.ArrayDeque<ILexToken> lps = new java.util.ArrayDeque<>();
        Sexpr.Seq seq = new Sexpr.Seq(); // deliberate direct construction -- see ISexpr's class comment

        while (true) {
            ILexToken token = getToken();
            if (token.isRP()) {
                seq.setPos(pos(lp.pos(),token.pos()));
                if (open.isEmpty()) return seq;
                Sexpr.Seq done = seq;
                seq = open.pop();
                lp = lps.pop();
                seq.sexprs().add(done);
            } else if (token.isEOD()) {
                throw new IParser.ParserException(pos(lp.pos(),lp.pos()),"Unbalanced parentheses at end of input");
            } else if (token.isLP()) {
                open.push(seq);
                lps.push(lp);
                seq = new Sexpr.Seq();
                lp = token;
            } else if (token.isError()) {
                throw new ParserException(token.pos(), lexMessage(token));
            } else if (token instanceof ISexpr) {
                seq.sexprs().add((ISexpr)token);
            } else {
                // Every token the lexer makes is one of the above
                throw new ParserException(token.pos(), "INTERNAL ERROR: unexpected token " + token);
            }
        }
    }

    /** Parses a qualified identifier (either a symbol, a parameterized identifier, or an as identifier)
     * from the token stream, returning null (with logged error messages) if there is not one.
     */
    @Override
    public /*@Nullable*/IQualifiedIdentifier parseQualifiedIdentifier() throws IOException, ParserException {
        if (!isLP()) {
            return parseSymbol();
        } else {
            ILexToken lp = parseLP(); // will succeed since isLP() was true
            ISymbol head = parseSymbolOrReservedWord("Expected a symbol here, not a #");
            if (head.value().equals(Utils.AS)) {
                return parseAsIdentifierRest(lp);
            } else if (head.value().equals(Utils.PARAM)) {
                return parseIdentifierRest(lp);
            } else {
                throw error(head.pos(), "Invalid beginning of an identifier: expected either 'as' or '_' here");
            }
        }
    }

//    private <T extends IPos.IPosable> T setPos(T p, IPos pos) { p.setPos(pos); return p; }

    /** Parses an 'as' identifier, presuming the left-paren and the 'as' are already parsed,
     * from the token stream, returning null (with logged error messages) if there is not one.
     */
    private /*@Nullable*/ IAsIdentifier parseAsIdentifierRest(ILexToken lp) throws IOException, ParserException {
        IIdentifier name = parseIdentifier();
        ISort sort = parseSort(null);
        ILexToken rp = parseRP();
        IPos pos = pos(lp.pos(),rp.pos());
        return setPos(smtConfig.exprFactory.id(name,sort),pos);
    }

    /** Parses an identifier (either symbol or parameterized identifier) from the token
     * stream, returning null with logged error messages if there is not one.
     */
    public /*@Nullable*/IIdentifier parseIdentifier() throws IOException, ParserException {
        if (!isLP()) {
            return parseSymbol();
        } else {
            ILexToken lp = parseLP();
            ISymbol head = parseSymbolOrReservedWord("Expected a symbol here, not a #");
            if (head.value().equals(Utils.PARAM)) {
                return parseIdentifierRest(lp);
            } else {
                throw error(head.pos(), "Invalid beginning of an identifier: expected a '_' here");
            }
        }
    }

    /** Parses a parameterized identifier from the token stream, presuming the left
     * parenthesis and the underscore character are already read, return null with 
     * logged error messages if there is not one.
     * @param lp the token for the left parenthesis that starts the identifier
     * @return the token or null
     * @throws ParserException if unrecoverable error occurs
     */
    private IIdentifier parseIdentifierRest(ILexToken lp) throws IOException, ParserException {
        ISymbol name = parseSymbol();
        List<IIndex> indices = new LinkedList<IIndex>();
        do {
            if (isEOD()) {
                throw new ParserException(pos(lp.pos().charStart(),currentPos()), "Unexpected end of data while parsing a parameterized identifier");
            }
            ILexToken peek = peekToken();
            if (peek instanceof Symbol) {
                indices.add(parseSymbol());
            } else if (peek instanceof IHexLiteral) {
                indices.add(parseHex());
            } else if (peek instanceof IBinaryLiteral) {
                indices.add(parseBinary());
            } else {
                indices.add(parseNumeral());
            }
        } while (!isRP());
        ILexToken rp = parseRP();
        IPos pos = pos(lp.pos(), rp.pos());
        return setPos(smtConfig.exprFactory.id(name, indices), pos);
    }

    /** Parses an expression, returning null with error messages if there is not a valid
     * expression in the token stream.
     */
    @Override
    public /*@Nullable*/IExpr parseExpr() throws IOException, ParserException {
        // Here we suffer a bit for using a hand-written top-down parser.
        // An IExpr can be
        //        literal
        //        symbol
        //        ( _ symbol index+ )
        //        ( as identifier sort )
        //        ( ! ...
        //        ( forall ...
        //        ( exists ...
        //        ( lambda ...
        //        ( let ...
        //        ( symbol ...
        //        ( ( _ symbol ...
        //        ( ( as ...
        if (!isLP()) {
            ILexToken token = getToken();
            if (token instanceof SMTExpr.Error) throw new ParserException(token.pos(), lexMessage(token));
            if (token instanceof IExpr) return (IExpr)token; // FIXME - do we need to check that this is just a literal or symbol
            throw error(token.pos(), "Expected an expression here");
        }
        ILexToken lp = getToken();
        IQualifiedIdentifier head;
        if (!isLP()) {
            head = parseSymbolOrReservedWord("Expected an identifier or reserved word here, not a #");
        } else {
            head = parseQualifiedIdentifier();
        }
        // head is now guaranteed non-null (throws on error)
        if (head instanceof ISymbol) { // in particular we want reserved words here
            String s = ((ISymbol)head).value();
            if (Utils.FORALL.equals(s)) {
                List<IDeclaration> decls = parseDeclarations();
                IExpr expr = parseExpr();
                ILexToken rp = parseRP();
                return setPos(smtConfig.exprFactory.forall(decls, expr), pos(lp.pos(), rp.pos()));
            } else if (Utils.EXISTS.equals(s)) {
                List<IDeclaration> decls = parseDeclarations();
                IExpr expr = parseExpr();
                ILexToken rp = parseRP();
                return setPos(smtConfig.exprFactory.exists(decls, expr), pos(lp.pos(), rp.pos()));
            } else if (Utils.LAMBDA.equals(s)) {
                List<IDeclaration> decls = parseDeclarations();
                IExpr expr = parseExpr();
                ILexToken rp = parseRP();
                return setPos(smtConfig.exprFactory.lambda(decls, expr), pos(lp.pos(), rp.pos()));
            } else if (Utils.LET.equals(s)) {
                List<IBinding> decls = parseBindings();
                IExpr expr = parseExpr();
                ILexToken rp = parseRP();
                return setPos(smtConfig.exprFactory.let(decls, expr), pos(lp.pos(), rp.pos()));
            } else if (Utils.MATCH.equals(s)) {
                IExpr scrutinee = parseExpr();
                List<IExpr.IMatchCase> cases = parseList(this::parseMatchCase, "match case", true);
                ILexToken rp = parseRP();
                return setPos(smtConfig.exprFactory.match(scrutinee, cases), pos(lp.pos(), rp.pos()));
            } else if (Utils.AS.equals(s)) {
                return parseAsIdentifierRest(lp);
            } else if (Utils.PARAM.equals(s)) {
                return parseIdentifierRest(lp);
            } else if (Utils.ATTRIBUTE.equals(s)) {
                IExpr expr = parseExpr();
                List<IAttribute<?>> list = parseTermAttributeSequence();
                ILexToken rp = parseRP();
                if (list.isEmpty()) {
                    throw new ParserException(pos(lp.pos(), rp.pos()), "An annotated term must have at least one attribute");
                }
                return setPos(smtConfig.exprFactory.attributedExpr(expr,list),pos(lp.pos(), rp.pos()));
            }
        }
        List<IExpr> list = new LinkedList<IExpr>();
        while (!isRP()) {
            if (isEOD()) {
                throw new ParserException(pos(lp.pos().charStart(),currentPos()), "Unexpected end of data while parsing a sequence of expressions");
            }
            list.add(parseExpr());
        }
        ILexToken rp = parseRP();
        IPos pos = pos(lp.pos(), rp.pos());
        // (f) is not a term; reported, then kept as an application with no arguments so that
        // type checking reports it too
        if (list.isEmpty()) recoverableError(pos, "A function application must have at least one argument");
        return setPos(smtConfig.exprFactory.fcn(head,list), pos);
    }

    /** Parses a parenthesized sequence of IDeclaration items */
    public List<IDeclaration> parseDeclarations() throws IOException, ParserException {
        return parseList(this::parseDeclaration, "declaration", true);
    }

    /** Parses a parenthesized sequence of let-bindings */
    public List<IBinding> parseBindings() throws IOException, ParserException {
        return parseList(this::parseBinding, "binding", true);
    }

    /** Parses a selector declaration "(symbol sort)" */
    @Override
    public IExpr.ISelector parseSelector() throws IOException, ParserException {
        ILexToken lp = parseLP();
        ISymbol symbol = parseSymbol();
        ISort sort = parseSort(null);
        ILexToken rp = parseRP();
        return setPos(smtConfig.exprFactory.selector(symbol, sort), pos(lp.pos(), rp.pos()));
    }

    /** Parses a constructor declaration "(symbol selector*)" */
    @Override
    public IExpr.IConstructor parseConstructor() throws IOException, ParserException {
        ILexToken lp = parseLP();
        ISymbol symbol = parseSymbol();
        List<IExpr.ISelector> selectors = new LinkedList<>();
        while (!isRP() && !isEOD()) {
            selectors.add(parseSelector());
        }
        ILexToken rp = parseRP();
        return setPos(smtConfig.exprFactory.constructor(symbol, selectors), pos(lp.pos(), rp.pos()));
    }

    /** Parses a datatype declaration: "( constructor+ )" or "( par ( symbol+ ) ( constructor+ ) )" */
    @Override
    public ISort.IDatatype parseDatatype() throws IOException, ParserException {
        ILexToken lp = parseLP();
        List<IExpr.IConstructor> constructors = new LinkedList<>();
        List<IExpr.ISymbol> typeParams = null;
        if (!isLP()) {
            ISymbol par = parseSymbolOrReservedWord("Expected 'par' or a constructor beginning with '(' here, not a #");
            if (!"par".equals(par.value()))
                throw new ParserException(par.pos(), "Expected 'par' keyword here");
            typeParams = parseList(this::parseSymbol, "type parameter", false);
            ILexToken lp2 = parseLP();
            while (!isRP() && !isEOD()) constructors.add(parseConstructor());
            parseRP();
        } else {
            while (!isRP() && !isEOD()) constructors.add(parseConstructor());
        }
        ILexToken rp = parseRP();
        return setPos(smtConfig.exprFactory.datatype(constructors, typeParams), pos(lp.pos(), rp.pos()));
    }

    /** Parses a function declaration "( symbol ( sorted_var* ) sort )" used in define-funs-rec */
    @Override
    public IExpr.IFunctionDeclaration parseFunctionDeclaration() throws IOException, ParserException {
        ILexToken lp = parseLP();
        ISymbol symbol = parseSymbol();
        List<IDeclaration> params = parseList(this::parseDeclaration, "declaration", true);
        ISort sort = parseSort(null);
        ILexToken rp = parseRP();
        return setPos(smtConfig.exprFactory.functionDeclaration(symbol, params, sort), pos(lp.pos(), rp.pos()));
    }




    /** Parses a declaration "(id sort)", returning null with error messages if an error occurs */
    @Override
    public IDeclaration parseDeclaration() throws IOException, ParserException {
        ILexToken lp = parseLP();
        ISymbol sym = parseSymbol();
        ISort sort = parseSort(null);
        ILexToken rp = parseRP();
        return setPos(smtConfig.exprFactory.declaration(sym,sort), pos(lp.pos(), rp.pos()));
    }

    /** Parses a binding "(id expression)", returning null with error messages if an error occurs */
    @Override
    public IBinding parseBinding() throws IOException, ParserException {
        ILexToken lp = parseLP();
        ISymbol sym = parseSymbol();
        IExpr expr = parseExpr();
        ILexToken rp = parseRP();
        return setPos(smtConfig.exprFactory.binding(sym,expr), pos(lp.pos(), rp.pos()));
    }

    /** Parses a parenthesized list of elements using the given element parser.
     * @param elementParser  lambda that parses one element
     * @param kind  singular noun describing the element type (e.g. "term"), used in error messages
     * @param allowEmpty  if false, throws when the list is empty
     */
    public <T> List<T> parseList(IParser.ElementParser<T> elementParser, String kind, boolean allowEmpty) throws IOException, ParserException {
        ILexToken next = peekToken();
        if (!next.isLP()) throw new ParserException(next.pos(), "Expected a parenthesized list of " + kind + "s beginning here");
        ILexToken lp = parseLP();
        List<T> list = new LinkedList<T>();
        while (!isRP() && !isEOD()) {
            list.add(elementParser.parse());
        }
        ILexToken rp = parseRP();
        if (!allowEmpty && list.isEmpty()) throw new ParserException(pos(lp.pos().charStart(), rp.pos().charEnd()), "Expected a parenthesized list of at least one " + kind);
        return list;
    }

    /** Parses a symbol, returning null with messages and not advancing the parser if an error occurs */
    @Override
    public /*@Nullable*/Symbol parseSymbol() throws IOException, ParserException {
        return parseSymbol("Expected a symbol here, not a #");
    }

    /** Parses a symbol (but not a reserved word unless the configuration field 'relax' is true), 
     * returning null with messages if an error occurs; the parser is advanced only if an actual symbol is parsed.  The error message
     * is given by the argument; it may contain a '#' character that will be replaced by the
     * kind() of the token actually observed; if the argument is null, no error message is
     * emitted. */
    public /*@Nullable*/Symbol parseSymbol(/*@Nullable*/String msg) throws IOException, ParserException {
        ILexToken token = peekToken();
        if (token instanceof Symbol) {
            ISymbol sym = (ISymbol)token;
            if (smtConfig.isReservedWord(sym.value())) {
                throw error(token.pos(),"A reserved word may not be used as a symbol here: " + token.toString());
            }
            token = getToken();
            return (Symbol)token;
        }
        if (token instanceof SMTExpr.Error) throw new ParserException(token.pos(), lexMessage(token));
        if (msg != null) throw error(token, msg);
        throw new ParserException(token.pos(), null);
    }

    /** Parses a symbol or a reserved word, returning null with messages if an error occurs.  The error message
     * is given by the argument; it may contain a '#' character that will be replaced by the
     * kind() of the token actually observed. */
    public /*@Nullable*/Symbol parseSymbolOrReservedWord(String msg) throws IOException, ParserException {
        ILexToken token = getToken();
        if (token instanceof Symbol) return (Symbol)token;
        throw error(token, msg);
    }

    /** Parses a literal, returning null with error messages if an error occurs. */
    @Override
    public /*@Nullable*/ILiteral parseLiteral() throws IOException, ParserException {
        ILexToken token = getToken();
        if (token instanceof ILiteral) return (ILiteral)token;
        throw error(token, "Expected a literal here, instead of a #");
    }

    /** Parses a numeral, returning null with error messages if an error occurs; if
     * the next token is not a numeral, the token is not consumed, */
    @Override
    public /*@Nullable*/INumeral parseNumeral() throws IOException, ParserException {
        ILexToken token = getToken(INumeral.class);
        if (token instanceof INumeral) return (INumeral)token;
        throw error(token, "Expected a numeral here, instead of a #");
    }

    /** Parses a decimal, returning null with the given message if an error occurs; if
     * the next token is not a decimal, the token is not consumed, */
    @Override
    public IDecimal parseDecimal() throws IOException, ParserException {
        ILexToken token = getToken(IDecimal.class);
        if (token instanceof IDecimal) return (IDecimal)token;
        throw error(token, "Expected a decimal here, instead of a #");
    }

    /** Parses a binary literal, returning null with the given message if an error occurs; if
     * the next token is not a binary literal, the token is not consumed, */
    @Override
    public IBinaryLiteral parseBinary() throws IOException, ParserException {
        ILexToken token = getToken(IBinaryLiteral.class);
        if (token instanceof IBinaryLiteral) return (IBinaryLiteral)token;
        throw error(token, "Expected a binary literal here, instead of a #");
    }

    /** Parses a hex literal, returning null with the given message if an error occurs; if
     * the next token is not a hex literal, the token is not consumed, */
    @Override
    public IHexLiteral parseHex() throws IOException, ParserException {
        ILexToken token = getToken(IHexLiteral.class);
        if (token instanceof IHexLiteral) return (IHexLiteral)token;
        throw error(token, "Expected a hex literal here, instead of a #");
    }

    /** Parses a string literal, returning null with an error message if an error occurs; if
     * the next token is not a string literal, the token is not consumed, */
    @Override
    public /*@Nullable*/StringLiteral parseStringLiteral() throws IOException, ParserException {
        ILexToken token = getToken(IStringLiteral.class);
        if (token instanceof StringLiteral) return (StringLiteral)token;
        throw error(token, "Expected a string literal here, instead of a #");
    }

    /** Parses a keyword, returning null with an error message if an error occurs; if
     * the next token is not a keyword, the token is not consumed. */
    @Override
    public /*@Nullable*/Keyword parseKeyword() throws IOException, ParserException {
        ILexToken token = getToken(Keyword.class);
        if (token instanceof Keyword) return (Keyword)token;
        throw error(token, "Expected a keyword (beginning with a colon) here, instead of a #");
    }

    /** Parses a sort, returning null with error messages if a valid sort is not in the 
     * next parser tokens.
     */
    // Can be:
    //        id
    //        ( id sort+ )
    // so 
    //        symbol
    //        ( _ symbol numeral+ )
    //        ( symbol sort+ )
    //        ( ( _ symbol numeral+ ) sort+ )
    @Override
    public /*@Nullable*/Sort parseSort(List<ISort.IParameter> parameters) throws IOException, ParserException {
        if (!isLP()) {
            Symbol sym = parseSymbol();
            if (parameters != null) {
                for (ISort.IParameter p: parameters) {
                    // a use of the parameter: its own node, with the use's position (#231)
                    if (p.identifier().equals(sym)) {
                        return p instanceof Sort.Parameter d ? new Sort.ParameterUse(d, sym) : (Sort)p;
                    }
                }
            }
            return setPos(new Sort.Application(sym),sym.pos());
        } else {
            ILexToken lp = parseLP();

            if (!isLP()) {
                ISymbol head = parseSymbolOrReservedWord("Expected a symbol or _ here, not a #");
                if (false) { // no longer reachable
                } else if (head.value().equals(Utils.PARAM)) {
                    IIdentifier id = parseIdentifierRest(lp);
                    return setPos(new Sort.Application(id),id.pos());
                }
                // else some other symbol

                List<ISort> list = parseSortList(parameters);
                ILexToken rp = parseRP();
                return parenthesizedSort(head, list, pos(lp.pos(),rp.pos()));
            } else {
                IIdentifier id = parseIdentifier();
                List<ISort> list = parseSortList(parameters);
                ILexToken rp = parseRP();
                return parenthesizedSort(id, list, pos(lp.pos(),rp.pos()));
            }
        }
    }

    /** A sort ( id sort+ ); (S), with no sorts, is reported, then kept so that type checking reports it too */
    private Sort parenthesizedSort(IIdentifier id, List<ISort> list, IPos pos) {
        if (list.isEmpty()) recoverableError(pos, "A parenthesized sort must have at least one sort parameter");
        return setPos(new Sort.Application(id, list, true), pos);
    }

    /** Reports a vertical tab or form feed between tokens (except with --relax), which is then read as
     *  white space, and a keyword that is not a colon followed by a simple symbol (#185) */
    @Override
    protected ILexToken getNextToken() throws ParserException {
        ILexToken token = super.getNextToken();
        if (badWhitespace != null) {
            IPos p = badWhitespace;
            badWhitespace = null;
            if (!smtConfig.relax) {
                int c = p.source() == null ? 0 : p.source().charAt(p.charStart());
                commandHasLexicalError = true;
                recoverableError(p, "Invalid character: ASCII(decimal) = " + c + "; it is read as white space");
            }
        }
        if (token instanceof IKeyword && !smtConfig.isOKKeyword(((IKeyword)token).value())) {
            commandHasLexicalError = true;
            recoverableError(token.pos(), "A keyword must be a colon followed by a simple symbol (not starting with a digit, not a reserved word): "
                    + ((IKeyword)token).value());
        }
        return token;
    }

    /** Reports a syntax error after which parsing goes on as if the text were legal */
    private void recoverableError(IPos pos, String msg) {
        commandHasError = true;
        lastError = smtConfig.log.logError(smtConfig.responseFactory.error(pos, msg));
    }

    /** Parses sequence of sorts up to a right-parenthesis, returning null with error messages
     * if an error occurs.
     */
    public /*@Nullable*/List<ISort> parseSortList(List<ISort.IParameter> parameters) throws IOException, ParserException {
        List<ISort> list = new LinkedList<ISort>();
        while (!isRP()) {
            if (isEOD()) {
                throw new ParserException(pos(currentPos()-1,currentPos()), "Unexpected end of data while parsing a sort");
            }
            ISort s = parseSort(parameters);
            list.add(s);
        }
        return list;
    }

    /** Parse an attribute (keyword with optional value), returning null with error messages
     * if an error occurs.
     */
    @Override
    public /*@Nullable*/IAttributeValue parseAttributeValue() throws IOException, ParserException {
        if (!isLP()) {
            if (isRP()) {
                throw new ParserException(pos(currentPos()-1,currentPos()),
                        "Expected an attribute value here, instead of a )");
            }
            ILexToken t = getToken();
            if (t.isError()) {
                throw new ParserException(t.pos(), lexMessage(t));
            }
            if (t instanceof IKeyword) {
                throw new ParserException(t.pos(), "Expected an attribute value here, instead of a " + t.kind());
            }
            checkNotReserved(t);
            if (t instanceof IAttributeValue) {
                IAttributeValue v = (IAttributeValue)t;
                return v;
            } else {
                throw new ParserException(t.pos(), "Expected an attribute value here, instead of a " + t.kind());
            }
        } else {
            ISexpr value = parseSexpr();
            return value;
        }
    }

    /** A symbol attribute value may not be a reserved word (the grammar says symbol) */
    private void checkNotReserved(ILexToken t) throws IOException, ParserException {
        if (t instanceof Symbol && smtConfig.isReservedWord(((Symbol)t).value())) {
            throw error(t.pos(), "A reserved word may not be used as a symbol here: " + t.toString());
        }
    }

    /** Parse an attribute (keyword with optional value), returning null with error messages
     * if an error occurs.
     */
    @Override
    public /*@Nullable*/IExpr.IAttribute<?> parseAttribute() throws IOException, ParserException {
        return parseAttributeRest(parseKeyword());
    }

    /** Parses the (optional) value of an attribute whose keyword has already been parsed. */
    protected /*@Nullable*/IExpr.IAttribute<?> parseAttributeRest(IKeyword keyword) throws IOException, ParserException {
        if (isRP() || isEOD()) {
            return setPos(smtConfig.exprFactory.attribute(keyword),keyword.pos());
        }
        ILexToken n = peekToken();
        if (n instanceof IKeyword) {
            return setPos(smtConfig.exprFactory.attribute(keyword),keyword.pos());
        } else {
            if (!isLP()) {
                ILexToken t = getToken();
                if (t.isError()) throw new ParserException(t.pos(), lexMessage(t));
                checkNotReserved(t);
                if (t instanceof IAttributeValue) {
                    IAttributeValue v = (IAttributeValue)t;
                    return setPos(smtConfig.exprFactory.attribute(keyword,v),pos(keyword.pos(),v.pos()));
                } else {
                    throw new ParserException(t.pos(), "The value for the keyword " +
                            smtConfig.defaultPrinter.toString(keyword) + " is not a legal attribute value");
                }
            } else {
                ISexpr value = parseSexpr();
                return setPos(smtConfig.exprFactory.attribute(keyword,value),pos(keyword.pos(),value.pos()));
            }
        }
    }

    /** Parse a sequence of attributes (keyword with optional value) terminated by a right parenthesis, returning null with error messages
     * if an error occurs.
     */
    public /*@Nullable*/List<IExpr.IAttribute<?>> parseAttributeSequence() throws IOException, ParserException {
        List<IExpr.IAttribute<?>> list = new LinkedList<IExpr.IAttribute<?>>();
        while (!isRP()) {
            if (isEOD()) {
                throw new ParserException(pos(currentPos()-1, currentPos()),
                        "Unexpected end of data while parsing attributes");
            }
            IExpr.IAttribute<?> attr = parseAttribute();
            list.add(attr);
        }
        return list;
    }

    /** Parses the attributes of an annotated term {@code (! t attr+)} up to the right parenthesis.
     * Like {@link #parseAttributeSequence()}, except that a {@code :pattern} value is parsed as
     * what SMT-LIB defines it to be, a parenthesized (possibly empty, per SMT-LIB 2.7) list of terms, giving an
     * {@link IExpr.IPatternTerms} -- the same representation the expression factory builds.
     * A {@code :pattern} value that is not a list is left for the TypeChecker to report.
     */
    public /*@Nullable*/List<IExpr.IAttribute<?>> parseTermAttributeSequence() throws IOException, ParserException {
        List<IExpr.IAttribute<?>> list = new LinkedList<IExpr.IAttribute<?>>();
        while (!isRP()) {
            if (isEOD()) {
                throw new ParserException(pos(currentPos()-1, currentPos()),
                        "Unexpected end of data while parsing attributes");
            }
            ILexToken n = peekToken();
            if (!(n instanceof IKeyword) || !Utils.PATTERN.equals(((IKeyword)n).value())) {
                list.add(parseAttribute());
                continue;
            }
            IKeyword keyword = parseKeyword();
            if (!isLP()) {
                list.add(parseAttributeRest(keyword));
                continue;
            }
            ILexToken lp = parseLP();
            List<IExpr> terms = new LinkedList<IExpr>();
            while (!isRP()) {
                if (isEOD()) {
                    throw new ParserException(pos(currentPos()-1, currentPos()),
                            "Unexpected end of data while parsing a pattern");
                }
                terms.add(parseExpr());
            }
            ILexToken rp = parseRP();
            IExpr.IPatternTerms value = setPos(smtConfig.exprFactory.patternTerms(terms), pos(lp.pos(), rp.pos()));
            list.add(setPos(smtConfig.exprFactory.attribute(keyword, value), pos(keyword.pos(), rp.pos())));
        }
        return list;
    }

    /** Parses a logic definition (including beginning and ending parentheses, returning null
     * with error messages if it fails; only part of the checking of the contents is
     * performed in this call (the rest is done in loadLogic).
     */
    @Override
    public /*@Nullable*/ ILogic parseLogic() throws IOException, ParserException {
        ILexToken lp = parseLP();
        ISymbol sym = parseSymbol();
        if (!Utils.LOGIC.equals(sym.value())) {
            throw new ParserException(sym.pos(),
                    "Faulty logic definition: should have the keyword '" + Utils.LOGIC + "' as the first token");
        }
        ISymbol name = parseSymbol();
        List<IAttribute<?>> attributes = parseAttributeSequence();
        parseRP();
        if (!isEOD()) {
            throw new ParserException(pos(lp.pos().charStart(),currentPos()),
                    "Expected the end of file after the right parenthesis");
        }
        String clazzName = "org.smtlib.logic." + name;
        try {
            @SuppressWarnings("unchecked")
            Class<? extends ILogic> clazz = (Class<? extends ILogic>)Class.forName(clazzName);
            Constructor<? extends ILogic> con = clazz.getConstructor(SMT.Configuration.class,ISymbol.class,Collection.class);
            return con.newInstance(smtConfig,name,attributes);
        } catch (ClassNotFoundException e) {
            // No dedicated restriction class for this logic name - falls back to an
            // unrestricted logic (no noQuantifiers/sort/function-declaration checks).
            // Legitimate for logics that genuinely have no extra restriction class yet,
            // but also what a missing or mistyped class name (e.g. QF_UFNIA) silently
            // produces, so make the fallback visible rather than silent.
            if (smtConfig.verbose != 0) smtConfig.log.logDiag("#No restriction class " + clazzName
                    + " found for logic " + name + " - using an unrestricted logic");
        } catch (NoSuchMethodException e) {
            // error - the class must have the right constructor
            throw error(pos(lp.pos().charStart(),currentPos()),
                    "The constructor for the class " + clazzName + " does not have a constructor with the correct argument types");
        } catch (IllegalAccessException e) {
            // error - could not create a new instance
            throw error(pos(lp.pos().charStart(),currentPos()),
                    "An exception occurred when instantiating class " + clazzName + ": " + e);
        } catch (InstantiationException e) {
            // error - could not create a new instance
            throw error(pos(lp.pos().charStart(),currentPos()),
                    "An exception occurred when instantiating class " + clazzName + ": " + e);
        } catch (InvocationTargetException e) {
            // error - could not create a new instance
            throw error(pos(lp.pos().charStart(),currentPos()),
                    "An exception occurred when instantiating class " + clazzName + ": " + e);
        }
        return smtConfig.exprFactory.logic(name, attributes);
    }

    /** Parses a theory definition (including beginning and ending parentheses, returning null
     * with error messages if it fails; only part of the checking of the contents is
     * performed in this call (the rest is done in loadTheory).
     */
    @Override
    public /*@Nullable*/ ITheory parseTheory() throws IOException, ParserException {
        ILexToken lp = parseLP();
        ISymbol sym = parseSymbol();
        if (!Utils.THEORY.equals(sym.value())) {
            throw new ParserException(sym.pos(),
                    "Faulty theory definition: should have the keyword '" + Utils.THEORY + "' as the first token");
        }
        ISymbol name = parseSymbol();
        List<IAttribute<?>> attributes = parseAttributeSequence();
        parseRP();
        if (!isEOD()) {
            throw new ParserException(pos(lp.pos().charStart(),currentPos()),
                    "Expected the end of file after the right parenthesis");
        }
        return smtConfig.exprFactory.theory(name, attributes);
    }

    /** Parses a parenthesized list of terms, as returned by a get-assertions response. */
    public List<IExpr> parseAssertionList() throws IOException, ParserException {
        return parseList(this::parseExpr, "assertion", true);
    }

    /** Parses a parenthesized list of terms, as returned by a get-unsat-assumptions response. */
    public List<IExpr> parseTermList() throws IOException, ParserException {
        return parseList(this::parseExpr, "term", true);
    }

    /** Parses a parenthesized list of names, as returned by a get-unsat-core response. */
    public List<ISymbol> parseSymbolList() throws IOException, ParserException {
        return parseList(this::parseSymbol, "name", true);
    }

    /** Parses one {@code (term value)} pair, as found in a get-value response. */
    public IResponse.IPair<IExpr,IExpr> parseValuePair() throws IOException, ParserException {
        parseLP();
        IExpr term = parseExpr();
        IExpr value = parseExpr();
        parseRP();
        return smtConfig.responseFactory.pair(term, value);
    }

    /** Parses a parenthesized list of {@code (term value)} pairs, as returned by a
     *  get-value response. */
    public List<IResponse.IPair<IExpr,IExpr>> parseValueList() throws IOException, ParserException {
        return parseList(this::parseValuePair, "value pair", false);
    }

    /** Parses one {@code (symbol bool)} pair, as found in a get-assignment response. */
    public IResponse.IPair<ISymbol,Boolean> parseAssignmentPair() throws IOException, ParserException {
        parseLP();
        ISymbol sym = parseSymbol();
        ISymbol val = parseSymbol();
        parseRP();
        if (!val.value().equalsIgnoreCase("true") && !val.value().equalsIgnoreCase("false")) {
            throw new ParserException(val.pos(), "Expected 'true' or 'false' here, not '" + val.value() + "'");
        }
        return smtConfig.responseFactory.pair(sym, Boolean.valueOf(val.value()));
    }

    /** Parses a parenthesized list of {@code (symbol bool)} pairs, as returned by a
     *  get-assignment response. */
    public List<IResponse.IPair<ISymbol,Boolean>> parseAssignmentList() throws IOException, ParserException {
        return parseList(this::parseAssignmentPair, "assignment", true);
    }

    /** The start of the error message for solver text that is not SMT-LIB (see parseResponse) */
    public static final String UNEXPECTED_RESPONSE = "Unexpected response from the solver: ";

    //@Override // FIXME - put this in the interface
    public /*@Nullable*/ IResponse parseResponse(String response) throws IOException, ParserException {
        IResponse.IFactory f = smtConfig.responseFactory;
        response = response.trim();
        if ("".equals(response)) return f.empty();
        if ("success".equals(response)) return f.success();
        if ("sat".equals(response)) return f.sat();
        if ("unsat".equals(response)) return f.unsat();
        if ("unknown".equals(response)) return f.unknown();
        if ("unsupported".equals(response)) return f.unsupported();
        if ("true".equals(response)) return smtConfig.exprFactory.symbol("true");
        if ("false".equals(response)) return smtConfig.exprFactory.symbol("false");
        // FIXME - more - iterate over a list?

        // Text that is not SMT-LIB (e.g. bitwuzla's "[error] ...") does not parse (#118); the
        // whole reply is then the error (#148)
        ISexpr sexpr;
        try {
            sexpr = parseSexpr();
        } catch (ParserException e) {
            return f.error(UNEXPECTED_RESPONSE + response);
        }
        if (sexpr instanceof ISexpr.ISeq) {
            List<ISexpr> list = ((ISexpr.ISeq)sexpr).sexprs();
            if (list.size() >= 2) {
                if (list.get(0) instanceof ISymbol && ((ISymbol)list.get(0)).value().equals("error") && list.get(1) instanceof IStringLiteral) {
                    return f.error(((IStringLiteral)list.get(1)).value());
                }
            }
            List<IAttribute<?>> attributes = attributeList(list);
            if (attributes != null) return f.get_info_response(attributes);
        }
        return sexpr;
        //return f.error("Could not translate response: " + response);
    }

    /** The attributes of a get-info reply, each a keyword with an optional value, or null if the
     *  list is not of that form */
    private /*@Nullable*/ List<IAttribute<?>> attributeList(List<ISexpr> list) {
        if (list.isEmpty()) return null;
        List<IAttribute<?>> attributes = new LinkedList<IAttribute<?>>();
        for (int i = 0; i < list.size(); i++) {
            if (!(list.get(i) instanceof IKeyword)) return null;
            IKeyword key = (IKeyword)list.get(i);
            if (i + 1 < list.size() && !(list.get(i + 1) instanceof IKeyword)) {
                attributes.add(smtConfig.exprFactory.attribute(key, list.get(++i)));
            } else {
                attributes.add(smtConfig.exprFactory.attribute(key));
            }
        }
        return attributes;
    }

    /** Parses a left parenthesis, returning null and emitting an error message
     *  if there isn't one (and the next token is not consumed)
     */
    public /*@Nullable*/ILexToken parseLP() throws IOException, ParserException {
        ILexToken token = peekToken();
        if (token.isLP()) return getToken();
        throw error(token, "Expected a left parenthesis here, instead of a #");
    }

    /** Parses a right parenthesis, returning null and emitting an error message
     *  if there isn't one (and the next token is not consumed)
     */
    public /*@Nullable*/ILexToken parseRP() throws IOException, ParserException {
        ILexToken token = peekToken();
        if (token.isRP()) return getToken();
        throw error(token, "Expected a right parenthesis here, instead of a #");
    }

    /** The message of a lexical error token (the Lexer reports nothing itself, #148) */
    static String lexMessage(ILexToken token) {
        return token instanceof org.smtlib.IExpr.IError ? ((org.smtlib.IExpr.IError)token).value() : "Invalid token";
    }

    /** Creates a ParserException with the given position and message; callers should throw the result. */
    public ParserException error(/*@Nullable*//*@ReadOnly*/IPos pos, String msg) {
        return new ParserException(pos, msg);
    }

    /** Creates a ParserException from the given token and message; callers should throw the result.
     *  If the token is a lexical error token, the exception carries the lexer's message instead. */
    public ParserException error(ILexToken token, String msg) {
        if (token.isError()) return new ParserException(token.pos(), lexMessage(token));
        return new ParserException(token.pos(), msg.replace("#", token.kind()));
    }

    /** Parses a single match case: "(pattern term)" */
    public IExpr.IMatchCase parseMatchCase() throws IOException, ParserException {
        ILexToken lp = parseLP();
        IExpr.IPattern pattern = parsePattern();
        IExpr body = parseExpr();
        ILexToken rp = parseRP();
        return setPos(smtConfig.exprFactory.matchCase(pattern, body), pos(lp.pos(), rp.pos()));
    }

    /** Parses a match pattern: either a bare symbol (or wildcard _) or "(symbol symbol*)" where params may include _ */
    public IExpr.IPattern parsePattern() throws IOException, ParserException {
        if (!isLP()) {
            ISymbol sym = parsePatternSymbol();
            return setPos(smtConfig.exprFactory.pattern(sym, new LinkedList<>()), sym.pos());
        } else {
            ILexToken lp = parseLP();
            ISymbol constructor = parseSymbol();
            List<ISymbol> params = new LinkedList<>();
            while (!isRP() && !isEOD()) {
                params.add(parsePatternSymbol());
            }
            ILexToken rp = parseRP();
            IPos pos = pos(lp.pos(), rp.pos());
            if (!params.isEmpty()) return setPos(smtConfig.exprFactory.pattern(constructor, params), pos);
            // (c) is not a pattern; reported (a warning with --relax), then kept so that type checking
            // reports it too (or, with --relax, accepts it for a nullary constructor)
            if (smtConfig.relax) {
                smtConfig.log.logWarning(pos, "A parenthesized pattern should have at least one variable: ("
                        + smtConfig.defaultPrinter.toString(constructor) + ")");
            } else {
                recoverableError(pos, "A parenthesized pattern must have at least one variable");
            }
            return setPos(new SMTExpr.Pattern(constructor, params, true), pos);
        }
    }

    /** Parses a symbol in pattern position: accepts _ as a wildcard (reserved elsewhere) */
    private Symbol parsePatternSymbol() throws IOException, ParserException {
        ILexToken token = peekToken();
        if (token instanceof Symbol && Utils.WILDCARD.equals(((Symbol)token).value())) {
            return (Symbol) getToken();
        }
        return parseSymbol();
    }
}
