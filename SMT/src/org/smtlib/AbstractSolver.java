/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

import java.io.IOException;
import java.io.StringWriter;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.smtlib.ICommand.*;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.SMT.Configuration;
import org.smtlib.sexpr.Parser;


/** This class implements the operations of the org.smtlib.ISolver interface that map
 *  directly onto a single translated command sent to the solver process, with the
 *  expected response of a fully SMT-LIB compliant solver (a flat success/error/sat/unsat/
 *  unknown/unsupported, or a bare value/attribute-pair for get-option/get-info): the
 *  command is translated with {@link #translate(INode)} and sent via {@link
 *  #sendCommand(ICommand)}. get_assertions/get_value/get_assignment/get_unsat_core/
 *  get_unsat_assumptions additionally reparse a non-flat response as the structured list
 *  they're actually specified to return (a {@code (term value)} pair list, a name list,
 *  etc. — see {@link org.smtlib.sexpr.Parser#parseValueList()} and its siblings), since
 *  {@link #parseResponse(String)}'s generic parse only handles flat outcomes and just
 *  returns a raw s-expression for anything else. A subclass whose target solver deviates
 *  from strict SMT-LIB concrete syntax or response format overrides {@link
 *  #translate(INode)} and/or {@link #parseResponse(String)}; a subclass whose target
 *  solver deviates in some other way overrides the individual ISolver method itself,
 *  same as before.
 *  <p>
 *  {@link #start()} still throws UnsupportedOperationException, because AbstractSolver has
 *  no generic way to provide it: constructing the solver process and choosing its command
 *  line is inherently solver-specific, so every concrete adapter must override it.
 *  {@link #exit()}, by contrast, has a working default (send the exit command tolerating a
 *  silent process exit, then tear down the process) that's generic enough to cover every
 *  solver seen so far; a subclass only overrides it when exiting needs solver-specific
 *  handling beyond that.
 *  <p>
 *  Thus this class can still be used as a base class for a solver adapter class that
 *  wants the convenience of not having to implement every operation at once (remove
 *  AbstractSolver as a base class and retain ISolver as an interface to check that all
 *  ISolver methods are indeed present in the derived class), while getting working
 *  default behavior for the operations that don't need solver-specific handling.
 *
 * @author David Cok
 *
 */
public class AbstractSolver implements ISolver {

    protected static boolean isWindows = System.getProperty("os.name").contains("Wind");
    protected static boolean isMac = System.getProperty("os.name").contains("Mac");

    final protected IKeyword printSuccess;

    protected boolean printSuccessResponse = true;

    /** The object that interacts with external processes */
    protected SolverProcess solverProcess;

    /** Running correction applied when rewriting a line number a solver reports back in its
     *  own error text, so what the user sees matches their own script's real line numbers
     *  rather than whatever the solver itself counted in what was actually sent to it (see
     *  issues #96/#97). Every real command line and every real standalone comment line sent
     *  to a solver corresponds to exactly one line of the user's own script -- no adjustment
     *  needed there -- but two kinds of event break that correspondence and must adjust this
     *  field at the point they happen: a line an adapter inserts that has no counterpart in
     *  the user's script (e.g. a `:print-success` priming send at start()) increments it by
     *  the number of lines inserted; a real script line an adapter deliberately never sends
     *  (e.g. Solver_z3_4_3 skipping literal `(set-logic ALL)`, which that solver has no
     *  equivalent for) decrements it by the number of lines skipped. A subclass that embeds
     *  a solver-reported line number in its own response text should rewrite it as
     *  {@code reportedLine - linesOffset} before returning that text -- see
     *  Solver_z3_4_3/Solver_z3_recent/Solver_bitwuzla's parseResponse() overrides. Solvers
     *  that don't insert or skip any line relative to the user's script (most adapters) never
     *  need to touch this at all, and it stays 0. */
    protected int linesOffset = 0;

    /** SMT configuration — set by each concrete subclass constructor. */
    protected SMT.Configuration smtConfig;

    /** Map that keeps current values of options. */
    protected Map<String, IAttributeValue> options = new HashMap<String, IAttributeValue>();

    /** The result of the most recent check-sat or check-sat-assuming, or null if none has
     *  been issued since the last state-changing command. */
    protected /*@Nullable*/ IResponse checkSatStatus = null;

    /** Overridden by a subclass whose target solver's :error-behavior is immediate-exit
     *  (e.g. cvc5, yices2) rather than the SMT-LIB default of continued-execution -- such a
     *  solver's process may start exiting asynchronously right after it reports an error,
     *  and {@link SolverProcess#send(boolean, String...)}'s own process.isAlive() check can
     *  still read true for a brief window afterward (OS process-death bookkeeping lags the
     *  actual exit) -- see {@link #sendCommand(ICommand, boolean)}, which uses this to give
     *  a solver that just reported an error a moment to actually finish dying before the
     *  next command's liveness check runs, closing that race deterministically rather than
     *  guessing from the error's content whether the process will actually exit. */
    protected boolean selfReportsImmediateExit() { return false; }

    /** Called with each response parsed from the solver. After an error response from a
     *  {@link #selfReportsImmediateExit()} solver, gives its process a moment to finish exiting
     *  (see {@link #IMMEDIATE_EXIT_SETTLE_MILLIS}). If the error is one after which the solver
     *  no longer processes input ({@link #errorStopsSolver(IResponse)}) and the process is
     *  still alive, it is stopped, since a later command -- or exit() -- would otherwise wait
     *  forever for a reply. Only the OS process is stopped; the adapter is left as it is, so
     *  later commands fail fast as "Solver process has already exited" and exit() cleans up
     *  normally. */
    protected /*@Nullable*/ IResponse checkImmediateExit(/*@Nullable*/ IResponse result) {
        if (result != null && result.isError() && selfReportsImmediateExit()) {
            try {
                Thread.sleep(IMMEDIATE_EXIT_SETTLE_MILLIS);
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }
            if (solverProcess != null && errorStopsSolver(result)) solverProcess.stopIfRunning();
        }
        return result;
    }

    /** Whether, after the given error response, the solver stops processing input (whether or
     *  not its process actually exits). False by default; see Solver_cvc5. */
    protected boolean errorStopsSolver(IResponse error) {
        return false;
    }

    /** How long to pause after an error response from a {@link #selfReportsImmediateExit()}
     *  solver, before letting the next command reach {@link SolverProcess}'s liveness check
     *  -- long enough that a process which is genuinely exiting has, in practice, finished
     *  doing so by the time that check runs. Only paid on error responses, not on the
     *  (much more frequent) non-error path, so this does not affect ordinary solving
     *  performance. */
    private static final long IMMEDIATE_EXIT_SETTLE_MILLIS = 50;

    @Override
    public String solverName() {
        return getClass().toString().substring(6);
    }

    @Override
    public void forceExit() {
        if (solverProcess != null) solverProcess.exit();
    }

    /** Interrupts the command the solver is running (see {@link SolverProcess#interrupt()}) */
    public void interrupt() {
        if (solverProcess != null) solverProcess.interrupt();
    }


    public AbstractSolver() {
        try {
            SMT.Configuration c = new SMT.Configuration();
            printSuccess = new Parser(c,c.smtFactory.createSource(":print-success",null)).parseKeyword();
        } catch (Exception e) {
            throw new RuntimeException("Failed to create an AbstractSolver: " + e);
        }
    }

    public IResponse successOrEmpty(SMT.Configuration smtConfig) {
        return smtConfig.nosuccess ? smtConfig.responseFactory.empty() : smtConfig.responseFactory.success();
    }


    public IResponse checkPrintSuccess(SMT.Configuration smtConfig,IKeyword key, IAttributeValue value) {
        if (key.equals(printSuccess)) {
            // C_set_option.parse() already rejects this eagerly for any text-driven
            // script -- but this method is also reachable directly via
            // smtConfig.commandFactory.set_option(key,value), which bypasses that
            // parse-time check entirely (see issue #41), so a value that isn't literally
            // true/false can't just be assumed to be "false" the way the previous
            // !value.toString().equals("true") check silently did.
            if (!(Utils.TRUE.equals(value) || Utils.FALSE.equals(value))) {
                return smtConfig.responseFactory.error("The value of the " + key.value() + " option must be 'true' or 'false'", value.pos());
            }
            smtConfig.nosuccess = Utils.FALSE.equals(value);
            return successOrEmpty(smtConfig);
        }
        return null;
    }

    /** Translates an in-memory node into the text sent to the solver process. The base
     *  behavior assumes the solver is fully SMT-LIB compliant, so it is exactly what the
     *  default printer produces. Override in a subclass whose target solver deviates from
     *  strict SMT-LIB concrete syntax. */
    protected String translate(INode sexpr) throws IVisitor.VisitorException {
        StringWriter sw = new StringWriter();
        org.smtlib.sexpr.Printer.write(smtConfig, sw, sexpr);
        return sw.toString();
    }

    /** Parses the solver's raw response text. The base behavior assumes the response is
     *  exactly standard SMT-LIB concrete syntax: success/sat/unsat/unknown/unsupported/
     *  true/false, an {@code (error "...")} s-expression, a bare value (get-option), or a
     *  single {@code (:keyword value)} attribute pair (get-info). It does not build the
     *  richer structured IResponse subtypes that get_value/get_model/get_proof/
     *  get_assertions/get_unsat_core/get_unsat_assumptions/get_assignment need, nor does it
     *  correct for any real solver's non-compliant quirks (e.g. legacy bit-vector literal
     *  syntax) — override in a subclass whose target solver needs either. */
    protected IResponse parseResponse(String response) {
        try {
            return new Parser(smtConfig, new org.smtlib.impl.Pos.Source(response, null)).parseResponse(response);
        } catch (IParser.ParserException e) {
            return smtConfig.responseFactory.error("ParserException while parsing response: " + response + " " + e);
        }
    }

    /** Translates the given command and sends it to the solver process, returning the
     *  parsed response. This is the mechanism behind the default implementations below;
     *  a subclass may also call it directly to send a command built some other way. */
    protected IResponse sendCommand(ICommand cmd) {
        return sendCommand(cmd, false);
    }

    /** Sends the exit command, tolerating the solver producing literally no response
     *  (SolverProcess.NoResponseException) as a benign, expected outcome rather than an
     *  error -- many solvers legitimately print nothing before terminating in response to
     *  exit. The tolerated result is "", which Parser.parseResponse("") already turns into
     *  a plain empty response -- the same outcome a real empty response (e.g. under
     *  :print-success false) already produces, so no separate response-construction case
     *  is needed here. A subclass's exit() should call this instead of
     *  sendCommand(commandFactory.exit()) directly. */
    protected IResponse sendExitCommand() {
        // exit answers success (nothing is tolerated); sendCommand reports anything else (#149)
        IResponse r = sendCommand(smtConfig.commandFactory.exit(), true);
        if (pipelinedEver && solverProcess != null) {
            // The solver stops after exit; whatever else it wrote is out of step
            try {
                String out;
                while (!solverProcess.outputEnded() && (out = solverProcess.readOutput(PIPELINE_POLL_MILLIS)) != null) unread.append(out);
            } catch (IOException e) {
                // nothing more to read
            }
            reportLeftover();
        }
        return r;
    }

    private IResponse sendCommand(ICommand cmd, boolean tolerateSilentExit) {
        return sendCommand(cmd, tolerateSilentExit, false);
    }

    /** Replaces known sources of non-deterministic content in a raw solver response with a
     *  fixed placeholder, so that --testing runs produce byte-for-byte reproducible output
     *  across machines and repeated runs. Deliberately a short, explicit list rather than a
     *  broad catch-all, so it can't silently mask an actual difference in solver output:
     *  elapsed-time figures (e.g. cvc5's :all-statistics response embeds these as bare,
     *  unquoted "NNNms" tokens, which aren't valid SMT-LIB syntax at all and would
     *  otherwise cascade into a wall of "Invalid token" parse errors that also differ
     *  every run), and, in a reply to {@code get-info :all-statistics}, every number: statistics
     *  are run-dependent by nature, and solvers name them as they please. Their names are kept. */
    protected static String normalizeForTesting(String raw, IKeyword infoflag) {
        String s = raw;
        s = s.replaceAll("\\d+(\\.\\d+)?ms", "TIME");
        if (Utils.ALL_STATISTICS.value().equals(infoflag.value())) {
            s = s.replaceAll("(?<=[\\s(])-?\\d+(\\.\\d+)?(?=[\\s)])", "VALUE");
        }
        return s;
    }

    /** True once the solver's whole-run time limit (smtConfig.timeoutTotal) has ended it; every later command then
     *  gets responseFactory.timeout() (exit tolerates it), rather than an error about the process having exited. */
    protected boolean endedByTimeLimit = false;

    /** Whether the raw response text is this solver's report that its whole-run time limit (smtConfig.timeoutTotal)
     *  ended it; consulted only when that limit is set. Solvers report this in their own ways, so an adapter whose
     *  solver has such a limit overrides this; the default recognizes nothing. */
    protected boolean isTimeLimitResponse(String rawResponse) {
        return false;
    }

    /** Returns responseFactory.timeout(), recording that the solver has ended, if the raw response reports that the
     *  solver's whole-run time limit ended it; otherwise null. For adapters that send commands by their own means. */
    protected /*@Nullable*/ IResponse timeLimitResponse(/*@Nullable*/ String rawResponse) {
        if (smtConfig.timeoutTotal > 0 && rawResponse != null && isTimeLimitResponse(rawResponse)) {
            endedByTimeLimit = true;
            return smtConfig.responseFactory.timeout();
        }
        return null;
    }

    /** For when a send has found the solver process gone: the timeout response if the process left this solver's
     *  report that its whole-run time limit ended it unread (that limit runs on the wall clock, so it can end the
     *  solver between commands, and its report then answers no command); otherwise null */
    protected /*@Nullable*/ IResponse timeLimitResponseAfterExit() {
        if (!(smtConfig.timeoutTotal > 0) || solverProcess == null) return null;
        return timeLimitResponse(solverProcess.unreadOutput());
    }

    /** The solver's raw response to cmd (sent by sendCommand and waited for), corrected where the solver departs
     *  from SMT-LIB; an adapter overrides this to patch a specific non-conforming response */
    protected String correctResponse(ICommand cmd, String response) {
        return response;
    }

    private IResponse sendCommand(ICommand cmd, boolean tolerateSilentExit, boolean scrubNonDeterminism) {
        if (endedByTimeLimit) {
            return tolerateSilentExit ? smtConfig.responseFactory.empty() : smtConfig.responseFactory.timeout();
        }
        String translatedCmd = null;
        try {
            if (!capturing) readPipelined(true);
            translatedCmd = translate(cmd);
            if (capturing) return sendWithoutWaiting(translatedCmd, shapeOf(cmd));
            String response = solverProcess.sendAndListen(translatedCmd, "\n");
            // A null response (observed rarely, likely a SolverProcess read-timing race)
            // would otherwise reach parseResponse() and surface as an uncaught
            // NullPointerException from deep in the parser, crashing the whole run
            // instead of just this one command.
            if (response == null) {
                return smtConfig.responseFactory.error("No response received from the solver for: " + translatedCmd);
            }
            IResponse timedOut = timeLimitResponse(response);
            if (timedOut != null) return timedOut;
            response = correctResponse(cmd, response);
            if (scrubNonDeterminism && smtConfig.testing && cmd instanceof Iget_info g) response = normalizeForTesting(response, g.infoflag());
            IResponse result = parseResponse(response);
            // parseResponse() (or a subclass override) can itself return null for some
            // malformed/edge-case response text without throwing -- same defensive
            // reasoning as the null-response guard above: surface it as an error rather
            // than let a null IResponse propagate up and crash the caller.
            if (result == null) {
                return smtConfig.responseFactory.error("Could not parse response from the solver for: " + translatedCmd + " -- raw response: " + response);
            }
            Shape shape = shapeOf(cmd);
            return checkShape(shape, translatedCmd, response,
                    checkImmediateExit(checkNonResponse(result, shape == Shape.ANY, translatedCmd, response)));
        } catch (SolverProcess.NoResponseException e) {
            if (tolerateSilentExit) return smtConfig.responseFactory.empty();
            IResponse timedOut = timeLimitResponseAfterExit();
            if (timedOut != null) return timedOut;
            return smtConfig.responseFactory.error("Error writing to solver: " + translatedCmd + " " + e);
        } catch (IOException e) {
            return smtConfig.responseFactory.error("Error writing to solver: " + translatedCmd + " " + e);
        } catch (IVisitor.VisitorException e) {
            return smtConfig.responseFactory.error("Error writing to solver: " + translatedCmd + " " + e);
        }
    }

    // Pipelining: a pipelined command is sent without waiting for its response, which is read later
    // and matched to it by position, since the solver writes one response per command in order.
    // Each response must have the bare shape its command can produce (#149); one that does not is an
    // error, as is output left over once every command is answered. A solver that writes nothing for
    // a successful command (see solverPrintsSuccess) is matched by shape instead, with an echo sent
    // as a barrier before waiting.

    /** The response returned for a command sent by {@link #sendPipelined(ICommand)} whose actual
     *  response has not yet been read; {@link #isReady()} tells when it has (see
     *  {@link #readPipelined(boolean)}), and {@link #response()} then gives it. */
    public static final class Pending implements IResponse {
        /** The text sent to the solver */
        final String sent;
        /** The kind of response the command has */
        final Shape shape;
        /** For a barrier (see readPipelined), the text it echoes; else null */
        final /*@Nullable*/ String marker;
        private /*@Nullable*/ IResponse response = null;

        Pending(String sent, Shape shape, /*@Nullable*/ String marker) {
            this.sent = sent;
            this.shape = shape;
            this.marker = marker;
        }

        public boolean isReady() { return response != null; }

        /** The response read for the command, or null if not yet read */
        public /*@Nullable*/ IResponse response() { return response; }

        @Override public boolean isOK() { return false; }
        @Override public boolean isError() { return false; }
        @Override public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
            throw new IVisitor.VisitorException("A pipelined response has not been read yet", null);
        }
        @Override public String toString() { return response == null ? "<pending>" : response.toString(); }
    }

    /** True while {@link #sendPipelined(ICommand)} executes a command, so that
     *  {@link #sendCommand(ICommand)} sends it without waiting */
    private boolean capturing = false;

    /** Commands sent without waiting whose responses have not yet been read, oldest first */
    private final java.util.ArrayDeque<Pending> pending = new java.util.ArrayDeque<>();

    /** Text read from the solver's standard output not yet matched to a command */
    private final StringBuilder unread = new StringBuilder();

    /** Text read from the solver's standard error not yet reported */
    private final StringBuilder unreadErrorOutput = new StringBuilder();

    /** The most recent response read for a pipelined command */
    private /*@Nullable*/ IResponse lastPipelined = null;

    /** Whether {@link #sendPipelined(ICommand)} may send the command without waiting for its
     *  response. True for the commands whose execution here sends the command (once) and has
     *  nothing to do with its response beyond returning it -- except check-sat, whose response
     *  becomes {@link #checkSatStatus} when it is read. A subclass returns false for a command
     *  whose solver response needs correcting before it is compliant, or that it executes
     *  otherwise, and for all commands if it does not send them through sendCommand. */
    public boolean pipelines(ICommand cmd) {
        return cmd instanceof Ideclare_fun || cmd instanceof Ideclare_const
                || cmd instanceof Ideclare_sort || cmd instanceof Ideclare_sort_parameter
                || cmd instanceof Idefine_fun || cmd instanceof Idefine_fun_rec
                || cmd instanceof Idefine_funs_rec || cmd instanceof Idefine_sort
                || cmd instanceof Ideclare_datatype || cmd instanceof Ideclare_datatypes
                || cmd instanceof Iassert || cmd instanceof Ipush || cmd instanceof Ipop
                || cmd instanceof Icheck_sat || cmd instanceof Icheck_sat_assuming
                || cmd instanceof Iset_logic || cmd instanceof Iset_info
                || cmd instanceof Ireset || cmd instanceof Ireset_assertions;
    }

    /** Executes a command for which {@link #pipelines(ICommand)} is true, sending it to the solver
     *  without waiting for the response. Returns a {@link Pending} response if the command was
     *  sent, or the actual response if it was not (e.g. an error found before sending). Any other
     *  request to this solver first waits for the pending responses, but a caller must call
     *  {@link #readPipelined(boolean)} with true itself before executing a command that is checked
     *  against an earlier response (such as get-value against check-sat). */
    public IResponse sendPipelined(ICommand cmd) {
        capturing = true;
        try {
            return cmd.execute(this);
        } finally {
            capturing = false;
        }
    }

    /** Executes the commands in order, as a script does: returns the first error, or else the last
     *  command's response. Commands that {@link #pipelines(ICommand)} allows are sent without waiting
     *  for their responses; check-sat, check-sat-assuming and every other command first wait for the
     *  pending responses, so that none is executed after an error. Used by IScript.execute when
     *  {@link SMT.Configuration#pipeline} is set. */
    public IResponse executePipelined(List<ICommand> commands) {
        List<Pending> sent = new java.util.ArrayList<>();
        IResponse response = smtConfig.responseFactory.success();
        for (ICommand c: commands) {
            if (pipelines(c) && !(c instanceof Icheck_sat) && !(c instanceof Icheck_sat_assuming)) {
                response = sendPipelined(c);
                if (response instanceof Pending p) {
                    sent.add(p);
                    continue;
                }
            } else {
                IResponse err = firstError(sent);
                if (err != null) return err;
                response = c.execute(this);
            }
            if (response.isError()) {
                IResponse err = firstError(sent);
                return err != null ? err : response;
            }
        }
        IResponse err = firstError(sent);
        if (err != null) return err;
        return response instanceof Pending p ? p.response() : response;
    }

    /** Waits for the responses to the sent commands and returns the first error among them, or null */
    private /*@Nullable*/ IResponse firstError(List<Pending> sent) {
        if (sent.isEmpty()) return null;
        readPipelined(true);
        IResponse err = null;
        for (Pending p: sent) {
            if (p.response().isError()) {
                err = p.response();
                break;
            }
        }
        sent.clear();
        return err;
    }

    /** Whether some pipelined command's response has not yet been read */
    public boolean hasPending() {
        return !pending.isEmpty();
    }

    /** Whether a command has been pipelined since finishPipelined last ran */
    private boolean pipelinedSinceFinish = false;

    /** Whether a command has been pipelined at all */
    private boolean pipelinedEver = false;

    private IResponse sendWithoutWaiting(String translatedCmd, Shape shape) {
        pipelinedSinceFinish = true;
        pipelinedEver = true;
        Pending p = new Pending(translatedCmd, shape, null);
        try {
            solverProcess.sendNoListen(translatedCmd, "\n");
            pending.add(p);
        } catch (IOException e) {
            // The solver has stopped: report it as for any command sent after that
            IResponse timedOut = timeLimitResponseAfterExit();
            p.response = timedOut != null ? timedOut : alreadyExited(translatedCmd);
        }
        return p;
    }

    private IResponse alreadyExited(String translatedCmd) {
        return smtConfig.responseFactory.error("Error writing to solver: " + translatedCmd + " "
                + new SolverProcess.NoResponseException("Solver process has already exited"));
    }

    /** How often (ms) reading that waits for a response also checks standard error */
    private static final long PIPELINE_POLL_MILLIS = 100;

    /** Reads what the solver has written for pipelined commands, matching each response to its
     *  command in order; with wait, until every pending command has its response (or the solver
     *  has stopped), else only what has already arrived. Standard error is checked each time
     *  output is read. Which command its text belongs to is not known while the solver runs, so
     *  it is kept until either the solver stops, when it becomes the response of the first
     *  command without one (as listen() would return it), or every pending response has been
     *  read, when it is logged as diagnostic output. */
    public void readPipelined(boolean wait) {
        // Without pending commands, leave everything to listen(), as without pipelining
        if (pending.isEmpty()) {
            if (wait) reportLeftover();
            return;
        }
        if (wait && !solverPrintsSuccess()) sendBarrier();
        while (!pending.isEmpty()) {
            checkErrorOutput(0);
            if (matchUnread()) continue;
            if (solverProcess == null || solverProcess.outputEnded()) {
                resolveAfterEnd();
                break;
            }
            String out;
            try {
                out = solverProcess.readOutput(wait ? PIPELINE_POLL_MILLIS : 0);
            } catch (IOException e) {
                resolveAfterEnd();
                break;
            }
            if (out != null) unread.append(out);
            else if (!wait) break;
        }
        if (pending.isEmpty()) {
            checkErrorOutput(0);
            // Text read beyond the responses is left, without waiting, for the next command
            // (a solver one response ahead then shows as a response out of step); waiting, no
            // command is left to take it
            if (wait) reportLeftover();
            String err = takeErrorOutput(false);
            if (!err.isEmpty()) smtConfig.log.logDiag(err.trim());
        }
    }

    /** Reports output read beyond the responses to the pipelined commands */
    private void reportLeftover() {
        String extra = unread.toString().trim();
        unread.setLength(0);
        if (!extra.isEmpty()) reportOutOfStep(extra);
    }

    /** At the end of a pipelined run: waits briefly for output still arriving after the last
     *  response, and reports any as out of step */
    public void finishPipelined() {
        readPipelined(true);
        if (solverProcess == null || !pipelinedSinceFinish) return;
        pipelinedSinceFinish = false;
        try {
            String out;
            while ((out = solverProcess.readOutput(PIPELINE_POLL_MILLIS)) != null) unread.append(out);
        } catch (IOException e) {
            // nothing more to read
        }
        reportLeftover();
    }

    private void checkErrorOutput(long waitMillis) {
        if (solverProcess == null) return;
        try {
            unreadErrorOutput.append(solverProcess.readErrorOutput(waitMillis));
        } catch (IOException e) {
            // nothing more to read
        }
    }

    /** The standard-error text read and not yet reported, as written but for comment lines (z3
     *  writes some), which listen() ignores too. The text arrives in pieces, so only whole lines are
     *  judged: unless all is true (the solver has stopped), an unfinished last line is left for later. */
    private String takeErrorOutput(boolean all) {
        int end = all ? unreadErrorOutput.length() : unreadErrorOutput.lastIndexOf("\n") + 1;
        String[] lines = unreadErrorOutput.substring(0, end).split("\n", -1);
        unreadErrorOutput.delete(0, end);
        StringBuilder text = new StringBuilder();
        for (int i = 0; i < lines.length; i++) {
            if (lines[i].startsWith(";")) continue;
            text.append(lines[i]);
            if (i < lines.length - 1) text.append('\n');
        }
        return text.toString().trim().isEmpty() ? "" : text.toString();
    }

    /** Matches the next complete response in the unread text, if any, to the oldest pending
     *  command; returns whether it did */
    private boolean matchUnread() {
        int start = 0;
        int end;
        while (true) {
            while (start < unread.length() && Character.isWhitespace(unread.charAt(start))) start++;
            if (start < unread.length() && unread.charAt(start) == ';') {
                // a comment line (z3 writes some): not a response
                int eol = unread.indexOf("\n", start);
                if (eol < 0) return false;
                start = eol + 1;
                continue;
            }
            end = responseEnd(unread, start);
            if (end < 0) return false;
            break;
        }
        String text = unread.substring(start, end);
        unread.delete(0, end);
        if (!solverPrintsSuccess()) return matchSilent(text);
        Pending p = pending.poll();
        resolve(p, toResponse(p, text));
        return true;
    }

    /** Whether the solver writes 'success' for a successful command, so that every pipelined command
     *  gets one response. True for every adapter now (the solver process is kept at
     *  :print-success true); an adapter whose solver does not returns false, and its pipelined
     *  responses are then matched by shape (see matchSilent). */
    protected boolean solverPrintsSuccess() {
        return true;
    }

    /** Set when pipelined responses were found out of step with their commands: a response of the
     *  wrong shape, or output left over once every command was answered */
    private boolean outOfStep = false;

    /** Whether pipelined responses have been found out of step with their commands (#149) */
    public boolean outOfStep() {
        return outOfStep;
    }

    private int barriers = 0;

    /** For a solver that writes nothing for a successful command: sends an echo, whose response
     *  marks the end of the responses to the commands pending before it */
    private void sendBarrier() {
        if (pending.peekLast() != null && pending.peekLast().marker != null) return;
        String marker = "jsmtlib-sync-" + (++barriers);
        String sent = "(echo \"" + marker + "\")";
        try {
            solverProcess.sendNoListen(sent, "\n");
            pending.add(new Pending(sent, Shape.ANY, marker));
        } catch (IOException e) {
            // The solver has stopped; the pending commands are resolved as its output ends
        }
    }

    /** Matches one response when the solver writes nothing for a successful command: a barrier's
     *  echo answers, with success, every command before it still without a response; sat, unsat or
     *  unknown answers the next check-sat (the commands before it having succeeded); an error or
     *  unsupported answers the oldest command without a response, though which command it belongs
     *  to cannot be known for certain; anything else is out of step */
    private boolean matchSilent(String text) {
        String t = text.trim();
        if (isBarrierFor(t)) {
            Pending p;
            while ((p = pending.poll()) != null && p.marker == null) {
                resolve(p, p.shape == Shape.CHECK_SAT
                        ? smtConfig.responseFactory.error("No response from the solver to: " + p.sent.trim())
                        : successOrEmpty(smtConfig));
            }
            return true;
        }
        IResponse parsed = smtConfig.log.unheld(() -> parseResponse(text));
        if (parsed instanceof ISymbol sym && CHECK_SAT_RESPONSES.contains(sym.value())) {
            Pending p;
            while ((p = pending.peek()) != null && p.shape != Shape.CHECK_SAT && p.marker == null) {
                resolve(pending.poll(), successOrEmpty(smtConfig));
            }
            if (p == null || p.marker != null) reportOutOfStep(text);
            else resolve(pending.poll(), toResponse(p, text));
            return true;
        }
        Pending p = pending.peek();
        if (p.marker != null) {
            reportOutOfStep(text);
            return true;
        }
        pending.poll();
        boolean errorLike = parsed != null && (parsed.isError()
                || (parsed instanceof ISymbol sym && "unsupported".equals(sym.value())));
        resolve(p, errorLike ? toResponse(p, text) : outOfStepResponse(p.sent, text));
        return true;
    }

    private static boolean isBarrierFor(String text, String marker) {
        return text.equals("\"" + marker + "\"") || text.equals(marker);
    }

    private boolean isBarrierFor(String text) {
        for (Pending p: pending) {
            if (p.marker != null && isBarrierFor(text, p.marker)) return true;
        }
        return false;
    }

    /** Output that no pending command can take */
    private void reportOutOfStep(String text) {
        outOfStep = true;
        smtConfig.log.logError(smtConfig.responseFactory.error("Unexpected output from the solver: " + text.trim()));
    }

    /** The responses that answer check-sat and check-sat-assuming (besides error and unsupported) */
    private static final java.util.Set<String> CHECK_SAT_RESPONSES = java.util.Set.of(
            "sat", "unsat", "unknown", "timeout", "memout", "incomplete");

    /** The kinds of response a command has besides an error or unsupported (#149) */
    protected enum Shape {
        /** success */
        SUCCESS,
        /** sat, unsat, unknown (or timeout, memout, incomplete): check-sat and check-sat-assuming */
        CHECK_SAT,
        /** a value other than a bare symbol: the get- commands but get-option */
        VALUE,
        /** any non-empty value, including a bare symbol: get-option's value, and echo's text, which
         *  some solvers write unquoted (their adapters answer a user's echo themselves) */
        ANY
    }

    /** The kind of response cmd has */
    protected static Shape shapeOf(ICommand cmd) {
        if (cmd instanceof Icheck_sat || cmd instanceof Icheck_sat_assuming) return Shape.CHECK_SAT;
        if (cmd instanceof Iget_option || cmd instanceof Iecho) return Shape.ANY;
        if (cmd instanceof Iget_assertions || cmd instanceof Iget_assignment || cmd instanceof Iget_info
                || cmd instanceof Iget_model || cmd instanceof Iget_proof || cmd instanceof Iget_unsat_assumptions
                || cmd instanceof Iget_unsat_core || cmd instanceof Iget_value) return Shape.VALUE;
        return Shape.SUCCESS;
    }

    /** Whether the response has a bare shape the command can produce: an error or unsupported for any
     *  command, else as the shape says */
    private static boolean fitsShape(Shape shape, IResponse r) {
        if (r.isError()) return true;
        if (!(r instanceof ISymbol sym)) return shape == Shape.VALUE || shape == Shape.ANY;
        String v = sym.value();
        if (v.equals("unsupported")) return true;
        return switch (shape) {
            case SUCCESS -> v.equals("success");
            case CHECK_SAT -> CHECK_SAT_RESPONSES.contains(v);
            case VALUE -> false;
            case ANY -> !v.isEmpty();
        };
    }

    /** r, if it has the given shape; else the error for a response out of step with the command sent,
     *  whose raw response was text */
    protected IResponse checkShape(Shape shape, String sent, String text, IResponse r) {
        return fitsShape(shape, r) ? r : outOfStepResponse(sent, text);
    }

    private IResponse outOfStepResponse(String sent, String text) {
        outOfStep = true;
        String t = text.trim();
        return smtConfig.responseFactory.error("Out of step: the response to " + sent.trim() + " was "
                + (t.isEmpty() ? "empty" : t));
    }

    /** The index just past the response that starts at start (an atom, a string literal, a quoted
     *  symbol, or one balanced S-expression), or -1 if that response is not yet complete */
    public static int responseEnd(CharSequence s, int start) {
        int n = s.length();
        if (start >= n) return -1;
        int depth = 0;
        int i = start;
        while (i < n) {
            char c = s.charAt(i);
            if (c == '"') {
                // a string literal; "" within it is an escaped quote
                i++;
                while (true) {
                    if (i >= n) return -1;
                    if (s.charAt(i) == '"') {
                        if (i + 1 >= n) return -1; // cannot yet tell whether this is ""
                        if (s.charAt(i + 1) != '"') break;
                        i++;
                    }
                    i++;
                }
                i++;
            } else if (c == '|') {
                int close = i + 1;
                while (close < n && s.charAt(close) != '|') close++;
                if (close >= n) return -1;
                i = close + 1;
            } else if (c == '(') {
                depth++;
                i++;
            } else if (c == ')') {
                depth--;
                i++;
            } else if (depth > 0) {
                i++;
                continue;
            } else {
                // an atom: ends at whitespace or a delimiter
                while (i < n && !Character.isWhitespace(s.charAt(i)) && "()\";|".indexOf(s.charAt(i)) < 0) i++;
                if (i >= n) return -1; // it may continue
                return i;
            }
            if (depth <= 0) return i;
        }
        return -1;
    }

    private IResponse toResponse(Pending p, String text) {
        IResponse timedOut = timeLimitResponse(text);
        if (timedOut != null) return timedOut;
        // Logged at once, as when not pipelining: an adapter may parse with the output redirected
        IResponse result = smtConfig.log.unheld(() -> parseResponse(text));
        if (result == null) {
            return smtConfig.responseFactory.error("Could not parse response from the solver for: " + p.sent + " -- raw response: " + text);
        }
        return checkShape(p.shape, p.sent, text,
                checkImmediateExit(checkNonResponse(result, p.shape == Shape.ANY, p.sent, text)));
    }

    /** The bare symbols that are responses in themselves, including the empty response; any
     *  other answers only get-option and echo */
    private static final java.util.Set<String> SYMBOL_RESPONSES = java.util.Set.of(
            "", "success", "unsupported", "sat", "unsat", "unknown", "timeout", "memout", "incomplete");

    /** How long a solver that wrote something other than a response is given to finish exiting,
     *  before it is judged to be still running (only paid on that abnormal path) */
    private static final long NON_RESPONSE_SETTLE_MILLIS = 500;

    /** Rejects a bare symbol that cannot answer the command sent (#134), such as the first word of
     *  a crash message: an error saying the solver stopped, if it did, or else one giving the text.
     *  anySymbol says whether the command may be answered by any symbol (see Shape.ANY). */
    private IResponse checkNonResponse(IResponse result, boolean anySymbol, String sent, String raw) {
        if (anySymbol || !(result instanceof ISymbol) || SYMBOL_RESPONSES.contains(((ISymbol)result).value())) {
            return result;
        }
        if (solverProcess != null && hasStopped()) {
            if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Solver output: " + raw.trim());
            return smtConfig.responseFactory.error("The solver stopped without a response to: " + sent.trim());
        }
        return smtConfig.responseFactory.error(Parser.UNEXPECTED_RESPONSE + raw.trim());
    }

    /** Whether the solver process has exited, waiting up to NON_RESPONSE_SETTLE_MILLIS for it */
    private boolean hasStopped() {
        long deadline = System.currentTimeMillis() + NON_RESPONSE_SETTLE_MILLIS;
        while (solverProcess.isRunning(true)) {
            if (System.currentTimeMillis() >= deadline) return false;
            try {
                Thread.sleep(10);
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
                return false;
            }
        }
        return true;
    }

    private void resolve(Pending p, IResponse r) {
        p.response = r;
        if (checkSatStatus == p) checkSatStatus = r;
        lastPipelined = r;
    }

    /** Gives every pending command a response once the solver's output has ended, as sending the
     *  commands one at a time would: the first gets what the solver wrote on standard error, if
     *  anything, or else, unless the solver stopped after an error response, the error for a solver
     *  that wrote no response; the rest get the error for a solver that has exited. */
    private void resolveAfterEnd() {
        checkErrorOutput(solverProcess == null ? 0 : solverProcess.errorSettleMillis);
        String err = takeErrorOutput(true);
        String extra = unread.toString().trim();
        unread.setLength(0);
        if (!extra.isEmpty()) err = err.isEmpty() ? extra : extra + "\n" + err;
        IResponse timedOut = err.isEmpty() ? null : timeLimitResponse(err);
        boolean first = !err.isEmpty() || lastPipelined == null || !lastPipelined.isError();
        Pending p;
        while ((p = pending.poll()) != null) {
            if (p.marker != null) continue;
            IResponse r;
            if (endedByTimeLimit || timedOut != null) {
                r = smtConfig.responseFactory.timeout();
            } else if (first && !err.isEmpty()) {
                r = toResponse(p, err);
            } else if (first) {
                r = smtConfig.responseFactory.error("Error writing to solver: " + p.sent + " "
                        + new SolverProcess.NoResponseException("Solver process closed its output stream without a response"));
            } else {
                r = alreadyExited(p.sent);
            }
            first = false;
            resolve(p, r);
        }
    }

    /** @see org.smtlib.ISolver#start() */
    @Override
    public IResponse start() {
        throw new UnsupportedOperationException("AbstractSolver.start");
    }

    /** @see org.smtlib.ISolver#exit() */
    @Override
    public IResponse exit() {
        IResponse response = sendExitCommand();
        solverProcess.exit();
        if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Ended " + smtConfig.solvername);
        solverProcess = null;
        return response;
    }


    @Override
    public IResponse echo(IStringLiteral arg) {
        return sendCommand(smtConfig.commandFactory.echo(arg));
    }

    /** Forwards a standalone comment (its own C_comment pseudo-command -- see issue #42) to
     *  the real solver process, uniformly for every solver adapter: a comment is legal
     *  SMT-LIB input (any conforming solver must silently ignore it), and forwarding it keeps
     *  the physical line count of what's actually sent matching the user's own script one
     *  real line for one sent line -- which line-number rewriting (see e.g.
     *  Solver_z3_4_3/Solver_z3_recent's linesOffset) depends on. sendNoListen is used, not
     *  sendAndListen: a comment has no response to wait for. A trailing, same-line comment
     *  never reaches here at all -- it's captured as Command.trailingText instead (see
     *  Parser.parseCommand()) and is never sent to a solver. */
    @Override public void comment(String comment) {
        try {
            solverProcess.sendNoListen(comment);
        } catch (IOException e) {
            if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Failed to send comment to " + smtConfig.solvername + ": " + e);
        }
    }

    /** @see org.smtlib.ISolver#set_logic(String,IPos) */
    @Override
    public IResponse set_logic(String logicName, /*@Nullable*/ IPos pos) {
        checkSatStatus = null;
        checkMade = false;
        return sendCommand(smtConfig.commandFactory.set_logic(smtConfig.exprFactory.symbol(logicName)));
    }

    /** @see org.smtlib.ISolver#reset() */
    @Override
    public IResponse reset() {
        checkSatStatus = null;
        checkMade = false;
        return sendCommand(smtConfig.commandFactory.reset());
    }

    /** @see org.smtlib.ISolver#reset_assertions() */
    @Override
    public IResponse reset_assertions() {
        checkSatStatus = null;
        return sendCommand(smtConfig.commandFactory.reset_assertions());
    }

    /** @see org.smtlib.ISolver#push(int) */
    @Override
    public IResponse push(int number) {
        checkSatStatus = null;
        return sendCommand(smtConfig.commandFactory.push(smtConfig.exprFactory.numeral(number)));
    }

    /** @see org.smtlib.ISolver#pop(int) */
    @Override
    public IResponse pop(int number) {
        checkSatStatus = null;
        return sendCommand(smtConfig.commandFactory.pop(smtConfig.exprFactory.numeral(number)));
    }

    /** @see org.smtlib.ISolver#assertExpr(IExpr) */
    @Override
    public IResponse assertExpr(IExpr sexpr) {
        checkSatStatus = null;
        return sendCommand(smtConfig.commandFactory.assertCommand(sexpr));
    }

    /** @see org.smtlib.ISolver#check_sat()*/
    @Override
    public IResponse check_sat() {
        checkMade = true;
        checkSatStatus = sendCommand(smtConfig.commandFactory.check_sat());
        return checkSatStatus;
    }

    /** @see org.smtlib.ISolver#check_sat_assuming(IExpr...)*/
    @Override
    public IResponse check_sat_assuming(IExpr ... exprs) {
        checkMade = true;
        checkSatStatus = sendCommand(smtConfig.commandFactory.check_sat_assuming(java.util.Arrays.asList(exprs)));
        return checkSatStatus;
    }

    /** @see org.smtlib.ISolver#define_const(ICommand.Idefine_const)  */
    @Override
    public IResponse define_const(Idefine_const cmd) {
        return define_fun(cmd);
    }

    /** @see org.smtlib.ISolver#define_fun(ICommand.Idefine_fun)  */
    @Override
    public IResponse define_fun(Idefine_fun cmd) {
        checkSatStatus = null;
        return sendCommand(cmd);
    }

    /** @see org.smtlib.ISolver#define_fun_rec(ICommand.Idefine_fun_rec)  */
    @Override
    public IResponse define_fun_rec(Idefine_fun_rec cmd) {
        checkSatStatus = null;
        return sendCommand(cmd);
    }

    /** @see org.smtlib.ISolver#define_funs_rec(ICommand.Idefine_funs_rec)  */
    @Override
    public IResponse define_funs_rec(Idefine_funs_rec cmd) {
        checkSatStatus = null;
        return sendCommand(cmd);
    }

    /** @see org.smtlib.ISolver#declare_const(ICommand.Ideclare_const)  */
    @Override
    public IResponse declare_const(Ideclare_const cmd) {
        // declare-const is syntactic sugar for declare-fun with an empty argument list
        return declare_fun(smtConfig.commandFactory.declare_fun(
                cmd.symbol(), new java.util.ArrayList<>(), cmd.resultSort()));
    }

    /** @see org.smtlib.ISolver#declare_fun(ICommand.Ideclare_fun)  */
    @Override
    public IResponse declare_fun(Ideclare_fun cmd) {
        checkSatStatus = null;
        return sendCommand(cmd);
    }

    /** @see org.smtlib.ISolver#define_sort(ICommand.Idefine_sort)  */
    @Override
    public IResponse define_sort(Idefine_sort cmd){
        checkSatStatus = null;
        return sendCommand(cmd);
    }

    /** @see org.smtlib.ISolver#declare_sort(ICommand.Ideclare_sort)  */
    @Override
    public IResponse declare_sort(Ideclare_sort cmd) {
        checkSatStatus = null;
        return sendCommand(cmd);
    }

    /** @see org.smtlib.ISolver#declare_sort_parameter(ICommand.Ideclare_sort_parameter)  */
    @Override
    public IResponse declare_sort_parameter(Ideclare_sort_parameter cmd) {
        checkSatStatus = null;
        return sendCommand(cmd);
    }

    /** @see org.smtlib.ISolver#set_option(IExpr.IKeyword,IExpr.IAttributeValue)
     *  The channel options are not sent: responses reach the user through jSMTLIB's own output,
     *  so it is jSMTLIB's output that they redirect. */
    @Override
    public IResponse set_option(IKeyword key, IAttributeValue value) {
        String option = key.value();
        if (Utils.REGULAR_OUTPUT_CHANNEL.equals(option)) {
            String name = (value instanceof IStringLiteral) ? ((IStringLiteral)value).value() : Utils.STDOUT;
            try {
                smtConfig.log.setRegularOutputChannel(name);
            } catch (IOException e) {
                return smtConfig.responseFactory.error("Failed to open regular output: " + e.getMessage(), value.pos());
            }
            options.put(option, value);
            return successOrEmpty(smtConfig);
        }
        if (Utils.DIAGNOSTIC_OUTPUT_CHANNEL.equals(option)) {
            String name = (value instanceof IStringLiteral) ? ((IStringLiteral)value).value() : Utils.STDERR;
            try {
                smtConfig.log.setDiagnosticOutputChannel(name);
            } catch (IOException e) {
                return smtConfig.responseFactory.error("Failed to open diagnostic output: " + e.getMessage(), value.pos());
            }
            options.put(option, value);
            return successOrEmpty(smtConfig);
        }
        return set_option_impl(key, value);
    }

    /** Override in subclasses to handle solver-specific options. Channel options are handled by set_option and never reach here.
     *  This default handles :print-success client-side (see {@link #checkPrintSuccess}):
     *  the solver process is always left with :print-success true at the wire level (see
     *  start()/sendCommand()) -- without that, we'd get no acknowledgment at all for other
     *  commands once a script turns it off -- so it is answered entirely client-side,
     *  matching the local smtConfig.nosuccess flag, and is never itself forwarded to the
     *  solver process. A subclass that overrides set_option_impl for other reasons (e.g.
     *  to also track option values locally) needs its own checkPrintSuccess call, same as
     *  it always has -- this default is only reached by a subclass that doesn't override
     *  set_option_impl at all. */
    protected IResponse set_option_impl(IKeyword key, IAttributeValue value) {
        IResponse r = checkPrintSuccess(smtConfig, key, value);
        if (r != null) return r;
        return sendCommand(smtConfig.commandFactory.set_option(key, value));
    }

    /** @see org.smtlib.ISolver#set_info(IExpr.IKeyword, IExpr.IAttributeValue)  */
    @Override
    public IResponse set_info(IKeyword key, IAttributeValue value){
        return sendCommand(smtConfig.commandFactory.set_info(key, value));
    }

    // The get- commands are sent without checking their preconditions: a conforming solver reports
    // a disabled option or a wrong mode itself. An adapter whose solver answers instead overrides
    // the command to check first, in the modes where its solver answers, using the helpers below.

    /** Whether a check command has been sent since the logic was set (or the solver was reset) */
    private boolean checkMade = false;

    /** Whether the most recent check command was answered sat or unknown, with the assertion stack
     *  unchanged since: SMT-LIB's sat mode (false once the whole-run time limit has ended the solver) */
    protected boolean inSatMode() {
        if (endedByTimeLimit) return false;
        readPipelined(true);
        return smtConfig.responseFactory.sat().equals(checkSatStatus) || smtConfig.responseFactory.unknown().equals(checkSatStatus);
    }

    /** Whether the most recent check command was answered unsat, with the assertion stack unchanged
     *  since: SMT-LIB's unsat mode (false once the whole-run time limit has ended the solver) */
    protected boolean inUnsatMode() {
        if (endedByTimeLimit) return false;
        readPipelined(true);
        return smtConfig.responseFactory.unsat().equals(checkSatStatus);
    }

    /** Returns an error response if the assertion stack has changed since a check command was answered
     *  (SMT-LIB's assert mode, where the get- commands about that check are errors), else null */
    protected /*@Nullable*/ IResponse requireUnchangedSinceCheck(String commandName) {
        if (endedByTimeLimit) return null;
        readPipelined(true);
        if (checkMade && checkSatStatus == null) {
            return smtConfig.responseFactory.error("The " + commandName
                    + " command is not valid once the assertion stack has changed since the last check command");
        }
        return null;
    }

    /** Returns an error response if the given option has not been enabled (per
     *  {@link #get_option(IKeyword)}), else null. */
    protected /*@Nullable*/ IResponse requireOptionEnabled(String commandName, String option) {
        IResponse value = get_option(smtConfig.exprFactory.keyword(option));
        // If asking failed (e.g. the solver has exited), report that rather than claim the option is off
        if (value != null && value.isError()) return value;
        if (smtConfig.responseFactory.timeout().equals(value)) return value; // the solver's whole-run limit ended it
        if (!Utils.TRUE.equals(value)) {
            return smtConfig.responseFactory.error("The " + commandName + " command is only valid if " + option + " has been enabled");
        }
        return null;
    }

    /** Returns an error response unless {@link #checkSatStatus} is sat or unknown, else null. */
    protected /*@Nullable*/ IResponse requireSatOrUnknown(String commandName) {
        if (!smtConfig.responseFactory.sat().equals(checkSatStatus) && !smtConfig.responseFactory.unknown().equals(checkSatStatus)) {
            return smtConfig.responseFactory.error("The " + commandName + " command is only valid immediately after check-sat returned sat or unknown");
        }
        return null;
    }

    /** Returns an error response unless {@link #checkSatStatus} is unsat, else null. */
    protected /*@Nullable*/ IResponse requireUnsat(String commandName, String afterWhat) {
        if (!smtConfig.responseFactory.unsat().equals(checkSatStatus)) {
            return smtConfig.responseFactory.error("The " + commandName + " command is only valid immediately after " + afterWhat + " returned unsat");
        }
        return null;
    }

    /** True if the given raw response text is a flat outcome (empty/success/unsupported/an
     *  {@code (error ...)} s-expression) rather than a structured list — used by the
     *  get_assertions/get_value/get_assignment/get_unsat_core/get_unsat_assumptions
     *  defaults below to decide whether to delegate to {@link #parseResponse(String)} or
     *  reparse the response as the structured list they actually expect. */
    protected boolean isFlatResponse(String response) {
        String r = response.trim();
        return r.isEmpty() || r.equals("success") || r.equals("unsupported") || r.startsWith("(error");
    }

    /** @see org.smtlib.ISolver#get_assertions() */
    @Override
    public IResponse get_assertions(){
        String response = null;
        try {
            // A single read may not capture a multi-line response, so keep reading
            // (paren-balance tracked across all reads so far) until it's complete.
            String sent = translate(smtConfig.commandFactory.get_assertions());
            StringBuilder sb = new StringBuilder();
            readPipelined(true);
            solverProcess.sendNoListen(sent, "\n");
            int parens = 0;
            // Tracks whether the scan is currently inside a double-quoted string literal,
            // carried across reads (a string can in principle straddle a chunk boundary),
            // so that a '(' or ')' inside a string-sort term value doesn't desync the
            // balance count -- same in-string tracking SolverProcess.endsWith() already
            // does for exactly the same reason, just applied incrementally per chunk here
            // instead of rescanning the whole buffer from the start each time.
            boolean inString = false;
            do {
                String s = solverProcess.listen();
                for (int p = 0; p < s.length(); p++) {
                    char c = s.charAt(p);
                    if (c == '"') inString = !inString;
                    else if (!inString) {
                        if (c == '(') parens++;
                        else if (c == ')') parens--;
                    }
                }
                sb.append(s.replace('\n',' ').replace("\r",""));
            } while (parens > 0);
            response = sb.toString();
            if (isFlatResponse(response)) return checkShape(Shape.VALUE, sent, response, checkImmediateExit(parseResponse(response)));
            List<IExpr> exprs = new Parser(smtConfig, new org.smtlib.impl.Pos.Source(response, null)).parseAssertionList();
            return smtConfig.responseFactory.get_assertions_response(exprs);
        } catch (IOException e) {
            return smtConfig.responseFactory.error("Error writing to solver: " + e);
        } catch (IVisitor.VisitorException e) {
            return smtConfig.responseFactory.error("Error writing to solver: " + e);
        } catch (IParser.ParserException e) {
            return smtConfig.responseFactory.error("Unexpected output from the solver: " + response);
        }
    }

    /** @see org.smtlib.ISolver#get_proof()*/
    @Override
    public IResponse get_proof(){
        return proofResponse(sendCommand(smtConfig.commandFactory.get_proof()));
    }

    /** Wraps a parsed get-proof answer as an IProofResponse; anything else (an error,
     *  unsupported) is returned unchanged. */
    protected IResponse proofResponse(IResponse r) {
        return r instanceof org.smtlib.sexpr.ISexpr
                ? smtConfig.responseFactory.get_proof_response((org.smtlib.sexpr.ISexpr)r) : r;
    }

    /** @see org.smtlib.ISolver#get_model()*/
    @Override
    public IResponse get_model(){
        return modelResponse(sendCommand(smtConfig.commandFactory.get_model()));
    }

    /** The get-model response r, without the leading symbol {@code model} if it has one: z3 4.3 to 4.7
     *  and yices2 2.6.5 (with --smt2-model-format) answer {@code (model (define-fun ...) ...)}, where
     *  SMT-LIB has the plain list {@code ((define-fun ...) ...)}. A conforming response, whose elements
     *  are all lists, is unchanged. */
    protected IResponse modelResponse(IResponse r) {
        if (r instanceof org.smtlib.sexpr.ISexpr.ISeq seq && !seq.sexprs().isEmpty()
                && seq.sexprs().get(0) instanceof ISymbol s && s.value().equals("model")) {
            return new org.smtlib.sexpr.Sexpr.Seq(new java.util.ArrayList<>(seq.sexprs().subList(1, seq.sexprs().size())));
        }
        return r;
    }

    /** @see org.smtlib.ISolver#get_unsat_assumptions()*/
    @Override
    public IResponse get_unsat_assumptions(){
        if (endedByTimeLimit) return smtConfig.responseFactory.timeout();
        String response = null;
        try {
            readPipelined(true);
            String sent = translate(smtConfig.commandFactory.get_unsat_assumptions());
            response = solverProcess.sendAndListen(sent, "\n");
            IResponse timedOut = timeLimitResponse(response);
            if (timedOut != null) return timedOut;
            if (isFlatResponse(response)) return checkShape(Shape.VALUE, sent, response, checkImmediateExit(parseResponse(response)));
            List<ISymbol> names = new Parser(smtConfig, new org.smtlib.impl.Pos.Source(response, null)).parseSymbolList();
            return smtConfig.responseFactory.get_unsat_assumptions_response(names);
        } catch (IOException e) {
            IResponse timedOut = timeLimitResponseAfterExit();
            if (timedOut != null) return timedOut;
            return smtConfig.responseFactory.error("Error writing to solver: " + e);
        } catch (IVisitor.VisitorException e) {
            return smtConfig.responseFactory.error("Error writing to solver: " + e);
        } catch (IParser.ParserException e) {
            return smtConfig.responseFactory.error("Unexpected output from the solver: " + response);
        }
    }

    /** @see org.smtlib.ISolver#get_unsat_core()*/
    @Override
    public IResponse get_unsat_core(){
        if (endedByTimeLimit) return smtConfig.responseFactory.timeout();
        String response = null;
        try {
            readPipelined(true);
            String sent = translate(smtConfig.commandFactory.get_unsat_core());
            response = solverProcess.sendAndListen(sent, "\n");
            IResponse timedOut = timeLimitResponse(response);
            if (timedOut != null) return timedOut;
            if (isFlatResponse(response)) return checkShape(Shape.VALUE, sent, response, checkImmediateExit(parseResponse(response)));
            List<ISymbol> names = new Parser(smtConfig, new org.smtlib.impl.Pos.Source(response, null)).parseSymbolList();
            return smtConfig.responseFactory.get_unsat_core_response(names);
        } catch (IOException e) {
            IResponse timedOut = timeLimitResponseAfterExit();
            if (timedOut != null) return timedOut;
            return smtConfig.responseFactory.error("Error writing to solver: " + e);
        } catch (IVisitor.VisitorException e) {
            return smtConfig.responseFactory.error("Error writing to solver: " + e);
        } catch (IParser.ParserException e) {
            return smtConfig.responseFactory.error("Unexpected output from the solver: " + response);
        }
    }

    /** @see org.smtlib.ISolver#get_value(IExpr... )*/
    @Override
    public IResponse get_value(IExpr... terms){
        if (endedByTimeLimit) return smtConfig.responseFactory.timeout();
        String response = null;
        try {
            readPipelined(true);
            String sent = translate(smtConfig.commandFactory.get_value(java.util.Arrays.asList(terms)));
            response = solverProcess.sendAndListen(sent, "\n");
            IResponse timedOut = timeLimitResponse(response);
            if (timedOut != null) return timedOut;
            if (isFlatResponse(response)) return checkShape(Shape.VALUE, sent, response, checkImmediateExit(parseResponse(response)));
            List<IResponse.IPair<IExpr,IExpr>> values = new Parser(smtConfig, new org.smtlib.impl.Pos.Source(response, null)).parseValueList();
            return smtConfig.responseFactory.get_value_response(values);
        } catch (IOException e) {
            IResponse timedOut = timeLimitResponseAfterExit();
            if (timedOut != null) return timedOut;
            return smtConfig.responseFactory.error("Error writing to solver: " + e);
        } catch (IVisitor.VisitorException e) {
            return smtConfig.responseFactory.error("Error writing to solver: " + e);
        } catch (IParser.ParserException e) {
            return smtConfig.responseFactory.error("Unexpected output from the solver: " + response);
        }
    }

    /** @see org.smtlib.ISolver#get_assignment()*/
    @Override
    public IResponse get_assignment(){
        if (endedByTimeLimit) return smtConfig.responseFactory.timeout();
        String response = null;
        try {
            readPipelined(true);
            String sent = translate(smtConfig.commandFactory.get_assignment());
            response = solverProcess.sendAndListen(sent, "\n");
            IResponse timedOut = timeLimitResponse(response);
            if (timedOut != null) return timedOut;
            if (isFlatResponse(response)) return checkShape(Shape.VALUE, sent, response, checkImmediateExit(parseResponse(response)));
            List<IResponse.IPair<ISymbol,Boolean>> assignments = new Parser(smtConfig, new org.smtlib.impl.Pos.Source(response, null)).parseAssignmentList();
            return smtConfig.responseFactory.get_assignment_response(assignments);
        } catch (IOException e) {
            IResponse timedOut = timeLimitResponseAfterExit();
            if (timedOut != null) return timedOut;
            return smtConfig.responseFactory.error("Error writing to solver: " + e);
        } catch (IVisitor.VisitorException e) {
            return smtConfig.responseFactory.error("Error writing to solver: " + e);
        } catch (IParser.ParserException e) {
            return smtConfig.responseFactory.error("Unexpected output from the solver: " + response);
        }
    }

    /** @see org.smtlib.ISolver#get_option(IExpr.IKeyword)*/
    @Override
    public IResponse get_option(IKeyword option){
        // :print-success is answered client-side (see set_option()); the solver process
        // itself is always left at :print-success true, so asking it directly would
        // always report true regardless of the script's own nosuccess state.
        if (option.equals(printSuccess)) return smtConfig.nosuccess ? Utils.FALSE : Utils.TRUE;
        // :regular-output-channel and :diagnostic-output-channel are likewise answered
        // client-side once set (see set_option()): that method only redirects jSMTLIB's own
        // log streams and never forwards the command to the solver process, so forwarding
        // get-option to the solver here would just report the solver's own unchanged
        // default forever, regardless of what the script actually set. Before any
        // set-option, fall through and ask the solver (or let it error) so its own default
        // is used, matching pre-set-option behavior for every other option.
        String opt = option.value();
        if (Utils.REGULAR_OUTPUT_CHANNEL.equals(opt) || Utils.DIAGNOSTIC_OUTPUT_CHANNEL.equals(opt)) {
            IAttributeValue cached = options.get(opt);
            if (cached != null) return cached;
        }
        return sendCommand(smtConfig.commandFactory.get_option(option));
    }

    /** @see org.smtlib.ISolver#get_info(IExpr.IKeyword)*/
    @Override
    public IResponse get_info(IKeyword option){
        return sendCommand(smtConfig.commandFactory.get_info(option), false, true);
    }

    /** @see org.smtlib.ISolver#smt()*/
    @Override
    public Configuration smt() {
        return smtConfig;
    }

    /** @see org.smtlib.ISolver#checkSatStatus()*/
    @Override
    public IResponse checkSatStatus() {
        return checkSatStatus;
    }


    @Override
    public IResponse declare_datatype(Ideclare_datatype cmd) {
        checkSatStatus = null;
        return sendCommand(cmd);
    }


    @Override
    public IResponse declare_datatypes(Ideclare_datatypes cmd) {
        checkSatStatus = null;
        return sendCommand(cmd);
    }
}
