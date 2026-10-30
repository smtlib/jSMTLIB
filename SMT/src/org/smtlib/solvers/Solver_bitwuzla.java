/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.solvers;

import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.smtlib.*;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IKeyword;

/** This class is an adapter for Bitwuzla (bit-vectors, floating-point, arrays and
 *  uninterpreted functions -- no arithmetic logics, no datatypes). It is a concrete,
 *  silent inheritor of {@link AbstractSolver} apart from a handful of real, empirically
 *  confirmed (against 0.9.1) protocol gaps:
 *  <p>
 *  1) Bitwuzla has no {@code get-info}, {@code get-option}, {@code get-assertions},
 *  {@code get-assignment} or {@code get-proof} at all -- each is rejected with {@code
 *  [error] <stdin>:L:C: unsupported command '...'} and, critically, that rejection
 *  KILLS the process (see point 2), so these are answered entirely client-side
 *  and never forwarded. {@link #get_option} therefore tracks values itself (via the
 *  inherited {@code options} map, falling back to {@code smtConfig.utils.defaults})
 *  rather than relying on AbstractSolver's default of asking the solver.
 *  <p>
 *  2) Unlike cvc5/yices2 (which die only after some errors), Bitwuzla's process exits
 *  immediately after essentially ANY error -- an unsupported command, an unsupported
 *  logic, a sort mismatch in an assertion, etc. -- not just protocol violations. {@link
 *  #selfReportsImmediateExit()} is therefore true, and {@code :error-behavior} is
 *  reported (via the hardcoded {@link #get_info}) as {@code immediate-exit}, which is
 *  simply the truth for this solver, not a workaround.
 *  <p>
 *  3) Bitwuzla's own error text for a genuine semantic error (e.g. {@code [error]
 *  <stdin>:3:14: expected terms of same sort ...}) is not SMT-LIB {@code (error "...")}
 *  syntax -- the leading {@code [} is not valid s-expression syntax at all, and feeding
 *  it to the standard parser doesn't just fail to parse cleanly, it throws a raw {@code
 *  ClassCastException} out of the lexer (a LexError token reaching code that assumes an
 *  IError) instead of the {@code IParser.ParserException} that {@link
 *  AbstractSolver#parseResponse} already knows how to turn into a clean error response.
 *  {@link #parseResponse} widens that catch locally so a non-conforming response
 *  produces an ordinary error IResponse instead of crashing the whole run.
 *  <p>
 *  4) With its :produce-* option on, Bitwuzla writes nothing at all, or the start of a
 *  list followed by an error on standard error, for get-model, get-value, get-unsat-core
 *  and get-unsat-assumptions when it has no answer (e.g. get-value after unknown, or
 *  get-unsat-core after an assert that followed unsat); it writes nothing or a fragment for
 *  get-unsat-assumptions whenever that option is off. The adapter answers those cases with an
 *  error itself, tracking Bitwuzla's own state (see {@link #lastCheck}). */
public class Solver_bitwuzla extends AbstractSolver implements ISolver {

    @Override
    protected boolean selfReportsImmediateExit() { return true; }

    /** The command-line arguments for launching the solver. */
    protected String cmds[];

    /** Creates an instance of the solver */
    public Solver_bitwuzla(SMT.Configuration smtConfig, /*@NonNull*/ String executable) {
        this.smtConfig = smtConfig;
        List<String> args = new java.util.ArrayList<String>(Arrays.asList(executable,"--lang","smt2"));
        if (smtConfig.seed != 0) {
            args.add("--seed");
            args.add(Integer.toString(smtConfig.seed));
        }
        if (smtConfig.timeout > 0) {
            // --time-limit-per is a per-check-sat timeout in milliseconds (matching
            // smtConfig.timeout's per-query semantics, as opposed to --time-limit,
            // which is a single limit for the whole run).
            args.add("--time-limit-per");
            args.add(Integer.toString((int)Math.ceil(smtConfig.timeout * 1000)));
        }
        if (smtConfig.timeoutTotal > 0) {
            // --time-limit is the whole-run counterpart, also in milliseconds.
            args.add("--time-limit");
            args.add(Integer.toString((int)Math.ceil(smtConfig.timeoutTotal * 1000)));
        }
        cmds = args.toArray(new String[args.size()]);
        // Bitwuzla prints no interactive prompt, so "\n" is the right end marker.
        solverProcess = new SolverProcess(cmds,"\n",smtConfig.logfile,StandardCharsets.UTF_8);
    }

    /** Launches the given command as is (a .command property, #147), without adding the flags
     *  the executable form adds */
    public Solver_bitwuzla(SMT.Configuration smtConfig, /*@NonNull*/ String[] command) {
        this.smtConfig = smtConfig;
        cmds = command;
        solverProcess = new SolverProcess(cmds,"\n",smtConfig.logfile,StandardCharsets.UTF_8);
    }

    @Override
    public IResponse start() {
        try {
            solverProcess.start(false);
            // Bitwuzla's own :print-success default is false (unlike e.g. cvc5, which
            // has a CLI flag for this) -- without explicitly turning it on at the wire
            // level, ordinary accepted commands (set-logic, declare-const, assert, ...)
            // produce no response at all, and sendAndListen just hangs waiting for one.
            solverProcess.sendAndListen("(set-option :print-success true)\n");
            if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Started " + smtConfig.solvername);
            return smtConfig.responseFactory.success();
        } catch (Exception e) {
            return smtConfig.responseFactory.error("Failed to start process " + cmds[0] + " : " + e.getMessage());
        }
    }

    @Override
    protected IResponse parseResponse(String response) {
        IResponse result;
        try {
            result = super.parseResponse(response);
        } catch (RuntimeException e) {
            return smtConfig.responseFactory.error("Unexpected (non-SMT-LIB) response from bitwuzla: " + rewriteStdinLine(response));
        }
        // Parser.parseResponse's fallback for response text that doesn't match any
        // recognized shape (success/sat/error/.../get-info attribute list) just returns
        // whatever the generic sexpr parser produced -- for bitwuzla's non-SMT-LIB
        // "[error] <stdin>:L:C: msg" diagnostic lines, the lexer chokes on the leading
        // '[' and that comes back as a bare lex-error token which satisfies isError()
        // but is NOT actually an IResponse.IError -- callers that safely narrow any
        // isError()==true response to IResponse.IError (e.g. SMT.java's own script
        // loop) get a ClassCastException instead of a clean error message. Catch that
        // shape here and manufacture a real one. Parser.parseResponse now reports such text itself
        // (#118), with a generic message and bitwuzla's own line number, so that is replaced too.
        if (result != null && result.isError() && (!(result instanceof IResponse.IError)
                || ((IResponse.IError)result).errorMsg().startsWith(org.smtlib.sexpr.Parser.UNEXPECTED_RESPONSE))) {
            return smtConfig.responseFactory.error("Unexpected (non-SMT-LIB) response from bitwuzla: " + rewriteStdinLine(response));
        }
        return result;
    }

    /** When its whole-run limit (--time-limit) ends it, Bitwuzla writes unknown -- as the answer to a running
     *  check-sat, or unprompted while idle -- and exits with code 0 (checked with 0.9.1). An unknown for any other
     *  reason (e.g. the per-query limit) leaves it running, so an unknown is the whole-run limit only if the
     *  process then exits. */
    @Override
    protected boolean isTimeLimitResponse(String rawResponse) {
        if (!rawResponse.trim().equals("unknown") || solverProcess == null) return false;
        for (int i = 0; i < 20 && solverProcess.isRunning(true); i++) {
            try {
                Thread.sleep(10);
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
                break;
            }
        }
        return !solverProcess.isRunning(true);
    }

    /** Bitwuzla writes its errors as "[error] ..." lines (class comment point 3), so for the get-
     *  commands that parse a list reply such a line goes to {@link #parseResponse}, not the list parser. */
    @Override
    protected boolean isFlatResponse(String response) {
        return super.isFlatResponse(response) || response.trim().startsWith("[error]");
    }

    /** Bitwuzla's diagnostics begin "{@code <stdin>:L:C:}", counting the lines of its whole input */
    private static final List<Pattern> LINE_NUMBERS = List.of(Pattern.compile("(<stdin>:)(\\d+)(:)"));

    @Override
    protected List<Pattern> lineNumberPatterns() {
        return LINE_NUMBERS;
    }

    /** A redefinition error also names the line of the earlier definition: "at line L column C" */
    private static final Pattern AT_LINE = Pattern.compile("(at line )(\\d+)( column)");

    @Override
    protected boolean reportsEarlierLines() {
        return true;
    }

    /** The diagnostic with its line numbers rewritten as source lines (see linesOffset) */
    private String rewriteStdinLine(String response) {
        Matcher m = AT_LINE.matcher(withSourceLines(response));
        StringBuilder sb = new StringBuilder();
        while (m.find()) {
            int n = Integer.parseInt(m.group(2));
            m.appendReplacement(sb, Matcher.quoteReplacement(m.group(1) + earlierSourceLine(n) + m.group(3)));
        }
        m.appendTail(sb);
        return sb.toString();
    }

    /** Sent to bitwuzla, and also kept here for get_option, which bitwuzla does not support */
    @Override
    protected IResponse set_option_impl(IKeyword key, IAttributeValue value) {
        IResponse r = checkPrintSuccess(smtConfig, key, value);
        if (r != null) return r;
        options.put(key.value(), value);
        return sendCommand(smtConfig.commandFactory.set_option(key, value));
    }


    /** Answered entirely client-side (never forwarded -- see class comment point 1):
     *  from whatever this run has set via {@link #set_option_impl}, falling back to the
     *  standard SMT-LIB default for any option never set, and "unsupported" for anything
     *  not a recognized standard option at all (matching what a compliant solver would
     *  say about an option it doesn't have). */
    @Override
    public IResponse get_option(IKeyword key) {
        if (key.equals(printSuccess)) return smtConfig.nosuccess ? Utils.FALSE : Utils.TRUE;
        String opt = key.value();
        IAttributeValue value = options.get(opt);
        if (value == null) value = smtConfig.utils.defaults.get(opt);
        if (value == null) return smtConfig.responseFactory.unsupported();
        return value;
    }

    /** Answered entirely client-side (never forwarded -- see class comment point 1).
     *  :version/:authors are fixed to the 0.9.1 build this adapter was written and
     *  tested against; if jsmtlib.properties is ever pointed at a different Bitwuzla
     *  build, update these to match. */
    @Override
    public IResponse get_info(IKeyword key) {
        IAttributeValue lit;
        if (Utils.ERROR_BEHAVIOR.equals(key)) {
            lit = smtConfig.exprFactory.symbol(Utils.IMMEDIATE_EXIT);
        } else if (Utils.AUTHORS.equals(key)) {
            lit = smtConfig.exprFactory.unquotedString("Aina Niemetz, Mathias Preiner, and contributors");
        } else if (Utils.VERSION.equals(key)) {
            lit = smtConfig.exprFactory.unquotedString("0.9.1");
        } else if (Utils.NAME.equals(key)) {
            lit = smtConfig.exprFactory.unquotedString("Bitwuzla");
        } else {
            return smtConfig.responseFactory.unsupported();
        }
        IAttribute<?> attr = smtConfig.exprFactory.attribute(key,lit);
        return smtConfig.responseFactory.get_info_response(attr);
    }

    /** Bitwuzla rejects get-proof as an unsupported command and exits (class comment point 1);
     *  a conforming solver without proofs answers unsupported. */
    @Override
    public IResponse get_proof() {
        return smtConfig.responseFactory.unsupported();
    }

    /** See {@link #get_proof()}: Bitwuzla rejects get-assignment the same way. */
    @Override
    public IResponse get_assignment() {
        return smtConfig.responseFactory.unsupported();
    }

    /** See {@link #get_proof()}: Bitwuzla rejects get-assertions the same way. */
    @Override
    public IResponse get_assertions() {
        return smtConfig.responseFactory.unsupported();
    }

    // Bitwuzla's own state for the get- commands of class comment point 4: the result of its last
    // check-sat or check-sat-assuming (kept until reset), whether no assert, push, pop or
    // reset-assertions has come since, and which :produce-* options were on when it ran (Bitwuzla
    // accepts these options after set-logic, but one set after the check does not apply to it).

    /** The response to the last check-sat or check-sat-assuming since start or reset, else null */
    private /*@Nullable*/ IResponse lastCheck = null;
    /** Whether no assert, push, pop or reset-assertions has come since {@link #lastCheck} */
    private boolean lastCheckCurrent = false;
    /** The :produce-* options that were on when {@link #lastCheck} ran */
    private final java.util.Set<String> optionsAtCheck = new java.util.HashSet<>();

    private IResponse recordCheck(IResponse result) {
        lastCheck = result;
        lastCheckCurrent = true;
        optionsAtCheck.clear();
        for (String o: new String[]{Utils.PRODUCE_MODELS, Utils.PRODUCE_UNSAT_CORES, Utils.PRODUCE_UNSAT_ASSUMPTIONS}) {
            if (optionOn(o)) optionsAtCheck.add(o);
        }
        return result;
    }

    private boolean optionOn(String option) {
        return Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(option)));
    }

    /** The response to {@link #lastCheck}, read first if it was pipelined */
    private /*@Nullable*/ IResponse lastResult() {
        readPipelined(true);
        return lastCheck instanceof Pending p ? p.response() : lastCheck;
    }

    @Override
    public IResponse check_sat() {
        return recordCheck(super.check_sat());
    }

    @Override
    public IResponse check_sat_assuming(IExpr ... exprs) {
        return recordCheck(super.check_sat_assuming(exprs));
    }

    // Bitwuzla does not support declare-datatype(s), define-fun-rec, define-funs-rec or
    // declare-sort-parameter, and instead of answering unsupported it writes "[error] expected
    // command" and exits; so these are answered unsupported here and not sent.

    /** Not sent: Bitwuzla exits on it (see above) */
    @Override
    public IResponse declare_datatype(ICommand.Ideclare_datatype cmd) {
        return unsupportedHere();
    }

    /** Not sent: Bitwuzla exits on it (see above) */
    @Override
    public IResponse declare_datatypes(ICommand.Ideclare_datatypes cmd) {
        return unsupportedHere();
    }

    /** Not sent: Bitwuzla exits on it (see above) */
    @Override
    public IResponse define_fun_rec(ICommand.Idefine_fun_rec cmd) {
        return unsupportedHere();
    }

    /** Not sent: Bitwuzla exits on it (see above) */
    @Override
    public IResponse define_funs_rec(ICommand.Idefine_funs_rec cmd) {
        return unsupportedHere();
    }

    /** Not sent: Bitwuzla exits on it (see above) */
    @Override
    public IResponse declare_sort_parameter(ICommand.Ideclare_sort_parameter cmd) {
        return unsupportedHere();
    }

    private IResponse unsupportedHere() {
        return smtConfig.responseFactory.unsupported();
    }

    @Override
    public IResponse assertExpr(IExpr sexpr) {
        lastCheckCurrent = false;
        return super.assertExpr(sexpr);
    }

    @Override
    public IResponse push(int number) {
        lastCheckCurrent = false;
        return super.push(number);
    }

    @Override
    public IResponse pop(int number) {
        lastCheckCurrent = false;
        return super.pop(number);
    }

    @Override
    public IResponse reset_assertions() {
        lastCheckCurrent = false;
        return super.reset_assertions();
    }

    /** Bitwuzla's reset restores its option defaults, so the values get_option answers from are
     *  dropped too (except the output channels, which are jSMTLIB's own and stay redirected). */
    @Override
    public IResponse reset() {
        options.keySet().removeIf(k -> !Utils.REGULAR_OUTPUT_CHANNEL.equals(k) && !Utils.DIAGNOSTIC_OUTPUT_CHANNEL.equals(k));
        lastCheck = null;
        lastCheckCurrent = false;
        return super.reset();
    }

    /** The kinds of command after which Bitwuzla still answers the get- commands about the last check
     *  (probed with 0.9.1, 2026-10-29); after assert, push, pop and reset-assertions it reports the
     *  error itself (or writes nothing, handled below). */
    private static final java.util.Set<StackChange> ANSWERED_AFTER = java.util.EnumSet.of(
            StackChange.DECLARE_FUN, StackChange.DECLARE_SORT, StackChange.DEFINE_SORT, StackChange.DEFINE_FUN);

    /** As {@link #ANSWERED_AFTER}, and reset-assertions, after which Bitwuzla crashes on get-model */
    private static final java.util.Set<StackChange> GET_MODEL_GUARDED_AFTER = java.util.EnumSet.of(
            StackChange.DECLARE_FUN, StackChange.DECLARE_SORT, StackChange.DEFINE_SORT, StackChange.DEFINE_FUN,
            StackChange.RESET_ASSERTIONS);

    /** With :produce-models on, Bitwuzla writes nothing for get-model unless its last check
     *  returned sat (and crashes if a reset came since); after an assert, push, pop or
     *  reset-assertions, or with the option set after the check, it writes an ordinary error.
     *  Bitwuzla also answers it in assert mode, after a declare or define following the check. */
    @Override
    public IResponse get_model() {
        IResponse unchanged = requireNoChangeSinceCheck("get-model", GET_MODEL_GUARDED_AFTER);
        if (unchanged != null) return unchanged;
        if (optionOn(Utils.PRODUCE_MODELS)) {
            IResponse r = lastResult();
            if (!smtConfig.responseFactory.sat().equals(r)) return noModel("get-model", r);
        }
        return super.get_model();
    }

    /** With :produce-models on, Bitwuzla writes nothing for get-value unless its last check
     *  returned sat, and a fragment and an error if an assert, push, pop or reset-assertions came
     *  since or the option was set after the check.
     *  Bitwuzla also answers it in assert mode, after a declare or define following the check. */
    @Override
    public IResponse get_value(IExpr... terms) {
        IResponse unchanged = requireNoChangeSinceCheck("get-value", ANSWERED_AFTER);
        if (unchanged != null) return unchanged;
        if (optionOn(Utils.PRODUCE_MODELS)) {
            IResponse r = lastResult();
            if (!smtConfig.responseFactory.sat().equals(r) || !lastCheckCurrent) return noModel("get-value", r);
            if (!optionsAtCheck.contains(Utils.PRODUCE_MODELS)) return enabledTooLate("get-value", Utils.PRODUCE_MODELS);
        }
        return super.get_value(terms);
    }

    /** With :produce-unsat-cores on, Bitwuzla writes nothing for get-unsat-core unless its last
     *  check returned unsat, and a fragment and an error if an assert, push, pop, reset-assertions
     *  or reset came since or the option was set after the check.
     *  Bitwuzla also answers it in assert mode, after a declare or define following the check. */
    @Override
    public IResponse get_unsat_core() {
        IResponse unchanged = requireNoChangeSinceCheck("get-unsat-core", ANSWERED_AFTER);
        if (unchanged != null) return unchanged;
        if (optionOn(Utils.PRODUCE_UNSAT_CORES)) {
            IResponse err = requireCurrentUnsat("get-unsat-core", "check-sat", Utils.PRODUCE_UNSAT_CORES);
            if (err != null) return err;
        }
        return super.get_unsat_core();
    }

    /** Bitwuzla writes nothing for get-unsat-assumptions unless its last check returned unsat; then
     *  it writes a fragment and an error if the option is off or was set after the check, or an
     *  assert, push, pop, reset-assertions or reset came since.
     *  Bitwuzla also answers it in assert mode, after a declare or define following the check. */
    @Override
    public IResponse get_unsat_assumptions() {
        IResponse unchanged = requireNoChangeSinceCheck("get-unsat-assumptions", ANSWERED_AFTER);
        if (unchanged != null) return unchanged;
        if (!optionOn(Utils.PRODUCE_UNSAT_ASSUMPTIONS)) {
            return smtConfig.responseFactory.error("The get-unsat-assumptions command is only valid if "
                    + Utils.PRODUCE_UNSAT_ASSUMPTIONS + " has been enabled");
        }
        // The same text as AbstractSolver.requireUnsat's
        IResponse err = requireCurrentUnsat("get-unsat-assumptions", "check-sat-assuming", Utils.PRODUCE_UNSAT_ASSUMPTIONS);
        if (err != null) return err;
        return super.get_unsat_assumptions();
    }

    /** The error for a get-model or get-value Bitwuzla has no model for */
    private IResponse noModel(String command, /*@Nullable*/ IResponse result) {
        if (lastCheckCurrent && smtConfig.responseFactory.unknown().equals(result)) {
            return smtConfig.responseFactory.error("The " + command + " command has no model to report after check-sat returned unknown");
        }
        return smtConfig.responseFactory.error("The " + command + " command is only valid immediately after check-sat returned sat or unknown");
    }

    /** An error unless the last check returned unsat, no assert, push, pop or reset-assertions
     *  came since and the option was on when it ran; else null */
    private /*@Nullable*/ IResponse requireCurrentUnsat(String command, String afterWhat, String option) {
        if (!smtConfig.responseFactory.unsat().equals(lastResult()) || !lastCheckCurrent) {
            return smtConfig.responseFactory.error("The " + command + " command is only valid immediately after " + afterWhat + " returned unsat");
        }
        if (!optionsAtCheck.contains(option)) return enabledTooLate(command, option);
        return null;
    }

    private IResponse enabledTooLate(String command, String option) {
        return smtConfig.responseFactory.error("The " + command + " command is only valid if " + option + " was enabled before the last check");
    }

}
