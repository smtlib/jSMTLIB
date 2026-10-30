/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.solvers;

import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.List;
import java.util.regex.Pattern;

import org.smtlib.*;

/** This class is an adapter for recent z3 versions (empirically verified against 4.8.12 and
 *  4.10.2), on the assumption that they are (or should be) fully SMT-LIB compliant: it is a
 *  concrete, silent inheritor of {@link AbstractSolver} -- only the startup command line and
 *  {@link #start()}/{@link #exit()} (process lifecycle) are overridden. Empirically, none of
 *  the z3-4.3-era workarounds the old version-specific adapters needed (see the git history of
 *  the now-removed Solver_z3_4_5/4_6/4_7/4_8 classes) are needed any more:
 *  bitvector literals print in standard #b/#x form (no bv5[8]-style regex conversion needed),
 *  and errors come back as clean, well-formed (error "...") s-expressions that
 *  AbstractSolver's generic parseResponse handles without any massaging.
 *  <p>
 *  {@code :print-success} needs an explicit priming command on Linux specifically, same
 *  idea as {@link Solver_z3_4_3}: jSMTLIB's own protocol expects a response to every
 *  command it sends, and print-success false (the SMT-LIB-compliant default) means most
 *  commands legitimately produce none on their own. Confirmed via gdb-attaching to a hung
 *  z3 process on Linux CI that the very first real command produced no response at all --
 *  z3 sitting in its own SMT2 scanner blocked reading stdin for more input, having
 *  silently consumed the command and moved on without acking it, which jSMTLIB has no way
 *  to distinguish from a solver that's simply slow, so it just waited forever. macOS/
 *  Windows don't hit this and already have goldens reflecting an un-primed first response,
 *  so the priming command below is Linux-only rather than unconditional -- doing it
 *  everywhere would shift every line-numbered error message on every platform by one, not
 *  just the platform that actually needs it.
 *  <p>
 *  One confirmed compliance gap, not caused by this adapter: z3 defaults
 *  {@code :produce-models} to {@code true} rather than the spec's {@code false}, with no
 *  known CLI flag or startup option to change that -- scripts checking that default need a
 *  z3-specific golden reflecting it. */
public class Solver_z3_recent extends AbstractSolver implements ISolver {

    /** The command-line arguments for launching the solver. */
    protected String cmds[];
    // WARNING=false suppresses z3's own diagnostic WARNING messages (e.g. "pattern does not
    // contain all quantified variables"): these print as a bare "WARNING" line with no
    // parens before the rest of the message follows on a later flush, which fools
    // SolverProcess's paren-balance response-completion heuristic into treating the
    // response as already complete and truncating it.
    protected String cmds_win[] = new String[]{ "", "-smt2","-in","SMTLIB2_COMPLIANT=true","WARNING=false"};
    protected String cmds_mac[] = new String[]{ "", "-smt2","-in","SMTLIB2_COMPLIANT=true","WARNING=false"};
    protected String cmds_unix[] = new String[]{ "", "-smt2","-in","SMTLIB2_COMPLIANT=true","WARNING=false"};

    /** True only on the platform where the print-success priming command below is needed
     *  (see the class javadoc) */
    protected final boolean needsPrintSuccessPriming = !isWindows && !isMac;

    /** z3 reports "line N column C" in its error messages, counting the lines of its whole input */
    private static final List<Pattern> LINE_NUMBERS = List.of(Pattern.compile("(line )(\\d+)( column)"));

    @Override
    protected List<Pattern> lineNumberPatterns() {
        return LINE_NUMBERS;
    }

    /** Creates an instance of the solver */
    public Solver_z3_recent(SMT.Configuration smtConfig, /*@NonNull*/ String executable) {
        this.smtConfig = smtConfig;
        if (isWindows) {
            cmds = cmds_win;
        } else if (isMac) {
            cmds = cmds_mac;
        } else {
            cmds = cmds_unix;
        }
        double timeout = smtConfig.timeout;
        double timeoutTotal = smtConfig.timeoutTotal;
        if (timeout > 0 || timeoutTotal > 0) {
            List<String> args = new java.util.ArrayList<String>(Arrays.asList(cmds));
            // Recent z3's own -t: is per-query but in MILLISECONDS (unlike z3-4.3's -t:,
            // which is seconds -- the unit silently changed between versions); -T: is the
            // whole-run limit and stayed in seconds. Earlier code here wired
            // smtConfig.timeout (per-query) to -T: (whole-run) -- wrong flag for the
            // intended semantics -- fixed to use -t: for the per-query value.
            if (timeout > 0) args.add("-t:" + Long.toString(Math.round(timeout*1000)));
            if (timeoutTotal > 0) args.add("-T:" + Integer.toString((int)Math.ceil(timeoutTotal)));
            cmds = args.toArray(new String[args.size()]);
        }
        cmds[0] = executable;
        // z3 -in does not print an interactive prompt, so "\n" is the right end marker.
        solverProcess = new SolverProcess(cmds,"\n",smtConfig.logfile,StandardCharsets.UTF_8);
    }

    /** Launches the given command as is (a .command property, #147), without adding the flags
     *  the executable form adds */
    public Solver_z3_recent(SMT.Configuration smtConfig, /*@NonNull*/ String[] command) {
        this.smtConfig = smtConfig;
        cmds = command;
        solverProcess = new SolverProcess(cmds,"\n",smtConfig.logfile,StandardCharsets.UTF_8);
    }

    @Override
    public IResponse start() {
        try {
            solverProcess.start(false);
            if (needsPrintSuccessPriming) {
                solverProcess.sendAndListen("(set-option :print-success true)\n");
            }
            if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Started " + smtConfig.solvername);
            return smtConfig.responseFactory.success();
        } catch (Exception e) {
            return smtConfig.responseFactory.error("Failed to start process " + cmds[0] + " : " + e.getMessage());
        }
    }

    /** z3 reports a query stopped by its per-query time limit, -t:, with :reason-unknown "canceled" in incremental
     *  mode (after a push; checked with z3 4.16.0 and 5.1.0, while 4.8.12 and 4.12.6 give up first, as incomplete),
     *  and in every mode in 4.6 and 4.7; one-shot queries in newer versions, and other solvers such as cvc5, report
     *  "timeout". jSMTLIB sets no other limit that cancels a query, so when the per-query limit is set, "canceled" is
     *  reported as "timeout" (OpenJML#1022). */
    @Override
    public IResponse get_info(org.smtlib.IExpr.IKeyword key) {
        IResponse response = super.get_info(key);
        if (smtConfig.timeout > 0 && ":reason-unknown".equals(key.value())
                && response instanceof IResponse.IAttributeList list && list.attributes().size() == 1
                && "canceled".equals(stripQuotes(list.attributes().get(0).attrValue().toString()))) {
            return smtConfig.responseFactory.get_info_response(
                    smtConfig.exprFactory.attribute(key, smtConfig.exprFactory.symbol("timeout"))); // as cvc5 reports it
        }
        return response;
    }

    private static String stripQuotes(String s) {
        return s.length() >= 2 && s.startsWith("\"") && s.endsWith("\"") ? s.substring(1, s.length() - 1) : s;
    }

    /** z3 answers 'timeout' (instead of a result) when its whole-run limit, -T:, ends it, and then exits
     *  (checked with z3 4.16.0 and 5.1.0) */
    @Override
    protected boolean isTimeLimitResponse(String rawResponse) {
        return rawResponse.trim().equals("timeout");
    }

    // The checks below correct recent z3 answering get- commands that SMT-LIB makes errors; it
    // reports the other cases itself. Every version answers get-assignment with
    // :produce-assignments off, though it reports the option as false. After some commands following
    // a check (see answeredAfter), where SMT-LIB returns to assert mode, z3 still answers from the
    // earlier check. The :produce-models default of true (see the class Javadoc) is not checked: z3
    // reports the option as true.

    /** The kinds of command after which this z3 still answers the get- commands about the last check
     *  (probed 2026-10-29: z3 4.6 to 5.1 after every declare and define; 4.8 and later also after
     *  reset-assertions, which 4.6 and 4.7 report themselves). After assert, push or pop z3 reports
     *  the error itself. */
    protected java.util.Set<StackChange> answeredAfter() {
        return java.util.EnumSet.of(StackChange.DECLARE_FUN, StackChange.DECLARE_SORT,
                StackChange.DECLARE_SORT_PARAMETER, StackChange.DECLARE_DATATYPE,
                StackChange.DEFINE_FUN, StackChange.DEFINE_FUN_REC,
                StackChange.DEFINE_SORT, StackChange.RESET_ASSERTIONS);
    }

    /** z3 answers get-assignment with :produce-assignments off, and in assert mode after a check */
    @Override
    public IResponse get_assignment() {
        IResponse err = inSatMode() ? requireOptionEnabled("get-assignment", Utils.PRODUCE_ASSIGNMENTS)
                : requireNoChangeSinceCheck("get-assignment", answeredAfter());
        return err != null ? err : super.get_assignment();
    }

    /** z3 answers get-model in assert mode after a check */
    @Override
    public IResponse get_model() {
        IResponse err = requireNoChangeSinceCheck("get-model", answeredAfter());
        return err != null ? err : super.get_model();
    }

    /** z3 answers get-value in assert mode after a check */
    @Override
    public IResponse get_value(IExpr... terms) {
        IResponse err = requireNoChangeSinceCheck("get-value", answeredAfter());
        return err != null ? err : super.get_value(terms);
    }

    /** z3 answers get-proof in assert mode after a check */
    @Override
    public IResponse get_proof() {
        IResponse err = requireNoChangeSinceCheck("get-proof", answeredAfter());
        return err != null ? err : super.get_proof();
    }

    /** The printed assumptions of the most recent check command if it was check-sat-assuming, else null */
    private /*@Nullable*/ List<String> lastAssumptions = null;

    @Override
    public IResponse check_sat() {
        lastAssumptions = null;
        return super.check_sat();
    }

    @Override
    public IResponse check_sat_assuming(IExpr... exprs) {
        lastAssumptions = new java.util.ArrayList<>();
        try {
            for (IExpr e : exprs) lastAssumptions.add(translate(e));
        } catch (IVisitor.VisitorException e) {
            lastAssumptions = null;
        }
        return super.check_sat_assuming(exprs);
    }

    @Override
    public IResponse reset() {
        lastAssumptions = null;
        return super.reset();
    }

    /** Whether the expression is one of the assumptions of the last check-sat-assuming */
    private boolean isAssumption(IExpr e) {
        try {
            return lastAssumptions.contains(translate(e));
        } catch (IVisitor.VisitorException ex) {
            return false;
        }
    }

    // After check-sat-assuming, z3 answers get-unsat-core and get-unsat-assumptions alike with one list
    // combining the core's labels and the unsat assumptions (e.g. (p a1 (not q))), whereas SMT-LIB's unsat
    // core holds only labels and its unsat assumptions only assumptions. These filters correct that.

    /** Drops the assumptions z3 adds to the unsat core (see above) */
    @Override
    protected List<IExpr> unsatCoreElements(List<IExpr> reply) {
        if (lastAssumptions == null) return reply;
        return reply.stream().filter(e -> !isAssumption(e)).toList();
    }

    /** Drops the labels z3 adds to the unsat assumptions (see above) */
    @Override
    protected List<IExpr> unsatAssumptionsElements(List<IExpr> reply) {
        if (lastAssumptions == null) return reply;
        return reply.stream().filter(this::isAssumption).toList();
    }

    /** z3 answers get-unsat-core in assert mode after a check */
    @Override
    public IResponse get_unsat_core() {
        IResponse err = requireNoChangeSinceCheck("get-unsat-core", answeredAfter());
        return err != null ? err : super.get_unsat_core();
    }

    /** z3 answers get-unsat-assumptions in assert mode after a check */
    @Override
    public IResponse get_unsat_assumptions() {
        IResponse err = requireNoChangeSinceCheck("get-unsat-assumptions", answeredAfter());
        return err != null ? err : super.get_unsat_assumptions();
    }

}
