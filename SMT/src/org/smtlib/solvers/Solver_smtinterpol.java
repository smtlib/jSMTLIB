/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.solvers;

import java.nio.charset.StandardCharsets;

import org.smtlib.*;

/** This class is an adapter for SMTInterpol (a Java SMT solver launched as
 *  {@code java -jar smtinterpol-VERSION.jar}, not a native executable): it is a concrete,
 *  silent inheritor of {@link AbstractSolver} -- the base launch command is declared in
 *  jsmtlib.properties via {@code org.smtlib.solver_smtinterpol-2.5.command} (see SMT.startSolver's
 *  {@code %exec%} placeholder substitution), so only the conditional timeout flag and
 *  {@link #start()}/{@link #exit()} (process lifecycle) are handled here, besides the
 *  get- command checks below. Otherwise empirically SMT-LIB compliant: :print-success already defaults to true (no priming
 *  command needed), errors come back as clean (error "...") s-expressions, and
 *  bitvector values print via the equally-valid {@code (_ bvN W)} indexed-literal
 *  form (not #b/#x, but standard concrete syntax that the generic parser handles
 *  without any massaging).
 *  <p>
 *  The {@code -q} flag is required, not cosmetic: without it, SMTInterpol writes a
 *  large volume of "INFO - ..." solver-internal logging to its own stderr for every
 *  check-sat (statistics, per-clause traces, model dumps). That's a separate stream
 *  from the stdout responses SolverProcess parses, but SolverProcess's listen() has a
 *  heuristic (see its "some cases (yices2) the prompt is on the error stream" comment)
 *  that can prefer non-empty stderr content over stdout -- so unsilenced INFO noise
 *  risks being returned as the response instead of the real one. -q suppresses it at
 *  the source rather than relying on that heuristic guessing right. */
public class Solver_smtinterpol extends AbstractSolver implements ISolver {

    /** The command-line arguments for launching the solver. */
    protected String cmds[];

    /** Creates an instance of the solver. The base launch command ("java -jar
     *  &lt;jar&gt; -q") comes from the org.smtlib.solver_smtinterpol-2.5.command
     *  property; only the timeout flag, which is conditional on smtConfig and so
     *  can't be expressed in that static property, is still added here. */
    public Solver_smtinterpol(SMT.Configuration smtConfig, /*@NonNull*/ String[] command) {
        this.smtConfig = smtConfig;
        // SMTInterpol has exactly one timeout flag, -t <milliseconds>, applying per
        // check-sat call -- there is no separate whole-run option at all. If only the
        // whole-run smtConfig.timeoutTotal was requested, it is applied here via -t as the
        // closest available approximation, since that's the only lever SMTInterpol offers.
        double effective = smtConfig.timeout > 0 ? smtConfig.timeout : smtConfig.timeoutTotal;
        if (effective > 0) {
            if (smtConfig.timeout <= 0) {
                smtConfig.log.logDiag("#smtinterpol has no whole-run timeout option; approximating with a per-query -t of " + smtConfig.timeoutTotal + "s (the requested whole-run value)");
            } else if (smtConfig.timeoutTotal > 0) {
                smtConfig.log.logDiag("#smtinterpol has no whole-run timeout option; only the per-query -t (" + smtConfig.timeout + "s) is applied, the whole-run --timeout-total (" + smtConfig.timeoutTotal + "s) is ignored");
            }
            java.util.List<String> args = new java.util.ArrayList<String>(java.util.Arrays.asList(command));
            args.add("-t");
            args.add(Integer.toString((int)Math.ceil(effective * 1000)));
            cmds = args.toArray(new String[args.size()]);
        } else {
            cmds = command;
        }
        // SMTInterpol prints no interactive prompt, so "\n" is the right end marker.
        solverProcess = new SolverProcess(cmds,"\n",smtConfig.logfile,StandardCharsets.UTF_8);
    }

    @Override
    public IResponse start() {
        // smtinterpol runs as java -jar <jar>: java itself starts even when the jar is missing and
        // only then exits, so a missing jar is reported here as a failed start, as for other solvers
        int jar = java.util.Arrays.asList(cmds).indexOf("-jar") + 1;
        if (jar > 0 && jar < cmds.length && !new java.io.File(cmds[jar]).isFile()) {
            return smtConfig.responseFactory.error("Failed to start process " + cmds[jar] + " : no such jar file");
        }
        try {
            solverProcess.start(false);
            if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Started " + smtConfig.solvername);
            return smtConfig.responseFactory.success();
        } catch (Exception e) {
            return smtConfig.responseFactory.error("Failed to start process " + cmds[0] + " : " + e.getMessage());
        }
    }

    // The checks below correct SMTInterpol 2.5 answering get- commands that SMT-LIB makes errors; it
    // reports the other cases itself. It answers get-model and get-value with :produce-models off,
    // though it reports the option as false; get-proof after sat; get-assignment after unsat; and,
    // after declare-* or define-* following a check, where SMT-LIB returns to assert mode, it still
    // answers from the earlier check.

    /** The kinds of command after which SMTInterpol still answers the get- commands about the last
     *  check (probed with 2.5, 2026-10-29); after assert, push, pop and reset-assertions it reports
     *  the error itself */
    private static final java.util.Set<StackChange> ANSWERED_AFTER = java.util.EnumSet.of(
            StackChange.DECLARE_FUN, StackChange.DECLARE_SORT, StackChange.DECLARE_SORT_PARAMETER,
            StackChange.DECLARE_DATATYPE, StackChange.DEFINE_FUN, StackChange.DEFINE_FUN_REC, StackChange.DEFINE_SORT);

    /** SMTInterpol answers get-model with :produce-models off, and in assert mode after a check */
    @Override
    public IResponse get_model() {
        IResponse err = inSatMode() ? requireOptionEnabled("get-model", Utils.PRODUCE_MODELS)
                : requireNoChangeSinceCheck("get-model", ANSWERED_AFTER);
        return err != null ? err : super.get_model();
    }

    /** SMTInterpol answers get-value with :produce-models off, and in assert mode after a check */
    @Override
    public IResponse get_value(IExpr... terms) {
        IResponse err = inSatMode() ? requireOptionEnabled("get-value", Utils.PRODUCE_MODELS)
                : requireNoChangeSinceCheck("get-value", ANSWERED_AFTER);
        return err != null ? err : super.get_value(terms);
    }

    /** SMTInterpol answers get-assignment after unsat, and in assert mode after a check */
    @Override
    public IResponse get_assignment() {
        IResponse err = inUnsatMode() ? requireSatOrUnknown("get-assignment")
                : requireNoChangeSinceCheck("get-assignment", ANSWERED_AFTER);
        return err != null ? err : super.get_assignment();
    }

    /** SMTInterpol answers get-proof after sat, and in assert mode after a check */
    @Override
    public IResponse get_proof() {
        IResponse err = inSatMode() ? requireUnsat("get-proof", "check-sat")
                : requireNoChangeSinceCheck("get-proof", ANSWERED_AFTER);
        return err != null ? err : super.get_proof();
    }

    /** SMTInterpol answers get-unsat-core in assert mode after a check */
    @Override
    public IResponse get_unsat_core() {
        IResponse err = requireNoChangeSinceCheck("get-unsat-core", ANSWERED_AFTER);
        return err != null ? err : super.get_unsat_core();
    }

    /** SMTInterpol answers get-unsat-assumptions in assert mode after a check */
    @Override
    public IResponse get_unsat_assumptions() {
        IResponse err = requireNoChangeSinceCheck("get-unsat-assumptions", ANSWERED_AFTER);
        return err != null ? err : super.get_unsat_assumptions();
    }

}
