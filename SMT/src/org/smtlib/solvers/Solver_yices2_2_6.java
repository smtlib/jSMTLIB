package org.smtlib.solvers;

import org.smtlib.SMT;

/** yices2 2.6.5: by default it answers get-model in yices's own model format, not SMT-LIB's; with
 *  --smt2-model-format it answers {@code (model (define-fun ...) ...)}, whose wrapper
 *  AbstractSolver#modelResponse removes. yices2 2.7.0 answers in SMT-LIB format and rejects the flag. */
public class Solver_yices2_2_6 extends Solver_yices2 {

    public Solver_yices2_2_6(SMT.Configuration smtConfig, /*@NonNull*/ String[] command) {
        super(smtConfig, command);
    }

    public Solver_yices2_2_6(SMT.Configuration smtConfig, /*@NonNull*/ String command) {
        super(smtConfig, command);
    }

    @Override
    public String[] cmd(String exec) {
        String[] args = super.cmd(exec);
        String[] result = java.util.Arrays.copyOf(args, args.length + 1);
        result[args.length] = "--smt2-model-format";
        return result;
    }
}
