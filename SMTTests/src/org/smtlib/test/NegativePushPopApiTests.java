package org.smtlib.test;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;
import org.smtlib.ICommand;
import org.smtlib.IExpr;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.SMT;
import org.smtlib.SolverProcess;
import org.smtlib.solvers.Solver_simplify;
import org.smtlib.solvers.Solver_test;
import org.smtlib.solvers.Solver_z3_4_3;

/** A negative push/pop count can only come from the API (the parser reads numerals as
 *  non-negative). It is an illegal command, so it must produce an error response, never an
 *  exception (#177 item 6d). The local solvers report it themselves; z3-4.3, like the other
 *  process adapters, forwards it and returns the solver's own answer. */
public class NegativePushPopApiTests {

    private static void assertNegativeError(IResponse r) {
        Assert.assertTrue(r.isError());
        Assert.assertEquals("A numeral may not be negative: -1", ((IResponse.IError) r).errorMsg());
    }

    private static void checkLocal(SMT.Configuration config, ISolver solver) {
        IExpr.IFactory f = config.exprFactory;
        ICommand.IFactory cf = config.commandFactory;
        Assert.assertTrue(solver.set_logic("QF_UF", null).isOK());
        assertNegativeError(solver.push(-1));
        assertNegativeError(solver.pop(-1));
        assertNegativeError(cf.push(f.numeral(-1)).execute(solver));
        assertNegativeError(cf.pop(f.numeral(-1)).execute(solver));
    }

    @Test
    public void testSolver() {
        SMT.Configuration config = new SMT.Configuration();
        Solver_test solver = new Solver_test(config, "test");
        Assert.assertTrue(solver.start().isOK());
        checkLocal(config, solver);
        // the stack is unchanged: one pop after one push succeeds, a second does not
        Assert.assertTrue(solver.push(1).isOK());
        Assert.assertTrue(solver.pop(1).isOK());
        Assert.assertTrue(solver.pop(1).isError());
    }

    @Test
    public void simplifySolver() {
        SMT.Configuration config = new SMT.Configuration();
        checkLocal(config, new Solver_simplify(config, "simplify") {
            { solverProcess = new FakeSolverProcess(); }
        });
    }

    @Test
    public void z3_4_3ForwardsToTheSolver() {
        SMT.Configuration config = new SMT.Configuration();
        FakeSolverProcess fake = new FakeSolverProcess();
        Solver_z3_4_3 solver = new Solver_z3_4_3(config, "z3") {
            { solverProcess = fake; }
        };
        fake.reply = "success\n";
        Assert.assertTrue(solver.set_logic("QF_UF", null).isOK());
        for (String cmd : new String[]{"push", "pop"}) {
            fake.reply = "(error \"line 2 column 5: invalid " + cmd + " command\")\n";
            IResponse r = cmd.equals("push") ? solver.push(-1) : solver.pop(-1);
            Assert.assertTrue(r.isError());
            Assert.assertTrue(fake.sent.get(fake.sent.size() - 1).startsWith("(" + cmd + " -1)"));
        }
    }

    /** Records each command and answers with the current canned reply, without a real process. */
    static class FakeSolverProcess extends SolverProcess {
        final List<String> sent = new LinkedList<>();
        String reply = "success\n";

        FakeSolverProcess() {
            super(new String[]{"dummy"}, "\n", null);
        }

        @Override
        public String sendAndListen(String... args) throws IOException {
            StringBuilder sb = new StringBuilder();
            for (String a : args) sb.append(a);
            sent.add(sb.toString());
            return reply;
        }
    }
}
