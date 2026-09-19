package org.smtlib.test.bugs;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.SMT;
import org.smtlib.SolverProcess;
import org.smtlib.solvers.Solver_z3_4_3_2;

/**
 * Pins down issue #51: {@code Solver_z3_4_3_2}'s {@code NAME_VALUE = "z3-4.3.2"} redeclares
 * (field-hides, not overrides -- Java fields aren't polymorphic) the parent
 * {@code Solver_z3_4_3}'s own {@code NAME_VALUE = "z3-4.3"} field. {@code start()} is inherited
 * unchanged from the parent and references {@code NAME_VALUE} directly (not through an
 * accessor), so it statically binds to the parent class's own field at compile time --
 * the startup diagnostic log always prints "#Started z3-4.3 ", never "z3-4.3.2", regardless of
 * which class is actually instantiated.
 * <p>
 * Fixed by turning {@code NAME_VALUE} into a real, overridable {@code name()} method that
 * {@code start()} calls, instead of a hidden field.
 * <p>
 * Reproduced with a fake {@code SolverProcess} that never spawns a real z3 process, capturing
 * the diagnostic output stream directly.
 * <p>
 * See <a href="https://github.com/smtlib/jSMTLIB/issues/51">issue #51</a>.
 */
public class SolverZ4332NameValueFieldHidingBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    /** A SolverProcess that never touches a real process: start() is a no-op, and
     *  sendAndListen() returns a canned "success" reply. */
    static class FakeSolverProcess extends SolverProcess {
        FakeSolverProcess() {
            super(new String[]{"dummy"}, "\n", null);
        }

        @Override
        public void start(boolean listen) {
            // no-op -- never spawns a real process
        }

        @Override
        public String sendAndListen(String... args) throws IOException {
            return "success\n";
        }
    }

    static class TestableSolver extends Solver_z3_4_3_2 {
        TestableSolver(SMT.Configuration config) {
            super(config, "z3");
            this.solverProcess = new FakeSolverProcess();
        }
    }

    @Test
    public void startupDiagnosticNamesTheActualSubclassNotTheParent() {
        SMT.Configuration config = new SMT.Configuration();
        config.verbose = 1;
        ByteArrayOutputStream diagBuf = new ByteArrayOutputStream();
        config.log.setChannels(config.log.getOut(), new PrintStream(diagBuf));

        TestableSolver solver = new TestableSolver(config);

        solver.start();

        String diag = diagBuf.toString();
        Assert.assertTrue("expected the startup diagnostic to name z3-4.3.2 (the actual "
                + "subclass), got: " + diag, diag.contains("z3-4.3.2"));
    }
}
