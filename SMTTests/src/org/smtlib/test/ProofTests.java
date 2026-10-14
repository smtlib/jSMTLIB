package org.smtlib.test;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.concurrent.TimeUnit;

import org.junit.After;
import org.junit.Assert;
import org.junit.Assume;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.junit.runners.ParameterizedWithNames;
import org.smtlib.ICommand;
import org.smtlib.IParser;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.SMT;

/** Tests that get-proof returns the solver's proof as an IProofResponse, for each solver in
 *  SMT_TEST_SOLVERS, and that the printed proof re-parses to the same proof. */
@RunWith(ParameterizedWithNames.class)
public class ProofTests {

    @Rule public Timeout timeout = new Timeout(2, TimeUnit.MINUTES);

    private final String solvername;
    private SMT.Configuration config;
    private ISolver solver;

    public ProofTests(String solvername) {
        this.solvername = solvername;
    }

    @Parameters
    public static Collection<String[]> data() {
        List<String[]> list = new ArrayList<>();
        for (String s : LogicTests.solvers) list.add(new String[]{s});
        return list;
    }

    @Before
    public void start() throws Exception {
        SMT smt = new SMT();
        config = smt.smtConfig;
        config.props = config.readProperties();
        solver = config.createSolver(solvername, smt.resolveExecutableForSolver(solvername));
        IResponse r = solver.start();
        Assert.assertFalse("start: " + r, r.isError());
    }

    @After
    public void stop() {
        if (solver != null) solver.forceExit();
    }

    /** Whether the solver produces proofs (the others answer unsupported or an error) */
    private boolean producesProofs() {
        return (solvername.startsWith("z3") && !solvername.startsWith("z3-4.3"))
                || solvername.startsWith("cvc5") || solvername.startsWith("smtinterpol");
    }

    /** Executes the commands, returning the last response */
    private IResponse run(String text) throws Exception {
        IParser parser = new org.smtlib.sexpr.Parser(config, config.smtFactory.createSource(text, null));
        IResponse r = null;
        ICommand cmd;
        while ((cmd = parser.parseCommand()) != null) r = cmd.execute(solver);
        return r;
    }

    private void checkProof(IResponse r) throws Exception {
        if (!producesProofs()) {
            Assert.assertFalse(r.toString(), r instanceof IResponse.IProofResponse);
            Assert.assertTrue(r.toString(), r.isError() || r == config.responseFactory.unsupported());
            return;
        }
        Assert.assertTrue(r.toString(), r instanceof IResponse.IProofResponse);
        String printed = r.toString();
        IResponse.IProofResponse reparsed = config.responseFactory.get_proof_response(
                new org.smtlib.sexpr.Parser(config, config.smtFactory.createSource(printed, null)).parseSexpr());
        Assert.assertEquals(printed, reparsed.toString());
    }

    @Test
    public void proof() throws Exception {
        checkProof(run("(set-option :produce-proofs true)(set-logic QF_UF)"
                + "(declare-fun p () Bool)(declare-fun q () Bool)"
                + "(assert (and p q))(assert (not p))(check-sat)(get-proof)"));
    }

    /** A long chain of equalities, in few commands: z3's proof nests about 6000 deep and
     *  smtinterpol's about 2000, beyond what a recursive parser or printer can handle.
     *  (cvc5's proof is flat.) */
    @Test
    public void deepProof() throws Exception {
        Assume.assumeTrue("proof not deeply nested", producesProofs() && !solvername.startsWith("cvc5"));
        int n = 2000;
        StringBuilder sb = new StringBuilder("(set-option :produce-proofs true)(set-logic QF_UF)(declare-sort U 0)"
                + "(declare-fun a (Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool) U)(assert (and");
        for (int i = 0; i < n; i++) sb.append(" (= " + constant(i) + " " + constant(i + 1) + ")");
        sb.append("))(assert (not (= " + constant(0) + " " + constant(n) + ")))(check-sat)(get-proof)");
        checkProof(run(sb.toString()));
    }

    /** The i-th distinct constant of sort U: a applied to the bits of i */
    private static String constant(int i) {
        StringBuilder sb = new StringBuilder("(a");
        for (int b = 0; b < 11; b++) sb.append(((i >> b) & 1) != 0 ? " true" : " false");
        return sb.append(")").toString();
    }
}
