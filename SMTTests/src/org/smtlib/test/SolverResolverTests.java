package org.smtlib.test;

import java.util.Properties;
import java.util.Set;
import java.util.function.Function;

import org.junit.Assert;
import org.junit.Test;
import org.smtlib.ISolver;
import org.smtlib.SolverResolver;
import org.smtlib.SolverResolver.Resolution;

/** The solver resolution rules of {@link SolverResolver} (#123), against made-up properties, a
 *  made-up class lookup and a solver directory that does not exist: no solver is needed. */
public class SolverResolverTests {

    private static final String P = "org.smtlib.solver_";
    private static final String DIR = "/no/such/solver/dir";

    /** A class lookup that knows only the given class names (any class stands in for them) */
    private static Function<String, Class<?>> known(String... names) {
        Set<String> set = Set.of(names);
        return n -> set.contains(n) ? Object.class : null;
    }

    private static Properties props(String... keyValues) {
        Properties p = new Properties();
        for (int i = 0; i < keyValues.length; i += 2) p.setProperty(P + keyValues[i], keyValues[i + 1]);
        return p;
    }

    private static Resolution resolve(Properties props, String name, String exec, Function<String, Class<?>> lookup)
            throws ISolver.CreationException {
        return SolverResolver.resolve(props, name, exec, "linux", DIR, lookup);
    }

    @Test
    public void platformAdapterBeforePlainAdapter() throws Exception {
        Properties p = props("s.adapter.linux", "a.Linux", "s.adapter", "a.Plain");
        Assert.assertEquals("a.Linux", resolve(p, "s", null, known("a.Linux", "a.Plain")).adapterClassName());
        Assert.assertEquals("a.Plain", SolverResolver.resolve(p, "s", null, "macos", DIR, known("a.Linux", "a.Plain")).adapterClassName());
    }

    @Test
    public void unloadableAdapterFallsBackToConvention() throws Exception {
        Properties p = props("s.adapter", "a.Missing");
        Assert.assertEquals("org.smtlib.solvers.Solver_s", resolve(p, "s", null, known("org.smtlib.solvers.Solver_s")).adapterClassName());
    }

    @Test
    public void namingConvention() throws Exception {
        String cls = "org.smtlib.solvers.Solver_cvc5_1_3_2";
        Assert.assertEquals(cls, resolve(null, "cvc5-1.3.2", null, known(cls)).adapterClassName());
    }

    @Test
    public void z3Fallback() throws Exception {
        String cls = "org.smtlib.solvers.Solver_z3_recent";
        Assert.assertEquals(cls, resolve(null, "z3-9.9.9", null, known(cls)).adapterClassName());
    }

    @Test
    public void genericFallback() throws Exception {
        Resolution r = resolve(null, "newsolver", null, known());
        Assert.assertEquals("org.smtlib.solvers.Solver_smt", r.adapterClassName());
        Assert.assertEquals(org.smtlib.solvers.Solver_smt.class, r.adapterClass());
    }

    @Test
    public void testPseudoSolver() throws Exception {
        Resolution r = resolve(props("test.exec", "ignored"), "test", "given", known());
        Assert.assertEquals(org.smtlib.solvers.Solver_test.class, r.adapterClass());
        Assert.assertEquals("given", r.executable());
        Assert.assertNull(r.command());
    }

    @Test
    public void solverNameIsReported() throws Exception {
        Assert.assertEquals("cvc5-1.3.2", resolve(null, "cvc5-1.3.2", null, known()).solvername());
    }

    @Test
    public void emptyCommandIsAnError() {
        try {
            resolve(props("s.command", ",,"), "s", null, known());
            Assert.fail("expected a CreationException");
        } catch (ISolver.CreationException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("appears to have no content"));
        }
    }

    @Test
    public void executableLookupOrder() throws Exception {
        Properties p = props("s.exec.linux", "s-linux", "s.exec", "s-plain");
        Assert.assertEquals(DIR + "/s-linux", resolve(p, "s", null, known()).executable());
        Assert.assertEquals(DIR + "/s-plain", SolverResolver.resolve(p, "s", null, "windows", DIR, known()).executable());
        // the caller's executable wins, and an absolute path is used as given
        Assert.assertEquals("/abs/solver", resolve(p, "s", "/abs/solver", known()).executable());
        // a blank .exec counts as none: the solver name is the executable
        Assert.assertEquals(DIR + "/s", resolve(props("s.exec", "  "), "s", null, known()).executable());
    }

    @Test
    public void execPlaceholderSubstitution() throws Exception {
        Resolution r = resolve(props("s.command", "java,-jar,%exec%,-q", "s.exec", "s.jar"), "s", null, known());
        Assert.assertArrayEquals(new String[]{"java", "-jar", DIR + "/s.jar", "-q"}, r.command());
    }

    @Test
    public void argv0Substitution() throws Exception {
        Resolution r = resolve(props("s.command", "s,--lang,smt2", "s.exec", "s-1.0"), "s", null, known());
        Assert.assertArrayEquals(new String[]{DIR + "/s-1.0", "--lang", "smt2"}, r.command());
    }

    @Test
    public void commandWithoutExecutableIsUnchanged() throws Exception {
        Resolution r = resolve(props("s.command", "s,--lang,smt2"), "s", null, known());
        Assert.assertArrayEquals(new String[]{"s", "--lang", "smt2"}, r.command());
        Assert.assertNull(r.executable());
    }

    @Test
    public void configuredExecutable() {
        Properties p = props("s.exec.linux", "s-linux", "s.exec", "s-plain", "b.exec", " ");
        Assert.assertEquals("s-linux", SolverResolver.configuredExecutable(p, "s", "linux"));
        Assert.assertEquals("s-plain", SolverResolver.configuredExecutable(p, "s", "macos"));
        Assert.assertNull(SolverResolver.configuredExecutable(p, "b", "linux"));
        Assert.assertNull(SolverResolver.configuredExecutable(null, "s", "linux"));
    }
}
