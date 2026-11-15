package org.smtlib.test;

import java.io.File;
import java.net.JarURLConnection;
import java.net.URL;
import java.util.Enumeration;
import java.util.Properties;
import java.util.Set;
import java.util.TreeSet;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

import org.junit.Assert;
import org.junit.Test;
import org.smtlib.SMT;
import org.smtlib.SolverResolver;

/** The solvers configured in jsmtlib.properties and the adapter each resolves to (#194 item 1).
 *  {@link #SOLVERS} is the one hand-kept list of them; these tests fail when it, the properties
 *  and the adapter classes disagree, so a new solver entry or adapter cannot be left out of it. */
public class BuiltInSolversTests {

    /** Each configured solver name, its adapter (simple class name), and its Windows adapter if that differs */
    static final String[][] SOLVERS = {
        {"z3", "Solver_z3_recent"},
        {"z3-4.3", "Solver_z3_4_3", "Solver_z3_4_3_2"},
        {"z3-4.3.1", "Solver_z3_4_3"},
        {"z3-4.5.0", "Solver_z3_4_5"},
        {"z3-4.6.0", "Solver_z3_recent"},
        {"z3-4.7.1", "Solver_z3_recent"},
        {"z3-4.8.12", "Solver_z3_recent"},
        {"z3-4.10.2", "Solver_z3_recent"},
        {"z3-4.12.6", "Solver_z3_recent"},
        {"z3-4.14.1", "Solver_z3_recent"},
        {"z3-4.16.0", "Solver_z3_recent"},
        {"cvc5", "Solver_cvc5"},
        {"cvc5-1.3.2", "Solver_cvc5"},
        {"yices2", "Solver_yices2", "Solver_yices2_2_6"},
        {"yices2-2.6.5", "Solver_yices2_2_6"},
        {"yices2-2.7.0", "Solver_yices2"},
        {"smtinterpol", "Solver_smtinterpol"},
        {"smtinterpol-2.5", "Solver_smtinterpol"},
        {"bitwuzla", "Solver_bitwuzla"},
        {"simplify", "Solver_simplify"},
        {"altergo", "Solver_altergo"},
    };

    /** Names configured in jsmtlib.properties that are not solvers: a script test's always-missing executable */
    private static final Set<String> NOT_SOLVERS = Set.of("missingexec");

    /** Adapters no configured name resolves to: the test pseudo-solver's, and the one for an unconfigured name */
    private static final String[][] OTHER_ADAPTERS = { {"test", "Solver_test"}, {"no-such-solver", "Solver_smt"} };

    private static final String[] PLATFORMS = { "macos", "linux", "windows" };

    private static final String PREFIX = "org.smtlib.solver_";

    private static final Set<String> SUFFIXES = Set.of("exec", "adapter", "command", "capabilities");

    /** The configured solver names */
    static String[] names() {
        String[] n = new String[SOLVERS.length];
        for (int i = 0; i < n.length; i++) n[i] = SOLVERS[i][0];
        return n;
    }

    private static Properties props() {
        return new SMT.Configuration().readProperties();
    }

    /** The names that jsmtlib.properties configures: a key is PREFIX + name + "." + suffix [+ "." + platform] */
    private static Set<String> configuredNames(Properties p) {
        Set<String> names = new TreeSet<>();
        for (String key: p.stringPropertyNames()) {
            if (!key.startsWith(PREFIX)) continue;
            String[] parts = key.substring(PREFIX.length()).split("\\.");
            int s = 1;
            while (s < parts.length && !SUFFIXES.contains(parts[s])) s++;
            Assert.assertTrue("unknown kind of solver property: " + key, s < parts.length);
            names.add(String.join(".", java.util.Arrays.copyOf(parts, s)));
        }
        names.removeAll(NOT_SOLVERS);
        return names;
    }

    /** The adapter classes in org.smtlib.solvers (simple names), read from the jar or directory holding them */
    static Set<String> adapterClasses() throws Exception {
        Class<?> anchor = org.smtlib.solvers.Solver_smt.class;
        URL url = anchor.getResource(anchor.getSimpleName() + ".class");
        Set<String> names = new TreeSet<>();
        if (url.getProtocol().equals("jar")) {
            JarURLConnection c = (JarURLConnection)url.openConnection();
            c.setUseCaches(false);
            try (JarFile jar = c.getJarFile()) {
                for (Enumeration<JarEntry> e = jar.entries(); e.hasMoreElements(); ) {
                    String n = e.nextElement().getName();
                    if (n.startsWith("org/smtlib/solvers/")) addAdapter(names, n.substring(n.lastIndexOf('/') + 1));
                }
            }
        } else {
            File[] files = new File(url.toURI()).getParentFile().listFiles();
            for (File f: files) addAdapter(names, f.getName());
        }
        Assert.assertTrue("no adapter classes found at " + url, names.contains(anchor.getSimpleName()));
        return names;
    }

    private static void addAdapter(Set<String> names, String file) {
        if (file.matches("Solver_\\w+\\.class")) names.add(file.substring(0, file.length() - ".class".length()));
    }

    @Test
    public void tableListsEveryConfiguredSolver() {
        Set<String> listed = new TreeSet<>(java.util.Arrays.asList(names()));
        Assert.assertEquals("SOLVERS vs the names configured in jsmtlib.properties", configuredNames(props()), listed);
    }

    @Test
    public void eachSolverResolvesToItsAdapter() throws Exception {
        Properties p = props();
        for (String[] s: SOLVERS) {
            for (String platform: PLATFORMS) {
                String expected = platform.equals("windows") && s.length > 2 ? s[2] : s[1];
                Assert.assertEquals(s[0] + " on " + platform, "org.smtlib.solvers." + expected,
                        SolverResolver.resolve(p, s[0], null, platform, null, SolverResolver::forName).adapterClassName());
            }
        }
        for (String[] s: OTHER_ADAPTERS) {
            Assert.assertEquals(s[0], "org.smtlib.solvers." + s[1],
                    SolverResolver.resolve(p, s[0], null, "linux", null, SolverResolver::forName).adapterClassName());
        }
    }

    @Test
    public void everyAdapterIsReached() throws Exception {
        Set<String> reached = new TreeSet<>();
        for (String[] s: SOLVERS) {
            for (int i = 1; i < s.length; i++) reached.add(s[i]);
        }
        for (String[] s: OTHER_ADAPTERS) reached.add(s[1]);
        Assert.assertEquals("adapter classes vs those SOLVERS and OTHER_ADAPTERS resolve to", adapterClasses(), reached);
    }
}
