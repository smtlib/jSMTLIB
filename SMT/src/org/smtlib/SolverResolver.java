/*
 * This file is part of the SMT project.
 * Copyright 2026 David R. Cok
 */
package org.smtlib;

import java.util.Properties;
import java.util.function.Function;

/** For internal use only (public so that the tests can reach it); not part of the API.
 *  Resolves a solver name, from the merged jsmtlib.properties, to the adapter class and the
 *  executable or command that {@link SMT.Configuration#createSolver} constructs it with (#123).
 *  The platform, solver directory and class lookup are passed in, so that the rules can be
 *  tested with no solver installed. */
public final class SolverResolver {

    private SolverResolver() {}

    /** The result of {@link #resolve}: the adapter class (and its name, for messages), and the
     *  executable, or the command array if the properties give one */
    public record Resolution(String solvername, Class<?> adapterClass, String adapterClassName,
            /*@Nullable*/ String executable, /*@Nullable*/ String[] command) {}

    /** {@link Class#forName(String)}, or null if there is no such class: the production class lookup */
    public static /*@Nullable*/ Class<?> forName(String name) {
        try {
            return Class.forName(name);
        } catch (ClassNotFoundException e) {
            return null;
        }
    }

    /** Resolves the solver:
     *  <ol>
     *  <li>the adapter: a {@code .adapter.<platform>} property, then {@code .adapter}; else the class
     *      {@code Solver_<name>} (with - and . in the name as _); else, for a z3 name,
     *      {@code Solver_z3_recent}; else {@code Solver_smt};</li>
     *  <li>a {@code .command} property, split at commas, if given;</li>
     *  <li>the executable: the one given, else {@code .exec.<platform>}, then {@code .exec}; resolved by
     *      {@link SMT#resolveExecutablePath}, and put in the command in place of {@code %exec%}, or as
     *      its first element if there is no {@code %exec%}; with neither a command nor an executable,
     *      the solver name itself, resolved the same way.</li>
     *  </ol>
     *  The {@code test} pseudo-solver is {@code Solver_test}, with the executable as given.
     * @param props the merged properties, or null for none
     * @param solvername the name of the solver
     * @param executable the caller's executable, or null to resolve one
     * @param platform the platform name, as {@code SMT.platformName()} gives it
     * @param solverDir the solver directory (SMT_SOLVER_DIR), or null
     * @param classLookup the class with a given name, or null if there is none
     * @throws ISolver.CreationException if the {@code .command} property has no content */
    public static Resolution resolve(/*@Nullable*/ Properties props, String solvername, /*@Nullable*/ String executable,
            String platform, /*@Nullable*/ String solverDir, Function<String, Class<?>> classLookup)
            throws ISolver.CreationException {
        if (solvername.equals(Utils.TEST_SOLVER)) {
            return new Resolution(solvername, org.smtlib.solvers.Solver_test.class,
                    org.smtlib.solvers.Solver_test.class.getName(), executable, null);
        }
        Class<?> adapterClass = null;
        String adapterClassName = null;

        // A platform-specific override (.adapter.<platform>) is checked before the bare
        // .adapter, for solvers whose behavior genuinely differs by platform (not just
        // their executable's filename) -- e.g. the Windows z3-4.3.2 binary has its own
        // push-command bug that the Unix/macOS z3-4.3.1 binary doesn't, needing its own
        // adapter subclass. Mirrors the same convention used for .exec.<platform>.
        if (props != null) {
            adapterClassName = props.getProperty(Utils.PROPS_SOLVER_PREFIX + solvername + Utils.PROPS_ADAPTER_SUFFIX + "." + platform);
            if (adapterClassName == null) {
                adapterClassName = props.getProperty(Utils.PROPS_SOLVER_PREFIX + solvername + Utils.PROPS_ADAPTER_SUFFIX);
            }
            if (adapterClassName != null) adapterClass = classLookup.apply(adapterClassName);
        }

        if (adapterClass == null) {
            adapterClassName = "org.smtlib.solvers.Solver_" + solvername.replace('-','_').replace('.', '_');
            adapterClass = classLookup.apply(adapterClassName);
        }

        // No Solver_z3 class exists (see the matching comment in jsmtlib.properties),
        // so a z3 solver name with neither a configured .adapter property nor a
        // version-specific adapter class of its own (e.g. an untested/future z3
        // version) would otherwise fall through to the fully generic Solver_smt below,
        // losing z3-specific handling that any current z3 build still needs. Default
        // such names to Solver_z3_recent instead.
        if (adapterClass == null && solvername.startsWith("z3")) {
            adapterClassName = "org.smtlib.solvers.Solver_z3_recent";
            adapterClass = classLookup.apply(adapterClassName);
        }

        // But otherwise presume the solver is a standard smt solver
        if (adapterClass == null) {
            adapterClass = org.smtlib.solvers.Solver_smt.class;
            adapterClassName = "org.smtlib.solvers.Solver_smt";
        }

        String[] command = null;
        String propName = Utils.PROPS_SOLVER_PREFIX + solvername + Utils.PROPS_COMMAND_SUFFIX;
        String commandString = props == null ? null : props.getProperty(propName);
        if (commandString != null && !commandString.isEmpty()) {
            command = commandString.split(",");
            if (command.length == 0) {
                throw new ISolver.CreationException("The command specified for " + propName + " appears to have no content");
            }
        }

        if (executable == null) executable = configuredExecutable(props, solvername, platform);
        if (executable != null) executable = SMT.resolveExecutablePath(executable, solverDir);

        if (command != null && executable != null) {
            // %exec% lets a .command entry place the resolved executable at any
            // position, not just the front -- needed for launchers like
            // "java,-jar,%exec%,-q" where the resolvable path isn't argv[0].
            // If no placeholder appears, fall back to substituting argv[0], so a
            // plain "EXE,arg1,arg2"-style command (executable genuinely first)
            // still works without needing the placeholder spelled out.
            boolean substituted = false;
            for (int i = 0; i < command.length; i++) {
                if (command[i].equals("%exec%")) {
                    command[i] = executable;
                    substituted = true;
                }
            }
            if (!substituted) command[0] = executable;
        }

        if (executable == null && command == null) {
            // No jsmtlib.properties entry for this solver name at all: default to
            // treating the solver name itself as the executable, resolved against
            // SMT_SOLVER_DIR like any configured .exec value would be. This lets a
            // solver be used just by name (e.g. --solver cvc5-1.3.2) without requiring
            // a properties entry.
            executable = SMT.resolveExecutablePath(solvername, solverDir);
        }
        return new Resolution(solvername, adapterClass, adapterClassName, executable, command);
    }

    /** The executable the properties configure for the solver: {@code .exec.<platform>}, then
     *  {@code .exec}; null if neither is given, or it is blank. A platform-specific override is
     *  for solvers whose executable filename itself differs by platform (e.g. z3-4.3 ships as
     *  z3-4.3.1 on Unix/macOS but z3-4.3.2 on Windows). Not resolved to a path. */
    public static /*@Nullable*/ String configuredExecutable(/*@Nullable*/ Properties props, String solvername, String platform) {
        if (props == null) return null;
        String executable = props.getProperty(Utils.PROPS_SOLVER_PREFIX + solvername + Utils.PROPS_EXEC_SUFFIX + "." + platform);
        if (executable == null) {
            executable = props.getProperty(Utils.PROPS_SOLVER_PREFIX + solvername + Utils.PROPS_EXEC_SUFFIX);
        }
        if (executable != null && executable.trim().isEmpty()) executable = null;
        return executable;
    }
}
