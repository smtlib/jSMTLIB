/*
 * This file is part of the SMT project.
 * Copyright 2026 David R. Cok
 */
package org.smtlib;

import java.util.Properties;

/** Whether a solver supports a capability, as recorded per solver name in jsmtlib.properties (#157):
 *  {@code org.smtlib.solver_<name>.capabilities=strings,-proofs,...} -- a name records a supported
 *  capability, a {@code -}name an unsupported one. A capability the solver's entry does not mention
 *  (or every capability, if it has no entry) is taken from its family's entry, the family being the
 *  name before the first {@code -<digit>} ({@code z3-4.12.6} uses {@code z3}). A capability neither
 *  records is {@link Support#UNKNOWN}. */
public final class SolverCapabilities {

    private SolverCapabilities() {}

    /** The capabilities that can be queried; {@link #token} is the name used in the properties */
    public enum Capability {
        STRINGS("strings"),
        FLOATING_POINT("floating-point"),
        DATATYPES("datatypes"),
        PROOFS("proofs");

        public final String token;

        Capability(String token) {
            this.token = token;
        }

        /** The capability whose token or enum name is the given name, ignoring case; null if none */
        public static /*@Nullable*/ Capability lookup(String name) {
            for (Capability c : values()) {
                if (c.token.equalsIgnoreCase(name) || c.name().equalsIgnoreCase(name)) return c;
            }
            return null;
        }
    }

    /** The answer to a query; UNKNOWN means the solver's entry does not record the capability */
    public enum Support { YES, NO, UNKNOWN }

    /** The suffix of the property that lists a solver's capabilities */
    public static final String PROPS_CAPABILITIES_SUFFIX = ".capabilities";

    private static /*@Nullable*/ Properties defaultProps;

    /** The merged jsmtlib.properties, read once, on first use */
    private static synchronized Properties defaultProperties() {
        if (defaultProps == null) defaultProps = new SMT.Configuration().readProperties();
        return defaultProps;
    }

    /** Whether the solver supports the capability, according to the merged jsmtlib.properties
     * @throws IllegalArgumentException if the solver's entry has an unknown or contradictory token */
    public static Support supports(String solvername, Capability capability) {
        return supports(defaultProperties(), solvername, capability);
    }

    /** As {@link #supports(String, Capability)}, with the capability given by its token or enum name
     * @throws IllegalArgumentException if there is no such capability */
    public static Support supports(String solvername, String capability) {
        Capability c = Capability.lookup(capability);
        if (c == null) throw new IllegalArgumentException("No such solver capability: " + capability);
        return supports(solvername, c);
    }

    /** Whether the solver supports the capability, according to the given properties
     * @throws IllegalArgumentException if the solver's entry has an unknown or contradictory token */
    public static Support supports(Properties props, String solvername, Capability capability) {
        Support result = recorded(props, solvername, capability);
        String family = family(solvername);
        if (result == Support.UNKNOWN && family != null) result = recorded(props, family, capability);
        return result;
    }

    /** What the solver's own entry records for the capability; UNKNOWN if there is no entry or it
     *  does not mention the capability */
    private static Support recorded(Properties props, String solvername, Capability capability) {
        String propName = Utils.PROPS_SOLVER_PREFIX + solvername + PROPS_CAPABILITIES_SUFFIX;
        String entry = props.getProperty(propName);
        if (entry == null) return Support.UNKNOWN;
        Support result = Support.UNKNOWN;
        for (String token : entry.split(",")) {
            token = token.trim();
            if (token.isEmpty()) continue;
            boolean negated = token.startsWith("-");
            String name = negated ? token.substring(1) : token;
            Capability c = Capability.lookup(name);
            if (c == null) throw new IllegalArgumentException("Unknown capability '" + name + "' in " + propName);
            if (c != capability) continue;
            Support s = negated ? Support.NO : Support.YES;
            if (result != Support.UNKNOWN && result != s) {
                throw new IllegalArgumentException("Capability '" + name + "' is both supported and unsupported in " + propName);
            }
            result = s;
        }
        return result;
    }

    /** The family name: the solver name before the first '-' followed by a digit; null if there is none */
    public static /*@Nullable*/ String family(String solvername) {
        for (int i = 0; i + 1 < solvername.length(); i++) {
            if (solvername.charAt(i) == '-' && Character.isDigit(solvername.charAt(i + 1))) {
                return i == 0 ? null : solvername.substring(0, i);
            }
        }
        return null;
    }
}
