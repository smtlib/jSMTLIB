/*
 * This file is part of the SMT project.
 * Copyright 2026 David R. Cok
 */
package org.smtlib;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.IParameterizedIdentifier;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.SMT.Configuration.SMTLIB;

/** The signatures of the bit-vector and floating-point functions and indexed constants. The theory
 *  files declare these only in prose, so they are tabulated here; TypeChecker applies them (#218). */
final class TheorySignatures {

    private TheorySignatures() {}

    /** The theories a signature needs */
    enum Theories {
        BV, FP, BV_INTS, FP_BV;

        boolean loaded(SymbolTable st) {
            return switch (this) {
                case BV -> st.bitVectorTheorySet;
                case FP -> st.floatingPointTheorySet;
                case BV_INTS -> st.bitVectorTheorySet && (st.intsTheorySet || st.realsIntsTheorySet);
                case FP_BV -> st.floatingPointTheorySet && st.bitVectorTheorySet;
            };
        }
    }

    /** The sort an argument must have */
    enum Kind {
        BV("a BitVec sort"),
        BV1("the sort (_ BitVec 1)"),
        FP("a FloatingPoint sort"),
        RM("the RoundingMode sort"),
        INT("the Int sort"),
        FP_REAL_BV("a FloatingPoint, Real, or BitVec sort");

        final String description;

        Kind(String description) { this.description = description; }
    }

    /** How the result sort is found */
    enum Result { SAME, BOOL, INT, REAL, BITVEC, FLOATINGPOINT }

    /** Computes the width of a BITVEC result, or {eb, sb} of a FLOATINGPOINT result, from the argument
     *  widths (-1 for an argument that is not a bit-vector) and the indices */
    @FunctionalInterface
    interface Widths {
        long[] of(int[] widths, int[] indices);
    }

    /** A violated constraint on the indices: at index {@code index}, at argument {@code arg} (whose
     *  required sort is {@code message}), or, if both are -1, at the whole identifier */
    record Problem(int index, int arg, String message) {
        static Problem atIndex(int i, String message) { return new Problem(i, -1, message); }
        static Problem atArg(int i, String sortDescription) { return new Problem(-1, i, sortDescription); }
        static Problem whole(String message) { return new Problem(-1, -1, message); }
    }

    /** A constraint on the indices, given the head symbol, the indices and the argument widths */
    @FunctionalInterface
    interface Check {
        /*@Nullable*/ Problem check(String head, int[] indices, int[] widths);
    }

    /** One signature: an application of one of {@code names} (or, if {@code constant}, an indexed
     *  constant) with {@code indices} numeral indices and arguments of {@code args} sorts (the last
     *  repeated if {@code nary}); if {@code same}, the bit-vector and floating-point arguments have one
     *  sort. Defined from SMT-LIB version {@code since}. */
    record Sig(Set<String> names, SMTLIB since, Theories theories, boolean constant, int indices,
            Kind[] args, boolean nary, boolean same, /*@Nullable*/ Check check,
            Result result, /*@Nullable*/ Widths widths) {

        /** Whether an application to n arguments has this signature's arity */
        boolean fits(int n) { return nary ? n >= args.length : n == args.length; }

        Kind kind(int i) { return args[Math.min(i, args.length - 1)]; }

        Sig since(SMTLIB v) { return new Sig(names, v, theories, constant, indices, args, nary, same, check, result, widths); }
        Sig indexed(int n) { return new Sig(names, since, theories, constant, n, args, nary, same, check, result, widths); }
        /** :left-assoc (bit-vectors) or :chainable (floating-point): two or more arguments, all of one sort */
        Sig leftAssoc() { return new Sig(names, since, theories, constant, indices, args, true, true, check, result, widths); }
        Sig chainable() { return leftAssoc(); }
        Sig sameSorts() { return new Sig(names, since, theories, constant, indices, args, nary, true, check, result, widths); }
        Sig check(Check c) { return new Sig(names, since, theories, constant, indices, args, nary, same, c, result, widths); }
        Sig returns(Result r) { return new Sig(names, since, theories, constant, indices, args, nary, same, check, r, widths); }
        Sig returnsBitVec(Widths w) { return new Sig(names, since, theories, constant, indices, args, nary, same, check, Result.BITVEC, w); }
        Sig returnsFloatingPoint(Widths w) { return new Sig(names, since, theories, constant, indices, args, nary, same, check, Result.FLOATINGPOINT, w); }
    }

    private static Sig fn(Set<String> names, Theories theories, Kind... args) {
        return new Sig(names, SMTLIB.V20, theories, false, 0, args, false, false, null, Result.SAME, null);
    }

    private static Sig constant(Set<String> names, Theories theories, int indices) {
        return new Sig(names, SMTLIB.V20, theories, true, indices, new Kind[0], false, false, null, Result.SAME, null);
    }

    /** The name under which (_ bvN m) is tabulated */
    private static final String BV_CONSTANT = "bv<N>";

    /** For an identifier whose result is a bit-vector of a width that is 0 if its first index is 0 */
    private static final Check NONZERO_WIDTH = (head, ix, w) -> ix[0] > 0 ? null : zeroWidth(head, ix);

    private static Problem zeroWidth(String head, int[] ix) {
        StringBuilder id = new StringBuilder("(_ ").append(head);
        for (int i : ix) id.append(' ').append(i);
        return Problem.atIndex(0, id.append(") would have the sort (_ BitVec 0), but a bit-vector sort must have")
                .append(" a length of at least 1").toString());
    }

    private static final Widths FROM_INDICES = (w, ix) -> new long[]{ ix[0], ix[1] };

    private static final List<Sig> SIGNATURES = List.of(
        // FixedSizeBitVectors theory and the QF_BV logic
        fn(Set.of("bvnot", "bvneg"), Theories.BV, Kind.BV),
        fn(Set.of("bvand", "bvor", "bvadd", "bvmul", "bvxor"), Theories.BV, Kind.BV, Kind.BV).leftAssoc(),
        fn(Set.of("bvudiv", "bvurem", "bvshl", "bvlshr", "bvnand", "bvnor", "bvxnor", "bvsub",
                "bvsdiv", "bvsrem", "bvsmod", "bvashr"), Theories.BV, Kind.BV, Kind.BV).sameSorts(),
        fn(Set.of("bvcomp"), Theories.BV, Kind.BV, Kind.BV).sameSorts().returnsBitVec((w, ix) -> new long[]{ 1 }),
        fn(Set.of("bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge"),
                Theories.BV, Kind.BV, Kind.BV).sameSorts().returns(Result.BOOL),
        fn(Set.of("bvuaddo", "bvsaddo", "bvumulo", "bvsmulo", "bvusubo", "bvssubo", "bvsdivo"),
                Theories.BV, Kind.BV, Kind.BV).sameSorts().returns(Result.BOOL).since(SMTLIB.V27),
        fn(Set.of("bvnego"), Theories.BV, Kind.BV).returns(Result.BOOL).since(SMTLIB.V27),
        fn(Set.of("concat"), Theories.BV, Kind.BV, Kind.BV).returnsBitVec((w, ix) -> new long[]{ (long)w[0] + w[1] }),
        fn(Set.of("ubv_to_int", "sbv_to_int"), Theories.BV_INTS, Kind.BV).returns(Result.INT).since(SMTLIB.V27),
        fn(Set.of("extract"), Theories.BV, Kind.BV).indexed(2)
                .check((head, ix, w) -> ix[0] < ix[1] ? Problem.atIndex(1, "The end index is less than the starting index")
                        : ix[0] >= w[0] ? Problem.atIndex(1, "The end index must be less than the length of the argument sort: "
                                + ix[0] + " vs. " + w[0])
                        : null)
                .returnsBitVec((w, ix) -> new long[]{ ix[0] - ix[1] + 1 }),
        fn(Set.of("int_to_bv"), Theories.BV_INTS, Kind.INT).indexed(1).check(NONZERO_WIDTH)
                .returnsBitVec((w, ix) -> new long[]{ ix[0] }).since(SMTLIB.V27),
        fn(Set.of("repeat"), Theories.BV, Kind.BV).indexed(1).check(NONZERO_WIDTH)
                .returnsBitVec((w, ix) -> new long[]{ (long)ix[0] * w[0] }),
        fn(Set.of("zero_extend", "sign_extend"), Theories.BV, Kind.BV).indexed(1)
                .returnsBitVec((w, ix) -> new long[]{ (long)w[0] + ix[0] }),
        fn(Set.of("rotate_left", "rotate_right"), Theories.BV, Kind.BV).indexed(1),
        constant(Set.of(BV_CONSTANT), Theories.BV, 1)
                .check((head, ix, w) -> ix[0] < 1 ? zeroWidth(head, ix)
                        : new java.math.BigInteger(head.substring(2)).bitLength() > ix[0]
                        ? Problem.whole("The value of the bitvector constant is too large for the given size ("
                                + new java.math.BigInteger(head.substring(2)).bitLength() + " vs. " + ix[0] + " bits)")
                        : null)
                .returnsBitVec((w, ix) -> new long[]{ ix[0] }),

        // FloatingPoint theory
        fn(Set.of("fp"), Theories.FP, Kind.BV1, Kind.BV, Kind.BV)
                .returnsFloatingPoint((w, ix) -> new long[]{ w[1], (long)w[2] + 1 }),
        fn(Set.of("fp.sqrt", "fp.roundToIntegral"), Theories.FP, Kind.RM, Kind.FP),
        fn(Set.of("fp.add", "fp.sub", "fp.mul", "fp.div"), Theories.FP, Kind.RM, Kind.FP, Kind.FP).sameSorts(),
        fn(Set.of("fp.fma"), Theories.FP, Kind.RM, Kind.FP, Kind.FP, Kind.FP).sameSorts(),
        fn(Set.of("fp.abs", "fp.neg"), Theories.FP, Kind.FP),
        fn(Set.of("fp.rem", "fp.min", "fp.max"), Theories.FP, Kind.FP, Kind.FP).sameSorts(),
        fn(Set.of("fp.leq", "fp.lt", "fp.geq", "fp.gt", "fp.eq"), Theories.FP, Kind.FP, Kind.FP).chainable().returns(Result.BOOL),
        fn(Set.of("fp.isNormal", "fp.isSubnormal", "fp.isZero", "fp.isInfinite", "fp.isNaN", "fp.isNegative",
                "fp.isPositive"), Theories.FP, Kind.FP).returns(Result.BOOL),
        fn(Set.of("fp.to_real"), Theories.FP, Kind.FP).returns(Result.REAL),
        fn(Set.of("fp.to_ubv", "fp.to_sbv"), Theories.FP_BV, Kind.RM, Kind.FP).indexed(1).check(NONZERO_WIDTH)
                .returnsBitVec((w, ix) -> new long[]{ ix[0] }),
        fn(Set.of("to_fp_unsigned"), Theories.FP_BV, Kind.RM, Kind.BV).indexed(2).returnsFloatingPoint(FROM_INDICES),
        fn(Set.of("to_fp"), Theories.FP, Kind.BV).indexed(2)
                .check((head, ix, w) -> w[0] == ix[0] + ix[1] ? null : Problem.atArg(0, "the sort (_ BitVec " + (ix[0] + ix[1]) + ")"))
                .returnsFloatingPoint(FROM_INDICES),
        fn(Set.of("to_fp"), Theories.FP, Kind.RM, Kind.FP_REAL_BV).indexed(2).returnsFloatingPoint(FROM_INDICES),
        constant(Set.of("+oo", "-oo", "+zero", "-zero", "NaN"), Theories.FP, 2).returnsFloatingPoint(FROM_INDICES)
    );

    private static final Map<String, List<Sig>> BY_NAME = new HashMap<>();
    static {
        for (Sig s : SIGNATURES) {
            for (String n : s.names()) BY_NAME.computeIfAbsent(n, k -> new ArrayList<>()).add(s);
        }
    }

    /** The signatures, among those whose theories are loaded, of an application of head (if
     *  constant is false) or of head as an indexed constant (if true); null if there are none */
    static /*@Nullable*/ List<Sig> lookup(IIdentifier head, boolean constant, SymbolTable symTable) {
        String name;
        if (head instanceof ISymbol s) name = s.value();
        else if (head instanceof IParameterizedIdentifier p) name = p.head().value();
        else return null;
        boolean indexed = head instanceof IParameterizedIdentifier;
        if (indexed && name.matches("bv(0|[1-9][0-9]*)")) name = BV_CONSTANT;
        List<Sig> sigs = BY_NAME.get(name);
        if (sigs == null) return null;
        List<Sig> found = new ArrayList<>();
        for (Sig s : sigs) {
            if (s.constant() == constant && (s.indices() > 0) == indexed && s.theories().loaded(symTable)) found.add(s);
        }
        return found.isEmpty() ? null : found;
    }

    private static final String[] COUNTS = { "no", "one", "two", "three", "four" };

    /** The argument counts of sigs, in words, for an error message: "one or two arguments" */
    static String arities(List<Sig> sigs) {
        Sig first = sigs.get(0);
        if (first.nary()) return "at least " + COUNTS[first.args().length] + " arguments";
        StringBuilder sb = new StringBuilder();
        int last = 0;
        for (Sig s : sigs) {
            if (sb.length() > 0) sb.append(" or ");
            last = s.args().length;
            sb.append(COUNTS[last]);
        }
        return sb.append(last == 1 ? " argument" : " arguments").toString();
    }
}
