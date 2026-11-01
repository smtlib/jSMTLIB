package org.smtlib.logic;

import java.util.Collection;
import java.util.List;

import org.smtlib.*;
import org.smtlib.IExpr.*;
import org.smtlib.impl.SMTExpr;

/** Common base for this package's per-logic syntactic-restriction classes (QF_IDL, LRA,
 *  QF_UF, etc). Each subclass overrides {@link ILanguage#validExpression},
 *  {@link ILanguage#checkFcnDeclaration}, and {@link ILanguage#checkSortDeclaration} to
 *  reject whatever its own logic's SMT-LIB-mandated grammar forbids (quantifiers,
 *  uninterpreted functions, nonlinear arithmetic, unrestricted sorts, ...); this class
 *  supplies the shared helpers those overrides call (noQuantifiers, noFunctions, noSorts,
 *  checkArraySort, isLinearReal, ...).
 *  <p>
 *  Extends {@code SMTExpr.Logic} (the plain, unrestricted {@link ILogic} implementation
 *  {@code sexpr.Parser} falls back to when no subclass exists for a given logic name -- see
 *  issue #46) rather than depending only on the bare {@link ILogic} interface, so that a
 *  subclass which doesn't override one of the three hooks above still gets that hook's
 *  already-permissive default (an empty/no-op override) for free, instead of every subclass
 *  having to restate "permit everything" explicitly. */
public abstract class Logic extends SMTExpr.Logic implements ILanguage {

    public Logic(SMT.Configuration smtConfig, ISymbol name, Collection<IAttribute<?>> attributes) {
        super(smtConfig,name,attributes);
    }

    public void noQuantifiers(IExpr expression) throws IVisitor.VisitorException {
        IVisitor<Void> visitor = new IVisitor.TreeVisitor<Void>() {
            @Override
            public Void visit(IForall e) throws IVisitor.VisitorException {
                throw new IVisitor.VisitorException("A quantified expression is not allowed in the " + logicName + " logic",e.pos());
            }
            @Override
            public Void visit(IExists e) throws IVisitor.VisitorException {
                throw new IVisitor.VisitorException("A quantified expression is not allowed in the " + logicName + " logic",e.pos());
            }
        };
        expression.accept(visitor);
    }

    public void noExponentiation(IExpr expression) throws IVisitor.VisitorException {
        IVisitor<Void> visitor = new IVisitor.TreeVisitor<Void>() {
            @Override
            public Void visit(IExpr.IFcnExpr e) throws IVisitor.VisitorException {
                if (Utils.EXP.equals(e.head()))
                    throw new IVisitor.VisitorException("The exponentiation operator ** is not allowed in the " + logicName + " logic", e.pos());
                return super.visit(e);
            }
        };
        expression.accept(visitor);
    }

    public void noFunctions(IExpr.IIdentifier id, List<ISort> argSorts, ISort resultSort, /*@Nullable*/IExpr definition) throws IVisitor.VisitorException {
        // May declare constants, but not functions without definitions
        if (argSorts.size() != 0 && definition == null) 
            throw new IVisitor.VisitorException("Declarations of uninterpreted functions are not allowed in this logic",id.pos());

    }

    public void noSorts(IIdentifier id, List<ISort.IParameter> params, ISort expr) throws IVisitor.VisitorException {
        if (expr == null) throw new IVisitor.VisitorException("New sorts are not allowed in this logic",id.pos());
    }

    /** Builds a VisitorException for a restriction violation (e.g. QF_IDL/QF_RDL's
     *  difference-logic shape, LRA's linearity check) whose message includes the offending
     *  expression's own printed text, not just an abstract description of the rule it
     *  broke -- several subclasses' checks used to throw the bare message alone, each with
     *  its own "// FIXME" noting the expression text was meant to be included but wasn't. */
    protected IVisitor.VisitorException restrictionError(String message, IExpr e) {
        return new IVisitor.VisitorException(message + ": " + smtConfig.defaultPrinter.toString(e), e.pos());
    }

    /** Creates the sort expression {@code name(params...)}, e.g. {@code sortApp("Array", intSort, intSort)}
     *  for {@code (Array Int Int)}. Used to build canonical sorts for structural comparison
     *  (via {@link ISort#equalsNoExpand}), rather than comparing printed text. */
    protected ISort sortApp(String name, ISort... params) {
        return smtConfig.sortFactory.createSortExpression(smtConfig.exprFactory.symbol(name), params);
    }

    /** The Array sorts this logic allows, as text for error messages, or null if it allows
     *  every Array sort. A logic restricting Array sorts overrides this and {@link #allowedArraySort}. */
    protected /*@Nullable*/ String allowedArraySorts() { return null; }

    /** Whether this logic allows the Array sort array, whose own sort is already expanded and
     *  which contains no sort parameter */
    protected boolean allowedArraySort(ISort.IApplication array) { return true; }

    /** Checks every Array sort within sort, expanding abbreviations, against {@link
     *  #allowedArraySort}. An Array sort containing a sort parameter is skipped: it is checked
     *  where the parameterized abbreviation is instantiated. */
    protected void checkArraySorts(ISort sort, IPos pos) throws IVisitor.VisitorException {
        if (allowedArraySorts() == null) return;
        ISort s = sort.expand();
        if (!(s instanceof ISort.IApplication)) return;
        ISort.IApplication app = (ISort.IApplication) s;
        if (Utils.ARRAY.equals(app.family().headSymbol()) && !hasSortParameter(app) && !allowedArraySort(app)) {
            throw new IVisitor.VisitorException("Array sorts must be " + allowedArraySorts() + " in this logic", pos);
        }
        for (ISort param : app.parameters()) {
            checkArraySorts(param, pos);
        }
    }

    /** Checks the Array sorts in a function's argument and result sorts */
    protected void checkArraySorts(List<ISort> argSorts, ISort resultSort, IIdentifier id) throws IVisitor.VisitorException {
        for (ISort s : argSorts) checkArraySorts(s, id.pos());
        checkArraySorts(resultSort, id.pos());
    }

    /** Checks the Array sorts of the variables bound by quantifiers in expression */
    protected void checkBoundArraySorts(IExpr expression) throws IVisitor.VisitorException {
        if (allowedArraySorts() == null) return;
        IVisitor<Void> visitor = new IVisitor.TreeVisitor<Void>() {
            @Override
            public Void visit(IForall e) throws IVisitor.VisitorException {
                for (IDeclaration d : e.parameters()) checkArraySorts(d.sort(), d.pos());
                return super.visit(e);
            }
            @Override
            public Void visit(IExists e) throws IVisitor.VisitorException {
                for (IDeclaration d : e.parameters()) checkArraySorts(d.sort(), d.pos());
                return super.visit(e);
            }
        };
        expression.accept(visitor);
    }

    private static boolean hasSortParameter(ISort sort) {
        if (sort instanceof ISort.IParameter) return true;
        if (!(sort instanceof ISort.IApplication)) return false;
        for (ISort p : ((ISort.IApplication) sort).parameters()) {
            if (hasSortParameter(p)) return true;
        }
        return false;
    }

    /** Whether sort, with abbreviations expanded, is structurally the same as allowed */
    protected static boolean sameSort(ISort sort, ISort allowed) {
        ISort s = sort.expand();
        if (!(s instanceof ISort.IApplication) || !(allowed instanceof ISort.IApplication)) return false;
        ISort.IApplication a = (ISort.IApplication) s;
        ISort.IApplication b = (ISort.IApplication) allowed;
        if (!a.family().equals(b.family()) || a.parameters().size() != b.parameters().size()) return false;
        for (int i = 0; i < a.parameters().size(); i++) {
            if (!sameSort(a.parameters().get(i), b.parameters().get(i))) return false;
        }
        return true;
    }

    /** Whether array is (Array (_ BitVec i) (_ BitVec j)), as QF_ABV and QF_AUFBV require */
    protected static boolean isBitVecArray(ISort.IApplication array) {
        List<ISort> params = array.parameters();
        return params.size() == 2 && isBitVecSort(params.get(0)) && isBitVecSort(params.get(1));
    }

    /** Whether sort, with abbreviations expanded, is a (_ BitVec n) sort */
    protected static boolean isBitVecSort(ISort sort) {
        ISort s = sort.expand();
        return (s instanceof ISort.IApplication) && Utils.BITVEC_SYM.equals(((ISort.IApplication) s).family().headSymbol());
    }


    public boolean isInteger(IExpr expr) {
        if (expr instanceof IExpr.INumeral) return true;
        if (!(expr instanceof IExpr.IFcnExpr)) return false;
        IExpr.IFcnExpr f = (IExpr.IFcnExpr)expr;
        if (Utils.MINUS.equals(f.head()) && f.args().size() == 1) {
            expr = f.args().get(0);
            if (expr instanceof IExpr.INumeral) return true;
            return false;
        }
        return false;
    }

    public boolean isFreeConstant(IExpr expr) {
        return (expr instanceof ISymbol);
//        if (!(expr instanceof IExpr.IFcnExpr)) return false;
//        IExpr.IFcnExpr f = (IExpr.IFcnExpr)expr;
//        return f.args().size() == 0;
    }

    /** The arguments of an application (of * or /) that are not coefficients. A product, of
     *  any arity, is linear when at most one of its factors is not a coefficient. */
    protected static List<IExpr> nonCoefficients(IExpr.IFcnExpr e, java.util.function.Predicate<IExpr> isCoefficient) {
        List<IExpr> result = new java.util.ArrayList<>();
        for (IExpr a : e.args()) {
            if (!isCoefficient.test(a)) result.add(a);
        }
        return result;
    }

    public boolean isLinearInteger(IExpr expr) {
        try {
            IVisitor<Void> visitor = new IVisitor.TreeVisitor<Void>() {
                @Override
                public Void visit(IExpr.IFcnExpr e) throws IVisitor.VisitorException {
                    IQualifiedIdentifier fcn = e.head();
                    if (Utils.MULT.equals(fcn)) {
                        List<IExpr> factors = nonCoefficients(e, Logic.this::isInteger);
                        if (factors.size() > 1 || (factors.size() == 1 && !isFreeConstant(factors.get(0))))
                            throw new IVisitor.VisitorException("nonlinear", null);
                        return null;
                    } else if (Utils.DIV.equals(fcn) || Utils.MOD.equals(fcn) || Utils.ABS.equals(fcn)) {
                        throw new IVisitor.VisitorException("nonlinear", null);
                    }
                    return super.visit(e);
                }
            };
            expr.accept(visitor);
            return true;
        } catch (IVisitor.VisitorException e) {
            return false;
        }
    }

    public boolean isLinearReal(IExpr expr) {
        try {
            IVisitor<Void> visitor = new IVisitor.TreeVisitor<Void>() {
                @Override
                public Void visit(IExpr.IFcnExpr e) throws IVisitor.VisitorException {
                    IQualifiedIdentifier fcn = e.head();
                    if (Utils.MULT.equals(fcn)) {
                        List<IExpr> factors = nonCoefficients(e, Logic.this::isRealConst);
                        if (factors.size() > 1 || (factors.size() == 1 && !isFreeConstant(factors.get(0))))
                            throw new IVisitor.VisitorException("nonlinear", null);
                        return null;
                    } else if (Utils.SLASH.equals(fcn)) {
                        if (!nonCoefficients(e, Logic.this::isRealConst).isEmpty())
                            throw new IVisitor.VisitorException("nonlinear", null);
                        return null;
                    }
                    return super.visit(e);
                }
            };
            expr.accept(visitor);
            return true;
        } catch (IVisitor.VisitorException e) {
            return false;
        }
    }

    public boolean isRealConst(IExpr expr) {
        if (expr instanceof IExpr.INumeral) return true;
        if (expr instanceof IExpr.IDecimal) return true;
        if (!(expr instanceof IExpr.IFcnExpr)) return false;
        IExpr.IFcnExpr f = (IExpr.IFcnExpr)expr;
        if (Utils.MINUS.equals(f.head()) && f.args().size() == 1) {
            return isRealConst(f.args().get(0));
        }
        if (Utils.SLASH.equals(f.head()) && f.args().size() == 2) {
            return isInteger(f.args().get(0)) && (f.args().get(1) instanceof IExpr.INumeral)
                && ((IExpr.INumeral)f.args().get(1)).intValue() != 0;
        }
        return false;
    }
}
