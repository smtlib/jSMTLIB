package org.smtlib.logic;

import org.smtlib.SMT;

import java.util.Collection;
import java.util.List;

import org.smtlib.IExpr;
import org.smtlib.ISort;
import org.smtlib.IVisitor;
import org.smtlib.Utils;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.ISymbol;

/** QF_RDL atoms (QF_RDL.smt2): (op x y), (op (- x y) c), (op (- (+ x ... x) (+ y ... y)) c)
 *  with k &gt; 1 occurrences each of x and y, and the extension (op (- x y) (/ c n)); x, y are
 *  free constants of sort Real, c is m or (- m), and m, n are numerals with n nonzero. Being real
 *  difference logic, c may also be a decimal d or (- d). */
public class QF_RDL extends DifferenceLogic {

    public QF_RDL(SMT.Configuration smtConfig, ISymbol name, Collection<IAttribute<?>> attributes) {
        super(smtConfig,name,attributes);
    }

    @Override
    protected String kind() { return "RDL"; }

    @Override
    protected void checkAtom(IExpr.IFcnExpr e, IExpr lhs, IExpr rhs) throws IVisitor.VisitorException {
        if (lhs instanceof ISymbol) {
            if (rhs instanceof ISymbol) return;
            throw restrictionError("rhs must be a symbol if the lhs is a symbol", e);
        }
        if (!(lhs instanceof IExpr.IFcnExpr) || !Utils.MINUS.equals(((IExpr.IFcnExpr)lhs).head())) {
            throw restrictionError("lhs must be a symbol or a difference", e);
        }
        if (isDifferenceOfSymbols(lhs)) {
            if (isConstant(rhs) || isQuotient(rhs)) return;
            throw restrictionError("The rhs must be a numeral or decimal, its negation, or (/ c n) with n a nonzero numeral", e);
        }
        if (!isDifferenceOfRepeatedSums((IExpr.IFcnExpr)lhs)) {
            throw restrictionError("differences must be difference of symbols", e);
        }
        if (!isConstant(rhs)) {
            throw restrictionError("The rhs must be a numeral or decimal, or its negation", e);
        }
    }

    /** True for a numeral or decimal, or its negation */
    private boolean isConstant(IExpr e) {
        if (isInteger(e) || e instanceof IExpr.IDecimal) return true;
        if (!(e instanceof IExpr.IFcnExpr)) return false;
        IExpr.IFcnExpr f = (IExpr.IFcnExpr) e;
        return Utils.MINUS.equals(f.head()) && f.args().size() == 1 && f.args().get(0) instanceof IExpr.IDecimal;
    }

    /** True for (/ c n) with c a numeral or negated numeral and n a nonzero numeral */
    private boolean isQuotient(IExpr e) {
        if (!(e instanceof IExpr.IFcnExpr)) return false;
        IExpr.IFcnExpr f = (IExpr.IFcnExpr) e;
        return Utils.SLASH.equals(f.head()) && f.args().size() == 2 && isInteger(f.args().get(0))
                && f.args().get(1) instanceof INumeral && ((INumeral)f.args().get(1)).value().signum() != 0;
    }

    /** True for (- (+ x ... x) (+ y ... y)), each sum having the same number (more than one) of a single symbol */
    private static boolean isDifferenceOfRepeatedSums(IExpr.IFcnExpr diff) {
        if (diff.args().size() != 2) return false;
        int k = repeatedSumLength(diff.args().get(0));
        return k > 1 && k == repeatedSumLength(diff.args().get(1));
    }

    /** The number of terms in (+ x ... x) for a single symbol x, or 0 if e has another form */
    private static int repeatedSumLength(IExpr e) {
        if (!(e instanceof IExpr.IFcnExpr)) return 0;
        IExpr.IFcnExpr f = (IExpr.IFcnExpr) e;
        if (!Utils.PLUS.equals(f.head())) return 0;
        IExpr first = f.args().get(0);
        if (!(first instanceof ISymbol)) return 0;
        for (IExpr a : f.args()) {
            if (!first.equals(a)) return 0;
        }
        return f.args().size();
    }

    @Override
    public void checkFcnDeclaration(IExpr.IIdentifier id, List<ISort> argSorts, ISort resultSort, /*@Nullable*/IExpr definition) throws IVisitor.VisitorException {
        noFunctions(id,argSorts,resultSort,definition);
    }

    @Override
    public void checkSortDeclaration(IIdentifier id, List<ISort.IParameter> params, ISort expr) throws IVisitor.VisitorException {
        noSorts(id,params,expr);
    }

}
