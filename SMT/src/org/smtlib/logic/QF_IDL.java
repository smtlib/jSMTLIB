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

/** QF_IDL atoms (QF_IDL.smt2): (op x y), (op (- x y) n) and (op (- x y) (- n)), with x, y
 *  free constants of sort Int and n a numeral. */
public class QF_IDL extends DifferenceLogic {

    public QF_IDL(SMT.Configuration smtConfig, ISymbol name, Collection<IAttribute<?>> attributes) {
        super(smtConfig,name,attributes);
    }

    @Override
    protected String kind() { return "IDL"; }

    @Override
    protected void checkAtom(IExpr.IFcnExpr e, IExpr lhs, IExpr rhs) throws IVisitor.VisitorException {
        if (lhs instanceof ISymbol) {
            if (rhs instanceof ISymbol) return;
            throw restrictionError("rhs must be a symbol if the lhs is a symbol", e);
        }
        if (!(lhs instanceof IExpr.IFcnExpr) || !Utils.MINUS.equals(((IExpr.IFcnExpr)lhs).head())) {
            throw restrictionError("lhs must be a symbol or a difference", e);
        }
        if (!isDifferenceOfSymbols(lhs)) {
            throw restrictionError("differences must be difference of symbols", e);
        }
        if (rhs instanceof INumeral) return;
        if (!(rhs instanceof IExpr.IFcnExpr)) {
            throw restrictionError("The rhs must be an integer", e);
        }
        if (!isInteger(rhs)) {
            throw restrictionError("The rhs must be a numeral or negation of numeral", e);
        }
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
