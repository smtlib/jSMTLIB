package org.smtlib.logic;

import org.smtlib.SMT;

import java.util.Collection;
import java.util.List;

import org.smtlib.IExpr;
import org.smtlib.ISort;
import org.smtlib.IVisitor;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.ISymbol;

public class QF_AUFLIA extends Logic {

    public QF_AUFLIA(SMT.Configuration smtConfig, ISymbol name, Collection<IAttribute<?>> attributes) {
        super(smtConfig,name,attributes);
    }

    public void checkFcnDeclaration(IExpr.IIdentifier id, List<ISort> argSorts, ISort resultSort, /*@Nullable*/IExpr definition) throws IVisitor.VisitorException {
        checkArraySorts(argSorts, resultSort, id);
    }

    public void validExpression(IExpr expression) throws IVisitor.VisitorException {
        noQuantifiers(expression);
        if (!isLinearInteger(expression)) throw new IVisitor.VisitorException("Integer expressions must be linear in this logic",expression.pos());
    }

    @Override
    public void checkSortDeclaration(IIdentifier id, List<ISort.IParameter> params, ISort expr) throws IVisitor.VisitorException {
        if (expr != null) checkArraySorts(expr, id.pos());
    }

    @Override
    protected String allowedArraySorts() { return "(Array Int Int)"; }

    @Override
    protected boolean allowedArraySort(ISort.IApplication array) {
        return sameSort(array, sortApp("Array", sortApp("Int"), sortApp("Int")));
    }
}
