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

public class AUFLIRA extends Logic {

    public AUFLIRA(SMT.Configuration smtConfig, ISymbol name, Collection<IAttribute<?>> attributes) {
        super(smtConfig,name,attributes);
    }

    @Override
    public void checkFcnDeclaration(IExpr.IIdentifier id, List<ISort> argSorts, ISort resultSort, /*@Nullable*/IExpr definition) throws IVisitor.VisitorException {
        checkArraySorts(argSorts, resultSort, id);
    }

    @Override
    public void validExpression(IExpr expression) throws IVisitor.VisitorException {
        if (!isLinearReal(expression))
            throw new IVisitor.VisitorException("Arithmetic expressions must be linear in the " + logicName + " logic", expression.pos());
        checkBoundArraySorts(expression);
    }

    @Override
    public void checkSortDeclaration(IIdentifier id, List<ISort.IParameter> params, ISort expr) throws IVisitor.VisitorException {
        if (expr != null) checkArraySorts(expr, id.pos());
    }

    @Override
    protected String allowedArraySorts() { return "(Array Int Real) or (Array Int (Array Int Real))"; }

    @Override
    protected boolean allowedArraySort(ISort.IApplication array) {
        ISort intReal = sortApp("Array", sortApp("Int"), sortApp("Real"));
        return sameSort(array, intReal) || sameSort(array, sortApp("Array", sortApp("Int"), intReal));
    }

}
