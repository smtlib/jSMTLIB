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

/** This logic does not allow quantifiers; all array terms have sort (Array (_ BitVec i) (_ BitVec j)) */
public class QF_AUFBV extends QF_UF {

    public QF_AUFBV(SMT.Configuration smtConfig, ISymbol name, Collection<IAttribute<?>> attributes) {
        super(smtConfig,name,attributes);
    }

    @Override
    public void checkFcnDeclaration(IExpr.IIdentifier id, List<ISort> argSorts, ISort resultSort, /*@Nullable*/IExpr definition) throws IVisitor.VisitorException {
        checkArraySorts(argSorts, resultSort, id);
    }

    @Override
    public void checkSortDeclaration(IIdentifier id, List<ISort.IParameter> params, ISort expr) throws IVisitor.VisitorException {
        if (expr != null) checkArraySorts(expr, id.pos());
    }

    @Override
    protected String allowedArraySorts() { return "(Array (_ BitVec i) (_ BitVec j))"; }

    @Override
    protected boolean allowedArraySort(ISort.IApplication array) { return isBitVecArray(array); }
}
