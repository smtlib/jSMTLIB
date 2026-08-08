package org.smtlib.logic;

import java.util.Collection;
import java.util.List;

import org.smtlib.IExpr;
import org.smtlib.ISort;
import org.smtlib.IVisitor;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.ISymbol;

public class QF_EIA extends Logic {

	public QF_EIA(ISymbol name, Collection<IAttribute<?>> attributes) {
		super(name,attributes);
	}

    public void checkFcnDeclaration(IExpr.IIdentifier id, List<ISort> argSorts, ISort resultSort, /*@Nullable*/IExpr definition) throws IVisitor.VisitorException {
        // May declare constants, but not functions without definitions
        noFunctions(id,argSorts,resultSort,definition);
    }

    public void validExpression(IExpr expression) throws IVisitor.VisitorException {
        noQuantifiers(expression);
        // Exponentiation (**) is permitted — that is the sole difference from QF_NIA.
    }

    public void checkSortDeclaration(IIdentifier id, List<ISort.IParameter> params, ISort expr) throws IVisitor.VisitorException {
        noSorts(id,params,expr);
    }

}
