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

public class QF_UFLIA extends LIA {

	public QF_UFLIA(SMT.Configuration smtConfig, ISymbol name, Collection<IAttribute<?>> attributes) {
		super(smtConfig,name,attributes);
	}

	public void checkFcnDeclaration(IExpr.IIdentifier id, List<ISort> argSorts, ISort resultSort, /*@Nullable*/IExpr definition) throws IVisitor.VisitorException {
		// May declare constants or functions
	}

	public void validExpression(IExpr expression) throws IVisitor.VisitorException {
		noQuantifiers(expression);
		super.validExpression(expression);
	}

	public void checkSortDeclaration(IIdentifier id, List<ISort.IParameter> params, ISort expr) throws IVisitor.VisitorException {
		// new sorts permitted
	}


}
