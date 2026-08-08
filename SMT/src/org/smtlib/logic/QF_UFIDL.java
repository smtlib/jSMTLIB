package org.smtlib.logic;

import java.util.Collection;
import java.util.List;

import org.smtlib.*;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.ISymbol;

public class QF_UFIDL extends QF_IDL {

	public QF_UFIDL(ISymbol name, Collection<IAttribute<?>> attributes) {
		super(name,attributes);
	}

	@Override
	public void validExpression(IExpr expression) throws IVisitor.VisitorException {
		noQuantifiers(expression);
		// Note: QF_UFIDL is not a syntactic extension of QF_IDL per the spec.
		// Full IDL atom-shape validation is pending a fix of the QF_IDL validExpression bugs.
	}

	public void checkFcnDeclaration(IExpr.IIdentifier id, List<ISort> argSorts, ISort resultSort, /*@Nullable*/IExpr definition) throws IVisitor.VisitorException {
	}

	public void checkSortDeclaration(IIdentifier id, List<ISort.IParameter> params, ISort expr) throws IVisitor.VisitorException {
	}

}
