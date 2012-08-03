package org.smtlib.logic;

import java.util.Collection;
import java.util.List;

import org.smtlib.IExpr;
import org.smtlib.IExpr.*;
import org.smtlib.impl.SMTExpr;
import org.smtlib.ILanguage;
import org.smtlib.IResponse;
import org.smtlib.ISort;
import org.smtlib.IVisitor;

public class QF_UF extends Logic implements ILanguage {

	public QF_UF(ISymbol name, Collection<IAttribute<?>> attributes) {
		super(name,attributes);
	}
	
	public void validExpression(IExpr expression) throws IVisitor.VisitorException {
		noQuantifiers(expression);
	}
	
	public void checkFcnDeclaration(IExpr.IIdentifier id, List<ISort> argSorts, ISort resultSort, /*@Nullable*/IExpr definition) throws IVisitor.VisitorException {}

}
