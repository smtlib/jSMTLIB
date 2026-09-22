package org.smtlib.logic;

import org.smtlib.SMT;

import java.util.Collection;
import java.util.List;

import org.smtlib.IExpr;
import org.smtlib.IExpr.*;
import org.smtlib.ILanguage;
import org.smtlib.ISort;
import org.smtlib.IVisitor;

public class QF_UF extends Logic implements ILanguage {

	public QF_UF(SMT.Configuration smtConfig, ISymbol name, Collection<IAttribute<?>> attributes) {
		super(smtConfig,name,attributes);
	}
	
	@Override
	public void validExpression(IExpr expression) throws IVisitor.VisitorException {
		noQuantifiers(expression);
	}
	
	@Override
	public void checkFcnDeclaration(IExpr.IIdentifier id, List<ISort> argSorts, ISort resultSort, /*@Nullable*/IExpr definition) throws IVisitor.VisitorException {}

}
