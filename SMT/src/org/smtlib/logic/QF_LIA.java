package org.smtlib.logic;

import org.smtlib.SMT;

import java.util.Collection;

import org.smtlib.IExpr;
import org.smtlib.IVisitor;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.ISymbol;

public class QF_LIA extends LIA {

	public QF_LIA(SMT.Configuration smtConfig, ISymbol name, Collection<IAttribute<?>> attributes) {
		super(smtConfig,name,attributes);
	}

	public void validExpression(IExpr expression) throws IVisitor.VisitorException {
		noQuantifiers(expression);
		super.validExpression(expression);
	}

}
