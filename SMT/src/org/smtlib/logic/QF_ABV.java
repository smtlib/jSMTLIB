package org.smtlib.logic;

import java.util.Collection;
import java.util.List;

import org.smtlib.IExpr;
import org.smtlib.ISort;
import org.smtlib.IVisitor;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.ISymbol;

/** This logic does not allow quantifiers or uninterpreted functions */
public class QF_ABV extends QF_UF {

	public QF_ABV(ISymbol name, Collection<IAttribute<?>> attributes) {
		super(name,attributes);
	}
	
	public void checkFcnDeclaration(IExpr.IIdentifier id, List<ISort> argSorts, ISort resultSort, /*@Nullable*/IExpr definition) throws IVisitor.VisitorException {
		// May declare constants, but not functions without definitions
		noFunctions(id,argSorts,resultSort,definition);
		checkArraySortIsBitVecToBitVec(resultSort, id);
	}

	public void checkSortDeclaration(IIdentifier id, List<ISort.IParameter> params, ISort expr) throws IVisitor.VisitorException {
		noSorts(id,params,expr);
		if (expr != null) checkArraySortIsBitVecToBitVec(expr, id);
	}

	// The spec's "Formulas in ite terms must satisfy the same restriction as well [i.e. be
	// quantifier-free], with the exception that they need not be closed" doesn't need any
	// extra handling here: noQuantifiers() (inherited from QF_UF.validExpression()) recurses
	// into every subexpression via the ordinary IVisitor.TreeVisitor traversal, including an
	// ite's condition argument, since neither QF_UF nor QF_ABV override visit(IFcnExpr) to
	// special-case ite. A quantifier nested inside an ite condition is already rejected.
}
