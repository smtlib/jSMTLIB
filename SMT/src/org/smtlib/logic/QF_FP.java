package org.smtlib.logic;

import java.util.Collection;
import java.util.List;

import org.smtlib.IExpr;
import org.smtlib.ISort;
import org.smtlib.IVisitor;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.ISymbol;

/** Not an official SMT-LIB logic -- see QF_FP.smt2's own :notes: a jSMTLIB-invented
 *  convenience logic for exercising the FloatingPoint theory in this project's own test
 *  suite without needing the broad ALL logic. Its own :language text ("Closed
 *  quantifier-free formulas ... with free constant symbols") is enforced the same way as
 *  any other quantifier-free, no-UF, no-new-sorts logic in this package. */
public class QF_FP extends Logic {

	public QF_FP(ISymbol name, Collection<IAttribute<?>> attributes) {
		super(name,attributes);
	}

	public void validExpression(IExpr expression) throws IVisitor.VisitorException {
		noQuantifiers(expression);
	}

	public void checkFcnDeclaration(IExpr.IIdentifier id, List<ISort> argSorts, ISort resultSort, /*@Nullable*/IExpr definition) throws IVisitor.VisitorException {
		noFunctions(id,argSorts,resultSort,definition);
	}

	public void checkSortDeclaration(IIdentifier id, List<ISort.IParameter> params, ISort expr) throws IVisitor.VisitorException {
		noSorts(id,params,expr);
	}

}
