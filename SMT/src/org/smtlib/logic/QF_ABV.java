package org.smtlib.logic;

import java.util.Collection;
import java.util.List;

import org.smtlib.IExpr;
import org.smtlib.ISort;
import org.smtlib.IVisitor;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.ISymbol;

/** This logic does not allow quantifiers or uninterpreted functions */
public class QF_ABV extends QF_UF {

	public QF_ABV(ISymbol name, Collection<IAttribute<?>> attributes) {
		super(name,attributes);
	}
	
	public void checkFcnDeclaration(IExpr.IIdentifier id, List<ISort> argSorts, ISort resultSort, /*@Nullable*/IExpr definition) throws IVisitor.VisitorException {
		// May declare constants, but not functions without definitions
		noFunctions(id,argSorts,resultSort,definition);
	}

	
}
