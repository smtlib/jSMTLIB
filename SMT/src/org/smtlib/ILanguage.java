package org.smtlib;

import java.util.List;

import org.smtlib.IExpr.IIdentifier;

// FIXME - document

public interface ILanguage {
	void validExpression(IExpr expression) throws IVisitor.VisitorException;
	
	void checkFcnDeclaration(IExpr.IIdentifier id, List<ISort> argSorts, ISort resultSort, /*@Nullable*/IExpr definition) throws IVisitor.VisitorException;
	void checkSortDeclaration(IIdentifier id, List<ISort.IParameter> params, ISort expr) throws IVisitor.VisitorException;
}