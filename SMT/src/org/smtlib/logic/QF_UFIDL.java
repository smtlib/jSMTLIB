package org.smtlib.logic;

import java.util.Collection;
import java.util.List;

import org.smtlib.*;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.ISymbol;

public class QF_UFIDL extends Logic {

	public QF_UFIDL(ISymbol name, Collection<IAttribute<?>> attributes) {
		super(name,attributes);
	}

	@Override
	public void validExpression(IExpr expression) throws IVisitor.VisitorException {
		noQuantifiers(expression);
		// QF_UFIDL's own :note (see QF_UFIDL.smt2) says its syntax is *not* an extension of
		// QF_IDL's -- so this deliberately does not reuse QF_IDL's atom-shape restriction (it
		// would reject valid QF_UFIDL formulas). The actual restriction the spec gives instead
		// -- for every (+ t1 t2)/(- t1 t2), at least one of t1, t2 must be a numeral -- is not
		// yet implemented here; see issue #49's FIXME family for that class of gap.
	}

	public void checkFcnDeclaration(IExpr.IIdentifier id, List<ISort> argSorts, ISort resultSort, /*@Nullable*/IExpr definition) throws IVisitor.VisitorException {
	}

	public void checkSortDeclaration(IIdentifier id, List<ISort.IParameter> params, ISort expr) throws IVisitor.VisitorException {
	}

}
