package org.smtlib.logic;

import java.util.Collection;
import java.util.List;

import org.smtlib.*;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.ISymbol;

public class QF_UFIDL extends Logic {

	public QF_UFIDL(ISymbol name, Collection<IAttribute<?>> attributes) {
		super(name,attributes);
	}
	
	public void validExpression(IExpr expression) throws IVisitor.VisitorException {
		noQuantifiers(expression);
		IVisitor<Void> visitor = new IVisitor.TreeVisitor<Void>() {
			public Void visit(IExpr.IFcnExpr e) throws IVisitor.VisitorException {
				String fcn = e.head().toString();
				if (e.args().size() == 2) {
					if (fcn.equals("*") || fcn.equals("div") || fcn.equals("mod") || fcn.equals("abs")) {
						throw new IVisitor.VisitorException(fcn + " is not allowed in QF_UFIDL", e.pos()); // FIXME + smt.defaultPrinter.toString(e),e.pos());
					} else if (fcn.equals("+") || fcn.equals("-")) {
						IExpr lhs = e.args().get(0);
						IExpr rhs = e.args().get(1);
						if (!(lhs instanceof INumeral || rhs instanceof INumeral)) {
							throw new IVisitor.VisitorException("One of the arguments of + or - must be a numeral", e.pos()); // FIXME + smt.defaultPrinter.toString(e),e.pos());
						}
					} else {
						super.visit(e); // checks all the arguments
					}
						
				} else if (e.args().size() == 1 && fcn.equals("-")) {
					throw new IVisitor.VisitorException("Negation is not allowed in QF_UFIDL", e.pos()); // FIXME + smt.defaultPrinter.toString(e),e.pos());
				}
				return (Void)null;
			}
		};
		expression.accept(visitor);
	}
	
	public void checkFcnDeclaration(IExpr.IIdentifier id, List<ISort> argSorts, ISort resultSort, /*@Nullable*/IExpr definition) throws IVisitor.VisitorException {
	}

	public void checkSortDeclaration(IIdentifier id, List<ISort.IParameter> params, ISort expr) throws IVisitor.VisitorException {
	}

}
