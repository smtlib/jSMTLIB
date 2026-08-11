package org.smtlib.logic;

import java.util.Collection;
import java.util.List;

import org.smtlib.IExpr;
import org.smtlib.ISort;
import org.smtlib.IVisitor;
import org.smtlib.Utils;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.IQualifiedIdentifier;
import org.smtlib.IExpr.ISymbol;

public class QF_IDL extends Logic {

	public QF_IDL(ISymbol name, Collection<IAttribute<?>> attributes) {
		super(name,attributes);
	}
	
	public void validExpression(IExpr expression) throws IVisitor.VisitorException {
		noQuantifiers(expression);
		IVisitor<Void> visitor = new IVisitor.TreeVisitor<Void>() {
			public Void visit(IExpr.IFcnExpr e) throws IVisitor.VisitorException {
				IQualifiedIdentifier fcn = e.head();
				if (Utils.AND.equals(fcn) || Utils.OR.equals(fcn) || Utils.NOT.equals(fcn) || Utils.IMPLIES.equals(fcn)) return (Void)null;
				if (Utils.EQ.equals(fcn) || Utils.DISTINCT.equals(fcn)) return (Void)null;
				// FIXME - need to restrict = and distinct for Int
				if (e.args().size() == 2 && (Utils.GE.equals(fcn) || Utils.GT.equals(fcn) || Utils.LT.equals(fcn) || Utils.LE.equals(fcn))) {
					IExpr lhs = e.args().get(0);
					IExpr rhs = e.args().get(1);
					if (lhs instanceof ISymbol) {
						if (rhs instanceof ISymbol) {
							return (Void)null;
						} else {
							throw new IVisitor.VisitorException("rhs must be a symbol if the lhs is a symbol", e.pos()); // FIXME + smt.defaultPrinter.toString(e),e.pos());
						}
					}
					if (!(lhs instanceof IExpr.IFcnExpr)) {
						throw new IVisitor.VisitorException("lhs must be a symbol or a difference", e.pos()); // FIXME + smt.defaultPrinter.toString(e),e.pos());
					}
                    IExpr.IFcnExpr f = (IExpr.IFcnExpr)lhs;
					if (!Utils.MINUS.equals(f.head())) {
						throw new IVisitor.VisitorException("lhs must be a symbol or a difference", e.pos()); // FIXME + smt.defaultPrinter.toString(e),e.pos());
					}
					if (f.args().size()  == 2 && f.args().get(0) instanceof ISymbol && f.args().get(1) instanceof ISymbol) {
						// OK
					} else {
						throw new IVisitor.VisitorException("differences must be difference of symbols", e.pos()); // FIXME + smt.defaultPrinter.toString(e),e.pos());
					}
					if (rhs instanceof INumeral) {
						// OK
					} else if (!(rhs instanceof IExpr.IFcnExpr)) {
						throw new IVisitor.VisitorException("The rhs must be an integer", e.pos()); // FIXME + smt.defaultPrinter.toString(e),e.pos());
					} else {
						f = (IExpr.IFcnExpr)rhs;
						if (f.args().size() == 1 && Utils.MINUS.equals(f.head()) && f.args().get(0) instanceof INumeral) {
						    // OK
						} else {
							throw new IVisitor.VisitorException("The rhs must be a numeral or negation of numeral", e.pos()); // FIXME + smt.defaultPrinter.toString(e),e.pos());
						}
					}
				} else {
					throw new IVisitor.VisitorException("Invalid operation in IDL logic", e.pos()); // FIXME + smt.defaultPrinter.toString(e),e.pos());
				}
				return (Void)null;
			}
		};
		expression.accept(visitor);
	}
	
	public void checkFcnDeclaration(IExpr.IIdentifier id, List<ISort> argSorts, ISort resultSort, /*@Nullable*/IExpr definition) throws IVisitor.VisitorException {
		noFunctions(id,argSorts,resultSort,definition);
	}

	public void checkSortDeclaration(IIdentifier id, List<ISort.IParameter> params, ISort expr) throws IVisitor.VisitorException {
		noSorts(id,params,expr);
	}


}
