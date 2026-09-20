package org.smtlib.logic;

import org.smtlib.SMT;

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

	public QF_IDL(SMT.Configuration smtConfig, ISymbol name, Collection<IAttribute<?>> attributes) {
		super(smtConfig,name,attributes);
	}
	
	public void validExpression(IExpr expression) throws IVisitor.VisitorException {
		noQuantifiers(expression);
		IVisitor<Void> visitor = new IVisitor.TreeVisitor<Void>() {
			public Void visit(IExpr.IFcnExpr e) throws IVisitor.VisitorException {
				IQualifiedIdentifier fcn = e.head();
				if (Utils.AND.equals(fcn) || Utils.OR.equals(fcn) || Utils.NOT.equals(fcn) || Utils.IMPLIES.equals(fcn)) {
					for (IExpr arg : e.args()) arg.accept(this);
					return (Void)null;
				}
				if (Utils.EQ.equals(fcn) || Utils.DISTINCT.equals(fcn)) return (Void)null;
				// FIXME - need to restrict = and distinct for Int
				if (e.args().size() == 2 && (Utils.GE.equals(fcn) || Utils.GT.equals(fcn) || Utils.LT.equals(fcn) || Utils.LE.equals(fcn))) {
					IExpr lhs = e.args().get(0);
					IExpr rhs = e.args().get(1);
					if (lhs instanceof ISymbol) {
						if (rhs instanceof ISymbol) {
							return (Void)null;
						} else {
							throw restrictionError("rhs must be a symbol if the lhs is a symbol", e);
						}
					}
					if (!(lhs instanceof IExpr.IFcnExpr)) {
						throw restrictionError("lhs must be a symbol or a difference", e);
					}
                    IExpr.IFcnExpr f = (IExpr.IFcnExpr)lhs;
					if (!Utils.MINUS.equals(f.head())) {
						throw restrictionError("lhs must be a symbol or a difference", e);
					}
					if (f.args().size()  == 2 && f.args().get(0) instanceof ISymbol && f.args().get(1) instanceof ISymbol) {
						// OK
					} else {
						throw restrictionError("differences must be difference of symbols", e);
					}
					if (rhs instanceof INumeral) {
						// OK
					} else if (!(rhs instanceof IExpr.IFcnExpr)) {
						throw restrictionError("The rhs must be an integer", e);
					} else {
						f = (IExpr.IFcnExpr)rhs;
						if (f.args().size() == 1 && Utils.MINUS.equals(f.head()) && f.args().get(0) instanceof INumeral) {
						    // OK
						} else {
							throw restrictionError("The rhs must be a numeral or negation of numeral", e);
						}
					}
				} else {
					throw restrictionError("Invalid operation in IDL logic", e);
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
