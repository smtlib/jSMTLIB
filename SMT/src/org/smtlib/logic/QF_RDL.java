package org.smtlib.logic;

import org.smtlib.SMT;

import java.util.Collection;
import java.util.List;

import org.smtlib.IExpr;
import org.smtlib.ISort;
import org.smtlib.IVisitor;
import org.smtlib.Utils;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IDecimal;
import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.IQualifiedIdentifier;
import org.smtlib.IExpr.ISymbol;

public class QF_RDL extends Logic {

	public QF_RDL(SMT.Configuration smtConfig, ISymbol name, Collection<IAttribute<?>> attributes) {
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
				// FIXME - need to restrict = and distinct for Real, mirroring QF_IDL's own FIXME
				if (e.args().size() == 2 && (Utils.GE.equals(fcn) || Utils.GT.equals(fcn) || Utils.LT.equals(fcn) || Utils.LE.equals(fcn))) {
					IExpr lhs = e.args().get(0);
					IExpr rhs = e.args().get(1);
					if (lhs instanceof ISymbol) {
						// (op x y): both symbols, or (op x c): a symbol against a real
						// constant -- e.g. (<= x 5.0), a single-variable bound, which
						// tests/logics/ok_QF_RDL.tst already establishes as valid QF_RDL
						// input (unlike QF_IDL's own, stricter, separately-tested
						// symbol-vs-symbol-only quirk -- not touched here).
						if (rhs instanceof ISymbol || isRealConstant(rhs)) {
							return (Void)null;
						} else {
							throw new IVisitor.VisitorException("rhs must be a symbol or a real constant if the lhs is a symbol", e.pos());
						}
					}
					if (!(lhs instanceof IExpr.IFcnExpr)) {
						throw new IVisitor.VisitorException("lhs must be a symbol or a difference", e.pos());
					}
					IExpr.IFcnExpr f = (IExpr.IFcnExpr)lhs;
					if (!Utils.MINUS.equals(f.head())) {
						throw new IVisitor.VisitorException("lhs must be a symbol or a difference", e.pos());
					}
					if (f.args().size() == 2 && f.args().get(0) instanceof ISymbol && f.args().get(1) instanceof ISymbol) {
						// OK
					} else {
						throw new IVisitor.VisitorException("differences must be difference of symbols", e.pos());
					}
					if (!isRealConstant(rhs)) {
						throw new IVisitor.VisitorException("The rhs must be a decimal or negation of a decimal", e.pos());
					}
				} else {
					throw new IVisitor.VisitorException("Invalid operation in RDL logic", e.pos());
				}
				return (Void)null;
			}

			/** True for a decimal literal, or the negation of one (e.g. 5.0 or (- 5.0)) --
			 *  the shape QF_RDL.smt2 allows as the constant "c" in a difference comparison. */
			private boolean isRealConstant(IExpr expr) {
				if (expr instanceof IDecimal) return true;
				if (!(expr instanceof IExpr.IFcnExpr)) return false;
				IExpr.IFcnExpr f = (IExpr.IFcnExpr) expr;
				return f.args().size() == 1 && Utils.MINUS.equals(f.head()) && f.args().get(0) instanceof IDecimal;
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
