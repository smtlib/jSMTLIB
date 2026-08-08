package org.smtlib.logic;

import java.util.Collection;
import java.util.List;

import org.smtlib.*;
import org.smtlib.IExpr.*;
import org.smtlib.impl.SMTExpr;

// FIXME - move some of this to ILogic - should the logic classes depend on SMTExpr.Logic?
//FIXME - document
public abstract class Logic extends SMTExpr.Logic implements ILanguage {

	public Logic(ISymbol name, Collection<IAttribute<?>> attributes) {
		super(name,attributes);
	}
	
	public void noQuantifiers(IExpr expression) throws IVisitor.VisitorException {
		IVisitor<Void> visitor = new IVisitor.TreeVisitor<Void>() {
			@Override
			public Void visit(IForall e) throws IVisitor.VisitorException {
				throw new IVisitor.VisitorException("A quantified expression is not allowed in the " + logicName + " logic",e.pos());
			}
			@Override
			public Void visit(IExists e) throws IVisitor.VisitorException {
				throw new IVisitor.VisitorException("A quantified expression is not allowed in the " + logicName + " logic",e.pos());
			}
		};
		expression.accept(visitor);
	}

	public void noExponentiation(IExpr expression) throws IVisitor.VisitorException {
		IVisitor<Void> visitor = new IVisitor.TreeVisitor<Void>() {
			@Override
			public Void visit(IExpr.IFcnExpr e) throws IVisitor.VisitorException {
				if (e.head().toString().equals("**"))
					throw new IVisitor.VisitorException("The exponentiation operator ** is not allowed in the " + logicName + " logic", e.pos());
				return super.visit(e);
			}
		};
		expression.accept(visitor);
	}
	
	public void noFunctions(IExpr.IIdentifier id, List<ISort> argSorts, ISort resultSort, /*@Nullable*/IExpr definition) throws IVisitor.VisitorException {
		// May declare constants, but not functions without definitions
		if (argSorts.size() != 0 && definition == null) 
			throw new IVisitor.VisitorException("Declarations of uninterpreted functions are not allowed in this logic",id.pos());

	}
	
	public void noSorts(IIdentifier id, List<ISort.IParameter> params, ISort expr) throws IVisitor.VisitorException {
		if (expr == null) throw new IVisitor.VisitorException("New sorts are not allowed in this logic",id.pos());
	}

	/** Checks that the sort expression contains no Array sort outside the allowed set.
	 *  Skips the check for Array sorts whose parameters include sort parameters (parameterized abbreviations).
	 *  @param allowedMsg  human-readable list of allowed Array sorts, used in the error message
	 *  @param allowedSorts  exact toString() representations of allowed Array sorts */
	protected void checkArraySort(ISort sort, IIdentifier id, String allowedMsg, String... allowedSorts) throws IVisitor.VisitorException {
		if (!(sort instanceof ISort.IApplication)) return;
		ISort.IApplication app = (ISort.IApplication) sort;
		if (app.family().headSymbol().toString().equals("Array")) {
			for (ISort param : app.parameters()) {
				if (param instanceof ISort.IParameter) return;
			}
			String sortStr = sort.toString();
			for (String allowed : allowedSorts) {
				if (sortStr.equals(allowed)) return;
			}
			throw new IVisitor.VisitorException("Array sorts must be " + allowedMsg + " in this logic", id.pos());
		}
		for (ISort param : app.parameters()) {
			checkArraySort(param, id, allowedMsg, allowedSorts);
		}
	}


	public boolean isInteger(IExpr expr) {
		if (expr instanceof IExpr.INumeral) return true;
		if (!(expr instanceof IExpr.IFcnExpr)) return false;
		IExpr.IFcnExpr f = (IExpr.IFcnExpr)expr;
		if (f.head().toString().equals("-") && f.args().size() == 1) {
			expr = f.args().get(0);
			if (expr instanceof IExpr.INumeral) return true;
			return false;
		}
		return false;
	}
	
	public boolean isFreeConstant(IExpr expr) {
		return (expr instanceof ISymbol);
//		if (!(expr instanceof IExpr.IFcnExpr)) return false;
//		IExpr.IFcnExpr f = (IExpr.IFcnExpr)expr;
//		return f.args().size() == 0;
	}
	
	public boolean isLinearInteger(IExpr expr) {
		try {
			IVisitor<Void> visitor = new IVisitor.TreeVisitor<Void>() {
				@Override
				public Void visit(IExpr.IFcnExpr e) throws IVisitor.VisitorException {
					String fcn = e.head().toString();
					if (fcn.equals("*") && e.args().size() == 2) {
						IExpr lhs = e.args().get(0);
						IExpr rhs = e.args().get(1);
						if (!((isInteger(lhs) && isFreeConstant(rhs)) || (isFreeConstant(lhs) && isInteger(rhs))))
							throw new IVisitor.VisitorException("nonlinear", null);
						return null;
					} else if (fcn.equals("div") || fcn.equals("mod") || fcn.equals("abs")) {
						throw new IVisitor.VisitorException("nonlinear", null);
					}
					return super.visit(e);
				}
			};
			expr.accept(visitor);
			return true;
		} catch (IVisitor.VisitorException e) {
			return false;
		}
	}

	public boolean isLinearReal(IExpr expr) {
		try {
			IVisitor<Void> visitor = new IVisitor.TreeVisitor<Void>() {
				@Override
				public Void visit(IExpr.IFcnExpr e) throws IVisitor.VisitorException {
					String fcn = e.head().toString();
					if (fcn.equals("*") && e.args().size() == 2) {
						IExpr lhs = e.args().get(0);
						IExpr rhs = e.args().get(1);
						if (!((isRealConst(lhs) && isFreeConstant(rhs)) || (isFreeConstant(lhs) && isRealConst(rhs))))
							throw new IVisitor.VisitorException("nonlinear", null);
						return null;
					} else if (fcn.equals("/") && e.args().size() == 2) {
						if (!(isRealConst(e.args().get(0)) && isRealConst(e.args().get(1))))
							throw new IVisitor.VisitorException("nonlinear", null);
						return null;
					}
					return super.visit(e);
				}
			};
			expr.accept(visitor);
			return true;
		} catch (IVisitor.VisitorException e) {
			return false;
		}
	}

	public boolean isRealConst(IExpr expr) {
		if (expr instanceof IExpr.INumeral) return true;
		if (expr instanceof IExpr.IDecimal) return true;
		if (!(expr instanceof IExpr.IFcnExpr)) return false;
		IExpr.IFcnExpr f = (IExpr.IFcnExpr)expr;
		if (f.head().toString().equals("-") && f.args().size() == 1) {
			IExpr arg = f.args().get(0);
			return (arg instanceof IExpr.INumeral) || (arg instanceof IExpr.IDecimal);
		}
		if (f.head().toString().equals("/") && f.args().size() == 2) {
			return isInteger(f.args().get(0)) && (f.args().get(1) instanceof IExpr.INumeral)
				&& ((IExpr.INumeral)f.args().get(1)).intValue() != 0;
		}
		return false;
	}
}
