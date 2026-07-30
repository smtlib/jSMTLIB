/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

// FIXME - document IVisitor, including an example of an implementation and a discussion about accept; not sure it is used
// FIXME - figure out how to properly do Nullable for generic types
// FIXME - do a review of all of the visit methods to be sure we have the structure correct

import org.smtlib.ICommand.IScript;
import org.smtlib.IExpr.*;
import org.smtlib.IExpr.IError;
import org.smtlib.IResponse.*;
import org.smtlib.ISort.*;

/** This is a visitor interface for visitors over IExpr ASTs. Each AST class implements
 * an accept method that calls the appropriate element of the IVisitor class. An implementation
 * of the IVisitor class will implement an appropriate action in the visit() method.
 * The type parameter T is the return type of the visit method.
 */
public interface IVisitor</*@Nullable*/T extends /*@Nullable*/ Object> {
	public /*@Nullable*/T visit(IAttribute<?> e) throws VisitorException;
	//public /*@Nullable*/T visit(IAttributeValue e) throws VisitorException;
	public /*@Nullable*/T visit(IAttributedExpr e) throws VisitorException;
	public /*@Nullable*/T visit(IBinaryLiteral e) throws VisitorException;
	public /*@Nullable*/T visit(IBinding e) throws VisitorException;
	public /*@Nullable*/T visit(IDecimal e) throws VisitorException;
	public /*@Nullable*/T visit(IError e) throws VisitorException;
	public /*@Nullable*/T visit(IExists e) throws VisitorException;
	public /*@Nullable*/T visit(IFcnExpr e) throws VisitorException;
	public /*@Nullable*/T visit(IForall e) throws VisitorException;
	public /*@Nullable*/T visit(IHexLiteral e) throws VisitorException;
	//public /*@Nullable*/T visit(IIdentifier e) throws VisitorException;
	public /*@Nullable*/T visit(IKeyword e) throws VisitorException;
	public /*@Nullable*/T visit(ILet e) throws VisitorException;
	//public /*@Nullable*/T visit(ILiteral e) throws VisitorException;
	public /*@Nullable*/T visit(INumeral e) throws VisitorException;
    public /*@Nullable*/T visit(ISort.IDatatype e) throws VisitorException;
    public /*@Nullable*/T visit(IExpr.ISortDeclaration e) throws VisitorException;
    public /*@Nullable*/T visit(ISelector e) throws VisitorException;
    public /*@Nullable*/T visit(IConstructor e) throws VisitorException;
    public /*@Nullable*/T visit(IDeclaration e) throws VisitorException;
    public /*@Nullable*/T visit(IFunctionDeclaration e) throws VisitorException;
	public /*@Nullable*/T visit(IParameterizedIdentifier e) throws VisitorException;
	public /*@Nullable*/T visit(IAsIdentifier e) throws VisitorException;
	public /*@Nullable*/T visit(IStringLiteral e) throws VisitorException;
	public /*@Nullable*/T visit(ISymbol e) throws VisitorException;
	public /*@Nullable*/T visit(IScript e) throws VisitorException;
	public /*@Nullable*/T visit(ICommand e) throws VisitorException;
	// Specific visit methods for ICommand subtypes; by default delegate to visit(ICommand e)
	// so that existing IVisitor implementations need not be updated.
	default public /*@Nullable*/T visit(ICommand.Iassert e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Icheck_sat e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Icheck_sat_assuming e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Ideclare_const e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Ideclare_datatype e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Ideclare_datatypes e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Ideclare_fun e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Ideclare_sort e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Ideclare_sort_parameter e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Idefine_const e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Idefine_fun e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Idefine_fun_rec e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Idefine_funs_rec e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Idefine_sort e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Iecho e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Iexit e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Iget_assertions e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Iget_assignment e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Iget_info e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Iget_model e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Iget_option e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Iget_proof e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Iget_unsat_assumptions e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Iget_unsat_core e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Iget_value e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Ipop e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Ipush e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Ireset e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Ireset_assertions e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Iset_info e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Iset_logic e) throws VisitorException { return visit((ICommand)e); }
	default public /*@Nullable*/T visit(ICommand.Iset_option e) throws VisitorException { return visit((ICommand)e); }
	public /*@Nullable*/T visit(IExpr.IMatch e) throws VisitorException;
	public /*@Nullable*/T visit(IExpr.IMatchCase e) throws VisitorException;
	public /*@Nullable*/T visit(IExpr.IPattern e) throws VisitorException;
	
	public /*@Nullable*/T visit(ISort.IFamily s) throws VisitorException;
	public /*@Nullable*/T visit(ISort.IAbbreviation s) throws VisitorException;
	public /*@Nullable*/T visit(ISort.IApplication s) throws VisitorException;
	public /*@Nullable*/T visit(ISort.IFcnSort s) throws VisitorException;
	public /*@Nullable*/T visit(ISort.IParameter s) throws VisitorException;
	
	public /*@Nullable*/T visit(ILogic s) throws VisitorException;
	public /*@Nullable*/T visit(ITheory s) throws VisitorException;
	
	public /*@Nullable*/T visit(IResponse e) throws VisitorException;
	public /*@Nullable*/T visit(IResponse.IError e) throws VisitorException;
	public /*@Nullable*/T visit(IResponse.IAssertionsResponse e) throws VisitorException;
	public /*@Nullable*/T visit(IResponse.IAssignmentResponse e) throws VisitorException;
	public /*@Nullable*/T visit(IResponse.IProofResponse e) throws VisitorException;
	public /*@Nullable*/T visit(IResponse.IValueResponse e) throws VisitorException;
	public /*@Nullable*/T visit(IResponse.IUnsatCoreResponse e) throws VisitorException;
	public /*@Nullable*/T visit(IResponse.IUnsatAssumptionsResponse e) throws VisitorException;
	public /*@Nullable*/T visit(IResponse.IAttributeList e) throws VisitorException;

	/** This class is an implementation of IVisitor, meant to be used as a base class
	 * for further derivation; it implements all of the visitors to simply return null
	 * - that is it will not walk the tree without further implementation.
	 * @param <T> the type of the return value of each visitor
	 */
	// FIXME - revisit the annotations. SHould all the methods have Nullable returns or all of them not?
	static public class NullVisitor</*@Nullable*/T extends /*@Nullable*/Object> implements IVisitor</*@Nullable*/T> {

		@Override
		public /*@Nullable*/T visit(IAttribute<?> e) throws VisitorException {
			return null;
		}

//		@Override
//		public /*@Nullable*/T visit(IAttributeValue e) throws VisitorException {
//			return null;
//		}

		@Override
		public /*@Nullable*/T visit(IAttributedExpr e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IBinaryLiteral e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IBinding e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IDecimal e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IError e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(org.smtlib.IResponse.IError e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IExists e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IFcnExpr e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IForall e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IHexLiteral e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IKeyword e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(ILet e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(INumeral e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IDeclaration e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IExpr.IFunctionDeclaration e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IExpr.ISelector e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IExpr.IConstructor e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IParameterizedIdentifier e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IAsIdentifier e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IStringLiteral e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(ISymbol e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IScript e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(ICommand e) throws VisitorException {
			return null;
		}

		@Override public /*@Nullable*/T visit(ICommand.Iassert e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Icheck_sat e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Icheck_sat_assuming e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Ideclare_const e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Ideclare_datatype e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Ideclare_datatypes e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Ideclare_fun e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Ideclare_sort e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Ideclare_sort_parameter e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Idefine_const e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Idefine_fun e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Idefine_fun_rec e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Idefine_funs_rec e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Idefine_sort e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Iecho e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Iexit e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Iget_assertions e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Iget_assignment e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Iget_info e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Iget_model e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Iget_option e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Iget_proof e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Iget_unsat_assumptions e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Iget_unsat_core e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Iget_value e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Ipop e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Ipush e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Ireset e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Ireset_assertions e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Iset_info e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Iset_logic e) throws VisitorException { return null; }
		@Override public /*@Nullable*/T visit(ICommand.Iset_option e) throws VisitorException { return null; }

		@Override
		public /*@Nullable*/T visit(IResponse e) throws VisitorException {
			return null;
		}

		@Override
		public T visit(IFamily s) throws VisitorException {
			return null;
		}

		@Override
		public T visit(IAbbreviation s) throws VisitorException {
			return null;
		}

		@Override
		public T visit(IApplication s) throws VisitorException {
			return null;
		}

		@Override
		public T visit(IFcnSort s) throws VisitorException {
			return null;
		}

		@Override
		public T visit(IParameter s) throws VisitorException {
			return null;
		}

		@Override
		public T visit(ILogic s) throws VisitorException {
			return null;
		}

		@Override
		public T visit(ITheory s) throws VisitorException {
			return null;
		}

		@Override
		public T visit(IAssertionsResponse e) throws VisitorException {
			return null;
		}

		@Override
		public T visit(IAssignmentResponse e) throws VisitorException {
			return null;
		}

		@Override
		public T visit(IProofResponse e) throws VisitorException {
			return null;
		}

		@Override
		public T visit(IValueResponse e) throws VisitorException {
			return null;
		}

		@Override
		public T visit(IUnsatCoreResponse e) throws VisitorException {
			return null;
		}

		@Override
		public T visit(IResponse.IUnsatAssumptionsResponse e) throws VisitorException {
			return null;
		}

		@Override
		public T visit(IAttributeList e) throws VisitorException {
			return null;
		}

        @Override
        public T visit(ISort.IDatatype e) throws VisitorException {
            return null;
        }

        @Override
        public T visit(IExpr.ISortDeclaration e) throws VisitorException {
            return null;
        }

		@Override
		public /*@Nullable*/T visit(IExpr.IMatch e) throws VisitorException { return null; }

		@Override
		public /*@Nullable*/T visit(IExpr.IMatchCase e) throws VisitorException { return null; }

		@Override
		public /*@Nullable*/T visit(IExpr.IPattern e) throws VisitorException { return null; }

	}

	/** This class is an implementation of IVisitor meant for further derivation:
	 * each visitor is implemented to visit its children without doing anything else;
	 * the default return value is null.
	 * @param <T> the type of the return value
	 */
	public class TreeVisitor</*@Nullable*/T> implements IVisitor</*@Nullable*/T> {

		@Override
		public /*@Nullable*/T visit(IAttribute<?> e) throws VisitorException {
			e.keyword().accept(this);
			if (e.attrValue() instanceof INode) {
				((INode)e.attrValue()).accept(this);
			}
			return null;
		}

//		@Override
//		public /*@Nullable*/T visit(IAttributeValue e) throws VisitorException {
//			return null;
//		}

		@Override
		public /*@Nullable*/T visit(IAttributedExpr e) throws VisitorException {
			e.expr().accept(this);
			for (IAttribute<?> a: e.attributes()) a.accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IBinaryLiteral e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IBinding e) throws VisitorException {
			e.parameter().accept(this);
			e.expr().accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IDecimal e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IError e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(org.smtlib.IResponse.IError e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IExists e) throws VisitorException {
			for (IDeclaration d: e.parameters()) d.accept(this);
			e.expr().accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IFcnExpr e) throws VisitorException {
			e.head().accept(this);
			for (IExpr p: e.args()) p.accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IForall e) throws VisitorException {
			for (IDeclaration d: e.parameters()) d.accept(this);
			e.expr().accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IHexLiteral e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IKeyword e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(ILet e) throws VisitorException {
			for (IBinding d: e.bindings()) d.accept(this);
			e.expr().accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(INumeral e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IDeclaration e) throws VisitorException {
			e.parameter().accept(this);
			e.sort().accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IExpr.IFunctionDeclaration e) throws VisitorException {
			e.symbol().accept(this);
			for (IDeclaration d : e.parameters()) d.accept(this);
			e.sort().accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IExpr.ISelector e) throws VisitorException {
			e.symbol().accept(this);
			e.sort().accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IExpr.IConstructor e) throws VisitorException {
			e.symbol().accept(this);
			for (IExpr.ISelector s : e.selectors()) s.accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IParameterizedIdentifier e) throws VisitorException {
			e.headSymbol().accept(this);
			for (IExpr.IIndex idx: e.indices()) idx.accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IAsIdentifier e) throws VisitorException {
			e.head().accept(this);
			e.qualifier().accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IStringLiteral e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(ISymbol e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IScript e) throws VisitorException {
			for (ICommand c: e.commands()) c.accept(this);
			return null;
		}

		// This should be implemented by each command, so this could be abstract
		// For now at least, we implement it here to avoid the nuisance of
		// requiring implementations when it is not needed
		@Override
		public /*@Nullable*/T visit(ICommand e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(ICommand.Iassert e) throws VisitorException {
			e.expr().accept(this); return null;
		}
		@Override
		public /*@Nullable*/T visit(ICommand.Icheck_sat e) throws VisitorException { return null; }
		@Override
		public /*@Nullable*/T visit(ICommand.Icheck_sat_assuming e) throws VisitorException {
			for (IExpr x : e.exprs()) x.accept(this); return null;
		}
		@Override
		public /*@Nullable*/T visit(ICommand.Ideclare_const e) throws VisitorException {
			e.symbol().accept(this); e.resultSort().accept(this); return null;
		}
		@Override
		public /*@Nullable*/T visit(ICommand.Ideclare_datatype e) throws VisitorException {
			e.sortDeclaration().accept(this); e.datatype().accept(this); return null;
		}
		@Override
		public /*@Nullable*/T visit(ICommand.Ideclare_datatypes e) throws VisitorException {
			for (IExpr.ISortDeclaration sd : e.sortDeclarations()) sd.accept(this);
			for (ISort.IDatatype dt : e.datatypes()) dt.accept(this);
			return null;
		}
		@Override
		public /*@Nullable*/T visit(ICommand.Ideclare_fun e) throws VisitorException {
			e.symbol().accept(this);
			for (ISort s : e.argSorts()) s.accept(this);
			e.resultSort().accept(this); return null;
		}
		@Override
		public /*@Nullable*/T visit(ICommand.Ideclare_sort e) throws VisitorException {
			e.sortSymbol().accept(this); e.arity().accept(this); return null;
		}
		@Override
		public /*@Nullable*/T visit(ICommand.Ideclare_sort_parameter e) throws VisitorException {
			e.sortSymbol().accept(this); return null;
		}
		@Override
		public /*@Nullable*/T visit(ICommand.Idefine_const e) throws VisitorException {
			e.symbol().accept(this); e.resultSort().accept(this); e.expression().accept(this); return null;
		}
		@Override
		public /*@Nullable*/T visit(ICommand.Idefine_fun e) throws VisitorException {
			e.symbol().accept(this);
			for (IDeclaration d : e.parameters()) d.accept(this);
			e.resultSort().accept(this); e.expression().accept(this); return null;
		}
		@Override
		public /*@Nullable*/T visit(ICommand.Idefine_fun_rec e) throws VisitorException {
			e.symbol().accept(this);
			for (IDeclaration d : e.parameters()) d.accept(this);
			e.resultSort().accept(this); e.expression().accept(this); return null;
		}
		@Override
		public /*@Nullable*/T visit(ICommand.Idefine_funs_rec e) throws VisitorException {
			for (IExpr.IFunctionDeclaration d : e.declarations()) d.accept(this);
			for (IExpr body : e.bodies()) body.accept(this);
			return null;
		}
		@Override
		public /*@Nullable*/T visit(ICommand.Idefine_sort e) throws VisitorException {
			e.sortSymbol().accept(this);
			for (IParameter p : e.parameters()) p.accept(this);
			e.expression().accept(this); return null;
		}
		@Override
		public /*@Nullable*/T visit(ICommand.Iecho e) throws VisitorException {
			e.arg().accept(this); return null;
		}
		@Override
		public /*@Nullable*/T visit(ICommand.Iexit e) throws VisitorException { return null; }
		@Override
		public /*@Nullable*/T visit(ICommand.Iget_assertions e) throws VisitorException { return null; }
		@Override
		public /*@Nullable*/T visit(ICommand.Iget_assignment e) throws VisitorException { return null; }
		@Override
		public /*@Nullable*/T visit(ICommand.Iget_info e) throws VisitorException {
			e.infoflag().accept(this); return null;
		}
		@Override
		public /*@Nullable*/T visit(ICommand.Iget_model e) throws VisitorException { return null; }
		@Override
		public /*@Nullable*/T visit(ICommand.Iget_option e) throws VisitorException {
			e.option().accept(this); return null;
		}
		@Override
		public /*@Nullable*/T visit(ICommand.Iget_proof e) throws VisitorException { return null; }
		@Override
		public /*@Nullable*/T visit(ICommand.Iget_unsat_assumptions e) throws VisitorException { return null; }
		@Override
		public /*@Nullable*/T visit(ICommand.Iget_unsat_core e) throws VisitorException { return null; }
		@Override
		public /*@Nullable*/T visit(ICommand.Iget_value e) throws VisitorException {
			for (IExpr x : e.exprs()) x.accept(this); return null;
		}
		@Override
		public /*@Nullable*/T visit(ICommand.Ipop e) throws VisitorException {
			e.number().accept(this); return null;
		}
		@Override
		public /*@Nullable*/T visit(ICommand.Ipush e) throws VisitorException {
			e.number().accept(this); return null;
		}
		@Override
		public /*@Nullable*/T visit(ICommand.Ireset e) throws VisitorException { return null; }
		@Override
		public /*@Nullable*/T visit(ICommand.Ireset_assertions e) throws VisitorException { return null; }
		@Override
		public /*@Nullable*/T visit(ICommand.Iset_info e) throws VisitorException {
			e.infoflag().accept(this);
			if (e.value() instanceof INode) ((INode)e.value()).accept(this);
			return null;
		}
		@Override
		public /*@Nullable*/T visit(ICommand.Iset_logic e) throws VisitorException {
			e.logic().accept(this); return null;
		}
		@Override
		public /*@Nullable*/T visit(ICommand.Iset_option e) throws VisitorException {
			e.option().accept(this);
			if (e.value() instanceof INode) ((INode)e.value()).accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IResponse e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IFamily s) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IAbbreviation s) throws VisitorException {
			s.identifier().accept(this);
			for (IParameter p: s.parameters()) p.accept(this);
			s.sortExpression().accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IApplication s) throws VisitorException {
			s.family().accept(this);
			for (ISort ss: s.parameters()) ss.accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IFcnSort s) throws VisitorException {
			for (ISort ss: s.argSorts()) ss.accept(this);
			s.resultSort().accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IParameter s) throws VisitorException {
			s.symbol().accept(this);
			return null;
		}
		
		@Override
		public /*@Nullable*/T visit(ILogic s) throws VisitorException {
			s.logicName().accept(this);
			for (IAttribute<?> attr: s.attributes().values()) {
				attr.accept(this);
			}
			return null;
		}

		@Override
		public /*@Nullable*/T visit(ITheory s) throws VisitorException {
			s.theoryName().accept(this);
			for (IAttribute<?> attr: s.attributes().values()) {
				attr.accept(this);
			}
			return null;
		}

		@Override
		public T visit(IAssertionsResponse e) throws VisitorException {
			for (IExpr t : e.assertions()) {
				t.accept(this);
			}
			return null;
		}

		@Override
		public T visit(IAssignmentResponse e) throws VisitorException {
			for (IResponse.IPair<ISymbol,Boolean> p : e.assignments()) {
				p.first().accept(this);
			}
			return null;
		}

		@Override
		public T visit(IProofResponse e) throws VisitorException {
			// TODO - add content to a proof object
			return null;
		}

		@Override
		public T visit(IValueResponse e) throws VisitorException {
			for (IResponse.IPair<IExpr,IExpr> p : e.values()) {
				p.first().accept(this);
				p.second().accept(this);
			}
			return null;
		}

		@Override
		public T visit(IUnsatCoreResponse e) throws VisitorException {
			for (ISymbol s: e.names()) {
				s.accept(this);
			}
			return null;
		}

		@Override
		public T visit(IResponse.IUnsatAssumptionsResponse e) throws VisitorException {
			for (ISymbol s: e.names()) {
				s.accept(this);
			}
			return null;
		}

		@Override
		public T visit(IAttributeList e) throws VisitorException {
			for (IAttribute<?> a : e.attributes()) {
				a.accept(this);
			}
			return null;
		}

        @Override
        public T visit(ISort.IDatatype e) throws VisitorException {
            if (e.symbols() != null) for (IExpr.ISymbol s : e.symbols()) s.accept(this);
            for (IExpr.IConstructor c : e.constructors()) c.accept(this);
            return null;
        }

        @Override
        public T visit(IExpr.ISortDeclaration e) throws VisitorException {
            e.symbol().accept(this);
            e.arity().accept(this);
            return null;
        }

		@Override
		public /*@Nullable*/T visit(IExpr.IMatch e) throws VisitorException {
			e.expr().accept(this);
			for (IExpr.IMatchCase mc : e.cases()) mc.accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IExpr.IMatchCase e) throws VisitorException {
			e.pattern().accept(this);
			e.body().accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IExpr.IPattern e) throws VisitorException {
			e.constructor().accept(this);
			for (IExpr.ISymbol v : e.params()) v.accept(this);
			return null;
		}

	}

	/** An Exception class to use if there is a problem during execution of an
	 * IVisitor (e.g. in printing or translating formulae). 
	 * @author David R. Cok
	 */
	public static class VisitorException extends Exception implements IPos.IPosable {
		private static final long serialVersionUID = 1L;
		/** Position information about the textual location of the error */
		@SuppressWarnings("serial") /*@Nullable*/ /*@ReadOnly*/ public IPos pos;
		
		@Override
		public /*@Nullable*/ /*@ReadOnly*/IPos pos() { return pos; }
		
		@Override
		public void setPos(/*@Nullable*/ /*@ReadOnly*/IPos pos) { this.pos = pos; }

		/** Constructor for an exception */
		public VisitorException(String msg, /*@Nullable*//*@ReadOnly*/IPos pos) { 
			super(msg); 
			this.pos = pos; 
		}
		
		/** Constructor taking an exception */
		public VisitorException(Throwable e) {
			super(e);
			this.pos = null;
		}
		
		/** Constructor taking an exception */
		public VisitorException(Throwable e, /*@Nullable*/IPos pos) {
			super(e);
			this.pos = pos;
		}
	}

}
