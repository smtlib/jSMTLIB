/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

import java.util.List;

import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IPos.IPosable;
import org.smtlib.sexpr.ISexpr.ISeq;

/** This interface represents responses that can be received from SMT-LIB commands. */
public interface IResponse extends INode {
	
	/** Returns true if the response is a SUCCESS response */
	boolean isOK();
	
	/** Returns true if the response is an error response */
	//@ ensures \result <==> (this instanceof IResponse.IError);
	boolean isError();
	
	/** The interface for error responses */
	public static interface IError extends IResponse, IPosable {
		/** Returns the error message held by this response */
		String errorMsg();
		
		/** Returns the textual location for the response, if available and applicable, otherwise null. */
		/*@Nullable*/ IPos pos();
	}
	
	/** An interface for simple pairs of objects; used to represent value/assignment response items */
	public static interface IPair<T1,T2> {
		T1 first();
		T2 second();
	}

	
	/** The factory interface for creating the standard IResponse singleton and structured instances. */
	public static interface IFactory {
		IError error(String msg);
		IError error(String msg, /*@Nullable*//*@ReadOnly*/ IPos pos);
		IResponse empty();
		IResponse success();
		IResponse unsupported();
		IResponse unknown();
		IResponse sat();
		IResponse unsat();
		IResponse immediate_exit();
		IResponse continued_execution();
		IResponse memout();
		IResponse incomplete();
		/** Returns a constant response with the given canonical name */
		IResponse constant(String id); // FIXME - use abstract keyword?
		/** The argument has no SMT-LIB escapes and no enclosing quotes */
		IResponse stringLiteral(String value);
		IResponse numericLiteral(int value);
		IResponse get_option_response(IAttributeValue v);
		IResponse.IAttributeList get_info_response(IAttribute<?> attr);
		IResponse.IAttributeList get_info_response(List<IAttribute<?>> attrList);
		IResponse.IProofResponse get_proof_response();
		IResponse.IValueResponse get_value_response(List<IPair<IExpr,IExpr>> values);
		<T1,T2> IPair<T1,T2> pair(T1 first, T2 second);
		IResponse.IAssignmentResponse get_assignment_response(List<IPair<IExpr.ISymbol,Boolean>> assignments);
        IResponse.IUnsatAssumptionsResponse get_unsat_assumptions_response(List<ISymbol> names);
        IResponse.IUnsatCoreResponse get_unsat_core_response(List<ISymbol> names);
		IResponse.IAssertionsResponse get_assertions_response(List<IExpr> exprs);
	}
	
	/** Response type for get-info, carrying a list of attribute key-value pairs. */
	static public interface IAttributeList extends IResponse {
		public List<IAttribute<? extends IAttributeValue>> attributes();
	}

	/** Response type for get-assignment, carrying a list of name-Boolean pairs. */
	static public interface IAssignmentResponse extends IResponse {
		public List<IPair<IExpr.ISymbol,Boolean>> assignments();
	}

	/** Response type for get-value, carrying a list of expression-value pairs. */
	static public interface IValueResponse extends IResponse {
		public List<IPair<IExpr,IExpr>> values();
	}

	/** Response type for get-unsat-core, carrying the names of the formulae in the unsat core. */
    static public interface IUnsatCoreResponse extends IResponse {
        public List<IExpr.ISymbol> names();
    }

	/** Response type for get-unsat-assumptions, carrying the named assumptions in the unsat core. */
    static public interface IUnsatAssumptionsResponse extends IResponse {
        public List<IExpr.ISymbol> names();
    }

	/** Response type for get-assertions, carrying the list of currently asserted formulae. */
	static public interface IAssertionsResponse extends IResponse {
		public List<IExpr> assertions();
	}

	/** Response type for get-proof, carrying an opaque proof object. */
	static public interface IProofResponse extends IResponse {
		public Object proof();
	}
}
