/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.sexpr;

import java.util.LinkedList;
import java.util.List;

import org.smtlib.IExpr;
import org.smtlib.IVisitor;
import org.smtlib.IVisitor.VisitorException;
import org.smtlib.impl.Pos;

/** This is the root class for S-expressions in the concrete syntax */
public abstract class Sexpr extends Pos.Printable implements ISexpr {
	
	/** The class corresponding to sequences of S-expressions */
	public static class Seq extends Sexpr implements ISeq {
		protected List<ISexpr> sexprs;
		
		public Seq() {
			this.sexprs = new LinkedList<ISexpr>();
		}
		
		public Seq(List<ISexpr> sexprs) {
			this.sexprs = sexprs;
		}
		
		@Override
		public List<ISexpr> sexprs() {
			return sexprs;
		}

		@Override
		public String kind() { return "sequence"; }
		
		@Override
		public boolean isOK() { return false; }
		
		@Override
		public boolean isError() { return false; }

		@Override
		public <TT> TT accept(IVisitor<TT> v) throws IVisitor.VisitorException {
			return v.visit(this);
		}
		
	}
	
	/** Represents a single S-expression token with intrinsic type T */
	public static class Token<T> extends Sexpr implements IToken<T> {
		protected T value;
		
		public Token(T value) {
			this.value = value;
		}
		
		@Override
		public T value() {
			return value;
		}

		@Override
		public String kind() { return "token"; }

		@Override
		public boolean isOK() { return false; }
		
		@Override
		public boolean isError() { return false; }

		@Override
		public <TT> TT accept(IVisitor<TT> v) throws IVisitor.VisitorException {
			return v.visit(this);
		}
	}
	
	// FIXME - this class is temporary until we have a way to convert an IExpr to an ISexpr
	public static class Expr extends Sexpr {

		@Override
		public String kind() {
			return "Expr";
		}

		@Override
		public boolean isOK() {
			return true;
		}

		@Override
		public boolean isError() {
			return false;
		}

		@Override
		public <T> T accept(IVisitor<T> v) throws VisitorException {
			return expr.accept(v);
		}

		public IExpr expr;

		public Expr(IExpr e) {
			expr = e;
		}
	}
}
