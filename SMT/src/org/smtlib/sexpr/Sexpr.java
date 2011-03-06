/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.sexpr;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.smtlib.IVisitor;
import org.smtlib.impl.Pos;

/** This is the root class for S-expressions in the concrete syntax */
public abstract class Sexpr extends Pos.Posable implements ISexpr {
	
	/** The class corresponding to sequences of S-expressions */
	public static class Seq extends Sexpr implements ISeq {
		List<ISexpr> sexprs;
		
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

		// Use object identity
//		@Override
//		public boolean equals(Object o) {
//			if (!(o instanceof Seq)) return false;
//			Seq s = (Seq)o;
//			if (s.sexprs.size() != sexprs.size()) return false;
//			Iterator<? extends ISexpr> iter = sexprs.iterator();
//			Iterator<? extends ISexpr> iterb = s.sexprs().iterator();
//			while (iter.hasNext() && iterb.hasNext()) {
//				if (!(iter.next().equals(iterb.next()))) return false;
//			}
//			return true;
//		}
//		
//		@Override
//		public int hashCode() {
//			Iterator<? extends ISexpr> iter = sexprs.iterator();
//			int hash = sexprs.size();
//			while (iter.hasNext()) {
//				hash += iter.next().hashCode();
//			}
//			return hash;
//		}
		
		/** For debugging - for real printing use a Printer */
		@Override
		public String toString() {
			StringBuilder sb = new StringBuilder();
			Iterator<? extends ISexpr> iter = sexprs.iterator();
			sb.append("( ");
			while (iter.hasNext()) {
				sb.append(iter.next().toString());
				sb.append(" ");
			}
			sb.append(")");
			return sb.toString();
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
		T value;
		public Token(T value) {
			this.value = value;
		}
		
		@Override
		public T value() {
			return value;
		}

		// Use object identity
//
//		@Override
//		public boolean equals(Object o) {
//			if (!(o instanceof IToken)) return false;
//			return ((IToken<?>)o).value().equals(value);
//		}
//		
//		@Override
//		public int hashCode() {
//			return value.hashCode();
//		}
		
		/** For debugging - for real printing use a Printer */
		@Override
		public String toString() {
			return value.toString();
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
}