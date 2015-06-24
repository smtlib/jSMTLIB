package org.smtlib;

import org.junit.Before;
import org.junit.Test;

// FIXME - need to check complex sorts; parameterized definitions; Int and NUMERAL types; variadic functions; parameterized function sorts
// FIXME - need to implement checking of sort expressions

public class TypeCheck extends TypeCheckRoot {

	@Override
	@Before
	public void setup() {
		super.setup();
		checkResponse(solver.set_logic("QF_UF",null));
	}
	
	@Test
	public void checkTrue() {
		check("true");
	}

	@Test
	public void checkBadVar() {
		check("p","Unknown constant symbol p");
	}
	
	@Test
	public void checkBoolVar() {
		doCommand("(declare-fun p () Bool)");
		check("p");
	}
	
	@Test
	public void checkBoolFcn() {
		doCommand("(declare-sort X 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () Bool)");
		check("(or p q)");
	}
	
	@Test
	public void checkBadFcn() {
		doCommand("(declare-sort X 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () X)");
		check("(or p q)","Unknown predicate symbol or with argument types Bool X");
	}
	
	@Test
	public void checkBadSort() {
		doCommand("(declare-sort X 0)");
		doCommand("(declare-fun p () X)");
		check("p","Expected an expression with Bool sort, not X");
	}
	
	@Test
	public void checkLet() {
		doCommand("(declare-sort X 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () X)");
		check("(let ((r true)(s q)) (not r))");
	}
	
	@Test
	public void checkBadLet() {
		doCommand("(declare-sort X 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () X)");
		check("(let ((r true)(s q)) (not s))","Unknown predicate symbol not with argument types X");
	}
	
	@Test
	public void checkForall() {
		doCommand("(declare-sort X 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () X)");
		check("(forall ((r Bool)(s X)) (and r p))",
				"A quantified expression is not allowed in the QF_UF logic");
	}
	
	@Test
	public void checkExists() {
		doCommand("(declare-sort X 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () X)");
		check("(exists ((r Bool)(s X)) (and r p))",
				"A quantified expression is not allowed in the QF_UF logic");
	}
	
	@Test
	public void checkNamed() {
		doCommand("(declare-sort X 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () X)");
		check("(and (! p :named P) (! (not p) :named Q))");
	}
	
	@Test
	public void checkBadNamed() {
		doCommand("(declare-sort X 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () X)");
		check("(and (! p :named P) (! (not t) :named Q))",
				"Unknown constant symbol t");
	}
	
	@Test
	public void checkGenericType() {
		doCommand("(declare-sort X 1)");
		doCommand("(declare-sort Y 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () (X Y))");
		doCommand("(declare-fun qb () (X Bool))");
		doCommand("(declare-fun r () Y)");
		doCommand("(declare-fun f (Y (X Y)) Bool)");
		doCommand("(declare-fun ff (Y (X Bool)) Bool)");
		check("(f r q)");
	}
	
	@Test
	public void checkGenericType2() {
		doCommand("(declare-sort X 1)");
		doCommand("(declare-sort Y 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () (X Y))");
		doCommand("(declare-fun qb () (X Bool))");
		doCommand("(declare-fun r () Y)");
		doCommand("(declare-fun f (Y (X Y)) Bool)");
		doCommand("(declare-fun ff (Y (X Bool)) (X Y))");
		check("(f r qb)",
				"Unknown predicate symbol f with argument types Y (X Bool)");
	}
	
	@Test
	public void checkGenericType3() {
		doCommand("(declare-sort X 1)");
		doCommand("(declare-sort Y 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () (X Y))");
		doCommand("(declare-fun qb () (X Bool))");
		doCommand("(declare-fun r () Y)");
		doCommand("(declare-fun f (Y X) Bool)","The sort symbol X expects 1 arguments, not 0");
	}
	
	@Test
	public void checkGenericType4() {
		doCommand("(declare-sort X 1)");
		doCommand("(declare-sort Y 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () (X Y))");
		doCommand("(declare-fun qb () (X Bool))");
		doCommand("(declare-fun r () Y)");
		doCommand("(declare-fun f (Y (X Y)) Bool)");
		doCommand("(declare-fun ff (Y (X Bool)) (X Y))");
		check("(f r (ff r qb))");
	}
	
	@Test
	public void checkGenericType5() {
		doCommand("(declare-sort X 1)");
		doCommand("(declare-sort Y 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () (X Y))");
		doCommand("(declare-fun qb () (X Bool))");
		doCommand("(declare-fun r () Y)");
		doCommand("(declare-fun f ((Y Y)) Bool)","The sort symbol Y expects 0 arguments, not 1");
	}
	
	@Test
	public void checkGenericType6() {
		doCommand("(declare-sort X 1)");
		doCommand("(declare-sort Y 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () (X Y))");
		doCommand("(declare-fun qb () (X Bool))");
		doCommand("(declare-fun r () Y)");
		doCommand("(declare-fun f () X)","The sort symbol X expects 1 arguments, not 0");
	}
	
	@Test
	public void checkTypeAbbrev() {
		doCommand("(declare-sort X 1)");
		doCommand("(declare-sort Y 0)");
		doCommand("(define-sort Z () (X Y))");
		doCommand("(declare-fun q () (X Y))");
		doCommand("(declare-fun qb () Z)");
		doCommand("(assert (= q qb))");
	}
	
	@Test
	public void checkTypeAbbrev1() {
		doCommand("(declare-sort X 1)");
		doCommand("(declare-sort Y 0)");
		doCommand("(define-sort Z (A) (X A))");
		doCommand("(declare-fun q () (X Y))");
		doCommand("(declare-fun qb () (Z Y))");
		doCommand("(assert (= q qb))");
	}
	
	@Test
	public void checkTypeAbbrev2() {
		doCommand("(declare-sort X 1)");
		doCommand("(declare-sort Y 0)");
		doCommand("(define-sort Z (A) (X A))");
		doCommand("(declare-fun q () (X Y))");
		doCommand("(declare-fun qb () (Z A))","No such sort symbol declared: A");
	}
	
	@Test
	public void checkTypeAbbrev3() {
		doCommand("(declare-sort X 1)");
		doCommand("(declare-sort Y 0)");
		doCommand("(define-sort Z (A) (X A))");
		doCommand("(declare-fun q () (X Y))");
		doCommand("(declare-fun qb () (Z Bool))");
		doCommand("(assert (= q qb))","Mismatched sorts of arguments: (X Y) vs. (Z Bool)");
	}
	

}
