package org.smtlib;

import org.junit.Before;
import org.junit.Test;

// FIXME - need to check complex sorts; parameterized definitions; Int and NUMERAL types; variadic functions; parameterized function sorts
// FIXME - need to implement checking of sort expressions

public class TypeCheckInt extends TypeCheckRoot {
	
	@Override
	@Before
	public void setup() {
		super.setup();
		checkResponse(solver.set_logic("AUFNIRA",null));
	}
	
	
	@Test
	public void checkFcnDef() {
		doCommand("(declare-fun q () Int)");
		doCommand("(declare-fun r () Int)");
		doCommand("(define-fun f ((a Int)(b Int)) Int (+ a b))");
		doCommand("(assert (= (f 1 2) 3))");
	}
	
	@Test
	public void checkFcnDef1() {
		doCommand("(declare-fun q () Int)");
		doCommand("(declare-fun r () Int)");
		doCommand("(define-fun f ((a Int)(b Int)) Int (+ a b))");
		doCommand("(assert (= (f 1 2) true))","Mismatched sorts of arguments: Int vs. Bool");
	}
	
	@Test
	public void checkFcnDef2() {
		doCommand("(define-sort Z () Int)");
		doCommand("(declare-fun q () Int)");
		doCommand("(declare-fun r () Int)");
		doCommand("(define-fun f ((a Int)(b Z)) Int (+ a b))");
		doCommand("(assert (= (f 1 2) true))","Mismatched sorts of arguments: Int vs. Bool");
	}
	

}
