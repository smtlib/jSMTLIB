package org.smtlib;

import java.util.Iterator;
import java.util.List;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.smtlib.IPos.ISource;
import org.smtlib.solvers.Solver_test;

// FIXME - need to check complex sorts; parameterized definitions; Int and NUMERAL types; variadic functions; parameterized function sorts
// FIXME - need to implement checking of sort expressions

public class TypeCheckInt extends TypeCheckRoot {
	
	@Before
	public void setup() {
		super.setup();
		checkResponse(solver.set_logic("QF_LIA",null));
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
