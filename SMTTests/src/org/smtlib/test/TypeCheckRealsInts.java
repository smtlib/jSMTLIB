package org.smtlib.test;

import org.junit.Before;
import org.junit.Test;


public class TypeCheckRealsInts extends TypeCheckRoot {

	@Override
	@Before
	public void setup() {
		super.setup();
		checkResponse(solver.set_logic("AUFNIRA",null));
	}
	
	@Test
	public void checkOverload() {
		doCommand("(declare-fun q () Int)");
		doCommand("(declare-fun r () Int)");
		doCommand("(declare-fun a () Real)");
		doCommand("(declare-fun b () Real)");
		doCommand("(assert (>= a b))");
		doCommand("(assert (>= q r))");
		doCommand("(assert (<= a b))");
		doCommand("(assert (<= q r))");
		doCommand("(assert (> a b))");
		doCommand("(assert (> q r))");
		doCommand("(assert (< a b))");
		doCommand("(assert (< q r))");
	}

	/** Exercises the Int-to-Real coercion paths in TypeChecker: the =/distinct
	 * argument-sort-matching loop, and the generic-operator symbol-table lookup
	 * fallback (an Int argument mixed with a Real argument in the same call). */
	@Test
	public void checkIntRealCoercion() {
		doCommand("(declare-fun q () Int)");
		doCommand("(declare-fun a () Real)");
		doCommand("(assert (= a q))");
		doCommand("(assert (= q a))");
		doCommand("(assert (>= a q))");
		doCommand("(assert (>= q a))");
	}

}
