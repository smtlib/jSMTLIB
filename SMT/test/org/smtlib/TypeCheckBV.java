package org.smtlib;

import org.junit.Before;
import org.junit.Test;


public class TypeCheckBV extends TypeCheckRoot {
	
	@Override
	@Before
	public void setup() {
		super.setup();
		checkResponse(solver.set_logic("QF_BV",null));
	}
	
	@Test
	public void checkFunctions() {
		doCommand("(declare-fun a () (_ BitVec 8))");
		doCommand("(declare-fun q () (_ BitVec 5))");
		doCommand("(declare-fun r () (_ BitVec 3))");
		doCommand("(declare-fun z () (_ BitVec 1))");
		doCommand("(assert (bvult a a))");
		// Add ok and err cases for all bit-vector functions
	}
	

}
