package org.smtlib;

import org.junit.Before;
import org.junit.Test;


public class TypeCheckRealsInts extends TypeCheckRoot {

	@Before
	public void setup() {
		super.setup();
		checkResponse(solver.set_logic("AUFLIRA",null));
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
	

}
