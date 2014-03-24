package org.smtlib;

import org.junit.Before;
import org.junit.Test;

public class TypeCheckQuantifiers extends TypeCheckRoot {


	@Override
	@Before
	public void setup() {
		super.setup();
		checkResponse(solver.set_logic("AUFNIRA",null)); // Any logic that allows quantifiers
	}
	
	@Test
	public void checkForall() {
		doCommand("(declare-sort X 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () X)");
		check("(forall ((r Bool)(s X)) (and r p))");
	}
	
	@Test
	public void checkBadForall() {
		doCommand("(declare-sort X 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () X)");
		check("(forall ((r Bool)(s X)) (and s t))","Unknown constant symbol t");
	}
	
	@Test
	public void checkExists() {
		doCommand("(declare-sort X 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () X)");
		check("(exists ((r Bool)(s X)) (and r p))");
	}
	
	@Test
	public void checkBadExists() {
		doCommand("(declare-sort X 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () X)");
		check("(exists ((r Bool)(s X)) (or (and s q) t))",
				"Unknown predicate symbol and with argument types X X",
				"Unknown constant symbol t");
	}
	

}
