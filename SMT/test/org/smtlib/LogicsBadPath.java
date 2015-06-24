package org.smtlib;

import org.junit.Test;
import org.junit.runner.RunWith;

import tests.ParameterizedIgnorable;

@RunWith(ParameterizedIgnorable.class)
public class LogicsBadPath extends LogicTests {

	@Override
	public void init() {
		super.init();
		smt.smtConfig.logicPath = "xxx";
	}

    public LogicsBadPath(String solver) {
    	solvername = solver;
    }

	@Test
	public void testLogic() {
		doCommand("(set-logic QF_UF)",
				solvername.startsWith("z3") || solvername.startsWith("cvc4")? "success" : // FIXME
				"(error \"No logic file found for QF_UF on path \\\"xxx\\\"\")");
	}
}
