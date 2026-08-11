package org.smtlib.test;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.ParameterizedWithNames;
import org.smtlib.SMT;
import org.smtlib.SMT.Configuration.SMTLIB;

@RunWith(ParameterizedWithNames.class)
public class LogicsBadPath extends LogicTests {

	@Override
	public void init() {
		super.init();
		smt.smtConfig.logicPath = "xxx";
	}

    public LogicsBadPath(String solver, String version) {
    	solvername = solver;
    	this.version = version;
    }

	@Test
	public void testLogic() {
		// "xxx" is not a real directory, so this is caught by the upfront logic-path
		// validation in Utils.openLogicStream -- before any classpath fallback is tried.
		doCommand("(set-logic QF_UF)",
				solvername.startsWith("z3") || solvername.startsWith("cvc5") || solvername.startsWith("yices2") || solvername.startsWith("z3_4_4")? "success" : // FIXME
				smt.smtConfig.isVersion(SMTLIB.V20) ? "(error \"Invalid logic path: \\\"xxx\\\" is not a directory\")"
		                                                : "(error \"Invalid logic path: \"\"xxx\"\" is not a directory\")");
	}
}
