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
		// That validation only runs for adapters that resolve a logic's theory
		// definitions locally (e.g. Solver_test/Solver_simplify, both ultimately via
		// Solver_test's TypeChecker-driven set_logic) -- solvers below just forward
		// "(set-logic QF_UF)" straight to their own real process (no local override),
		// which accepts it without jSMTLIB ever needing to open a logic-definition
		// file, so a broken logicPath is never actually consulted for them. Confirmed
		// directly for bitwuzla (same forward-only set_logic as cvc5/yices2/z3/
		// smtinterpol): identical "success" outcome with this same broken path.
		doCommand("(set-logic QF_UF)",
				solvername.startsWith("z3") || solvername.startsWith("cvc5") || solvername.startsWith("yices2") || solvername.startsWith("z3_4_4") || solvername.startsWith("smtinterpol") || solvername.startsWith("bitwuzla")? "success" : // FIXME
				smt.smtConfig.isVersion(SMTLIB.V20) ? "(error \"Invalid logic path: \\\"xxx\\\" is not a directory\")"
		                                                : "(error \"Invalid logic path: \"\"xxx\"\" is not a directory\")");
	}
}
