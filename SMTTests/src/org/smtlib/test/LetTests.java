package org.smtlib.test;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.ParameterizedWithNames;
import org.smtlib.IResponse;

@RunWith(ParameterizedWithNames.class)
public class LetTests extends LogicTests {

    public LetTests(String solvername, String version) {
    	this.solvername = solvername;
    }
    
	@Override
	public IResponse doCommand(String input, String result) {
		return super.doCommand(input,(solvername.equals("test") ? "unknown" : result));
	}

	@Test
	public void checkLetBool() {
		doCommand("(set-logic QF_UF)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(assert (let ((x p)(y (not p))) (= x (not y)) ))");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}

	@Test
	public void checkLetBool2() {
		doCommand("(set-logic QF_UF)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(assert (let ((x p)(y (not p))) (= x y) ))");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}

	@Test
	public void checkLetInt() {
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun c () Int)");
		doCommand("(assert (let ((x 5)(y (+ c 1)) (z (- c 1))) (= (- y z) 2)))");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}

	@Test
	public void checkLetInt2() {
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun c () Int)");
		doCommand("(assert (let ((x 5)(y (+ c 1)) (z (- c 1))) (= (- y z) 3)))");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}
	
	// TODO: let as a term
	// TODO: let inside a quantifier

}
