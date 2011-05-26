package org.smtlib;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public class QuantTests extends LogicTests {

	// FIXME - should use a different logic since these have quantifiers
	
    public QuantTests(String solvername) {
    	this.solvername = solvername;
    }
    
	public IResponse doCommand(String input, String result) {
		return super.doCommand(input,(solvername.equals("test") ? "unknown" : result));
	}

	@Test
	public void checkQuantifiedTransSat() {
		String result = "simplify".equals(solvername) ? "sat" : "unknown";
		doCommand("(set-logic AUFNIRA)");
		doCommand("(declare_fun p () Bool)");
		doCommand("(declare_fun q () Bool)");
		doCommand("(declare_fun r () Bool)");
		doCommand("(declare_fun f (Bool Bool) Bool)");
		doCommand("(assert (forall ((x Bool)(y Bool)(z Bool)) (=> (and (f x y) (f y z)) (f x z))))");
		doCommand("(assert (and (f p q) (f q r)))");
		doCommand("(assert (f p r))");
		doCommand("(check-sat)",result); // FIXME - why is this not sat
		doCommand("(exit)");
	}

	@Test
	public void checkQuantifiedTransUnsat() {
		doCommand("(set-logic AUFNIRA)");
		doCommand("(declare_fun p () Bool)");
		doCommand("(declare_fun q () Bool)");
		doCommand("(declare_fun r () Bool)");
		doCommand("(declare_fun f (Bool Bool) Bool)");
		doCommand("(assert (forall ((x Bool)(y Bool)(z Bool)) (=> (and (f x y) (f y z)) (f x z))))");
		doCommand("(assert (and (f p q) (f q r)))");
		doCommand("(assert (not (f p r)))");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}

	@Test
	public void checkQuantifiedTransSatNT() {
		String result = "simplify".equals(solvername) ? "sat" : "unknown";
		doCommand("(set-logic AUFNIRA)");
		doCommand("(declare-sort B 0)");
		doCommand("(declare_fun p () B)");
		doCommand("(declare_fun q () B)");
		doCommand("(declare_fun r () B)");
		doCommand("(declare_fun f (B B) Bool)");
		doCommand("(assert (forall ((x B)(y B)(z B)) (=> (and (f x y) (f y z)) (f x z))))");
		doCommand("(assert (and (f p q) (f q r)))");
		doCommand("(assert (f p r))");
		doCommand("(check-sat)",result); // FIXME - why is this not sat
		doCommand("(exit)");
	}

	@Test
	public void checkQuantifiedTransUnSatNT() {
		doCommand("(set-logic AUFNIRA)");
		doCommand("(declare-sort B 0)");
		doCommand("(declare_fun p () B)");
		doCommand("(declare_fun q () B)");
		doCommand("(declare_fun r () B)");
		doCommand("(declare_fun f (B B) Bool)");
		doCommand("(assert (forall ((x B)(y B)(z B)) (=> (and (f x y) (f y z)) (f x z))))");
		doCommand("(assert (and (f p q) (f q r)))");
		doCommand("(assert (not (f p r)))");
		doCommand("(check-sat)","unsat"); // FIXME - why is this not sat
		doCommand("(exit)");
	}

	@Test
	public void checkQuantifiedTransBool() {
		String result = "simplify".equals(solvername) ? "sat" : "unknown";
		String result2 = "simplify".equals(solvername) ? "unsat" : "unsat";
		doCommand("(set-logic AUFNIRA)");
		doCommand("(declare_fun p () Bool)");
		doCommand("(declare_fun q () Bool)");
		doCommand("(declare_fun r () Bool)");
		doCommand("(declare_fun f (Bool Bool) Bool)");
		doCommand("(assert (forall ((x Bool)(y Bool)(z Bool)) (=> (and (f x y) (f y z)) (f x z))))");
		doCommand("(assert (and (f p q) (f q r)))");
		doCommand("(push 1)");
		doCommand("(assert (f p r))");
		doCommand("(check-sat)",result);
		doCommand("(pop 1)");
		doCommand("(assert (not (f p r)))");
		doCommand("(check-sat)",result2); // FIXME - yices fails on this, producing unknown, although the equivalent problem in checkQuantifiedTransUnsat is OK
		doCommand("(exit)");
	}


	@Test
	public void existsIntSat() {
		doCommand("(set-logic AUFNIRA)");
		doCommand("(assert (exists ((x Int)) (and (<= 1 x)(<= x 3))))");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}

	@Test
	public void existsIntUnSat() {
		doCommand("(set-logic AUFNIRA)");
		doCommand("(assert (exists ((x Int)) (and (<= 4 x) (<= x 3))  ))");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}

// FIXME
//	@Test
//	public void forallBoolUnSat() {
//		doCommand("(set-logic QF_LIA)");
//		doCommand("(assert (forall ((q Bool)) (not q)))"); // false
//		doCommand("(check-sat)","unknown");
//		doCommand("(exit)");
//	}
//
//	@Test
//	public void forallBoolSat2() {
//		doCommand("(set-logic QF_LIA)");
//		doCommand("(declare-fun p () Bool)");
//		doCommand("(assert (not (forall ((q Bool)) (not q))))"); // true
//		doCommand("(check-sat)","sat");
//		doCommand("(exit)");
//	}

	@Test
	public void forallBoolSat() {
		doCommand("(set-logic AUFNIRA)");
		doCommand("(assert (forall ((q Bool)) (or q (not q))))");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}

	@Test
	public void existsBoolSat() {
		doCommand("(set-logic AUFNIRA)");
		doCommand("(assert (exists ((q Bool)) (not q)))");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}


	@Test
	public void existsBoolUnSat() {
		doCommand("(set-logic AUFNIRA)");
		doCommand("(assert (exists ((q Bool)) (and q (not q))))");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}

}
