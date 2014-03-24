package org.smtlib;

import org.junit.Assume;
import org.junit.Test;
import org.junit.runner.RunWith;
import tests.*;

@RunWith(ParameterizedIgnorable.class)
public class QuantTests extends LogicTests {

    public QuantTests(String solvername) {
    	this.solvername = solvername;
    }
    
	@Override
	public IResponse doCommand(String input, String result) {
		return super.doCommand(input,(solvername.equals("test") ? "unknown" : result));
	}

	@Test
	public void checkQuantifiedTransSat() {
		Assume.assumeTrue(!"simplify".equals(solvername)); // FIXME - simplify does not implement Bool terms
		String result = "simplify".equals(solvername) || "z3_4_3".equals(solvername) || "yices2".equals(solvername) ? "sat" : "unknown";
		doCommand("(set-logic AUFLIA)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () Bool)");
		doCommand("(declare-fun r () Bool)");
		doCommand("(declare-fun f (Bool Bool) Bool)");
		doCommand("(assert (forall ((x Bool)(y Bool)(z Bool)) (=> (and (f x y) (f y z)) (f x z))))");
		doCommand("(assert (and (f p q) (f q r)))");
		doCommand("(assert (f p r))");
		doCommand("(check-sat)",result);
		doCommand("(exit)");
	}

	@Test
	public void checkQuantifiedTransUnsat() {
		Assume.assumeTrue(!"simplify".equals(solvername)); // FIXME - simplify does not implement Bool terms
		Assume.assumeTrue(!"yices2".equals(solvername)); // FIXME - yices2 has a bug here as of Feb 2014
		doCommand("(set-logic AUFLIA)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () Bool)");
		doCommand("(declare-fun r () Bool)");
		doCommand("(declare-fun f (Bool Bool) Bool)");
		doCommand("(assert (forall ((x Bool)(y Bool)(z Bool)) (=> (and (f x y) (f y z)) (f x z))))");
		doCommand("(assert (and (f p q) (f q r)))");
		doCommand("(assert (not (f p r)))");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}

	@Test
	public void checkQuantifiedTransSatNT() {
		Assume.assumeTrue(!"yices2".equals(solvername)); // FIXME - yices2 does not implement quantifiers
		String result = "simplify".equals(solvername) || "z3_4_3".equals(solvername)  || "yices2".equals(solvername) ? "sat" : "unknown";
		doCommand("(set-logic AUFLIA)");
		doCommand("(declare-sort B 0)");
		doCommand("(declare-fun p () B)");
		doCommand("(declare-fun q () B)");
		doCommand("(declare-fun r () B)");
		doCommand("(declare-fun f (B B) Bool)");
		doCommand("(assert (forall ((x B)(y B)(z B)) (=> (and (f x y) (f y z)) (f x z))))");
		doCommand("(assert (and (f p q) (f q r)))");
		doCommand("(assert (f p r))");
		doCommand("(check-sat)",result);
		doCommand("(exit)");
	}

	@Test
	public void checkQuantifiedTransUnSatNT() {
		Assume.assumeTrue(!"yices2".equals(solvername)); // FIXME - yices2 does not implement quantifiers as terms
		String result = "test".equals(solvername) ? "unknown" : "unsat";
		doCommand("(set-logic AUFLIA)");
		doCommand("(declare-sort B 0)");
		doCommand("(declare-fun p () B)");
		doCommand("(declare-fun q () B)");
		doCommand("(declare-fun r () B)");
		doCommand("(declare-fun f (B B) Bool)");
		doCommand("(assert (forall ((x B)(y B)(z B)) (=> (and (f x y) (f y z)) (f x z))))");
		doCommand("(assert (and (f p q) (f q r)))");
		doCommand("(assert (not (f p r)))");
		doCommand("(check-sat)",result);
		doCommand("(exit)");
	}

	@Test
	public void checkQuantifiedTransBool() {
		Assume.assumeTrue(!"simplify".equals(solvername)); // FIXME - simplify does not implement Bool terms
		Assume.assumeTrue(!"yices2".equals(solvername));  // FIXME - yices crashes

		String result = "simplify".equals(solvername) || "z3_4_3".equals(solvername) || "yices2".equals(solvername)? "sat" : "unknown";
		String result2 = "unsat";
		doCommand("(set-logic AUFLIA)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () Bool)");
		doCommand("(declare-fun r () Bool)");
		doCommand("(declare-fun f (Bool Bool) Bool)");
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
		Assume.assumeTrue(!"yices2".equals(solvername)); // FIXME - yices2 does not implement quantifiers
		doCommand("(set-logic AUFLIA)");
		doCommand("(assert (exists ((x Int)) (and (<= 1 x)(<= x 3))))");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}

	@Test
	public void existsIntUnSat() {
		Assume.assumeTrue(!"yices2".equals(solvername)); // FIXME - yices2 does not implement quantifiers
		String result = "unsat";
		doCommand("(set-logic AUFLIA)");
		doCommand("(assert (exists ((x Int)) (and (<= 4 x) (<= x 3))  ))");
		doCommand("(check-sat)",result);
		doCommand("(exit)");
	}

 
	@Test
	public void forallBoolUnSat() {
		Assume.assumeTrue(!"simplify".equals(solvername)); // FIXME - simplify does not implement Bool terms
		//Assume.assumeTrue(!"yices2".equals(solvername)); // FIXME - yices2 does not implement Boolean quantifiers
		String result = solvername.equals("z3_2_11") 
				|| solvername.equals("yices") 
				|| solvername.equals("cvc4") 
				? "unknown" : "unsat";
		doCommand("(set-logic AUFLIA)");
		doCommand("(assert (forall ((q Bool)) (not q)))");
		doCommand("(check-sat)",result);
		doCommand("(exit)");
	}

	@Test
	public void forallBoolSat2() {
		Assume.assumeTrue(!"simplify".equals(solvername)); // FIXME - simplify does not implement Bool terms
		Assume.assumeTrue(!"yices2".equals(solvername)); // FIXME - yices2 does not implement Boolean quantifiers
		String result = "sat";
		doCommand("(set-logic AUFLIA)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(assert (not (forall ((q Bool)) (not q))))"); // true
		doCommand("(check-sat)",result);
		doCommand("(exit)");
	}

	@Test
	public void forallBoolSat() {
		Assume.assumeTrue(!"simplify".equals(solvername)); // FIXME - simplify does not implement Bool terms
		String result = solvername.equals("cvc4") 
				? "unknown" : "sat";
		doCommand("(set-logic AUFLIA)");
		doCommand("(assert (forall ((q Bool)) (or q (not q))))");
		doCommand("(check-sat)",result);
		doCommand("(exit)");
	}

	@Test
	public void existsBoolSat() {
		Assume.assumeTrue(!"simplify".equals(solvername)); // FIXME - simplify does not implement Bool terms
		//Assume.assumeTrue(!"yices2".equals(solvername)); // FIXME - yices2 does not implement Boolean quantifiers
		doCommand("(set-logic AUFLIA)");
		doCommand("(assert (exists ((q Bool)) (not q)))");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}


	@Test
	public void existsBoolUnSat() {
		Assume.assumeTrue(!"simplify".equals(solvername)); // FIXME - simplify does not implement Bool terms
		doCommand("(set-logic AUFLIA)");
		doCommand("(assert (exists ((q Bool)) (and q (not q))))");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}

}
