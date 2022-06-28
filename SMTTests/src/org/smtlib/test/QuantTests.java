package org.smtlib.test;

import org.junit.Assume;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.ParameterizedWithNames;
import org.smtlib.IResponse;
import org.smtlib.SMT;
import org.smtlib.SMT.Configuration;
import org.smtlib.SMT.Configuration.SMTLIB;

@RunWith(ParameterizedWithNames.class)
public class QuantTests extends LogicTests {

    public QuantTests(String solvername, String version) {
    	this.solvername = solvername;
    	this.version = version;
    }
    
	@Override
	public IResponse doCommand(String input, String result) {
		return super.doCommand(input,(solvername.equals("test") ? "unknown" : result));
	}

	@Test
	public void checkQuantifiedTransSat() {
		Assume.assumeTrue(!"simplify".equals(solvername)); // FIXME - simplify does not implement Bool terms
		Assume.assumeTrue(!"yices2".equals(solvername)); // FIXME - yices2 does not implement quantifiers yet
		String result = "simplify".equals(solvername) || solvername.startsWith("z3_4") || "yices2".equals(solvername) ? "sat" : "unknown";
		doCommand("(set-logic UFLRA)");
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
		String result = "unsat";
		Assume.assumeTrue(!"simplify".equals(solvername)); // FIXME - simplify does not implement Bool terms
		Assume.assumeTrue(!"yices2".equals(solvername)); // FIXME - yices2 has a bug here as of Feb 2014
		//if ("z3_4_4".equals(solvername)) result = "unknown"; // FIXME - problem with Z3 4.4
		doCommand("(set-logic AUFLIA)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () Bool)");
		doCommand("(declare-fun r () Bool)");
		doCommand("(declare-fun f (Bool Bool) Bool)");
		doCommand("(assert (forall ((x Bool)(y Bool)(z Bool)) (=> (and (f x y) (f y z)) (f x z))))");
		doCommand("(assert (and (f p q) (f q r)))");
		doCommand("(assert (not (f p r)))");
		doCommand("(check-sat)",result);
		doCommand("(exit)");
	}

	@Test
	public void checkQuantifiedTransSatNT() {
		Assume.assumeTrue(!"yices2".equals(solvername)); // FIXME - yices2 does not implement quantifiers
		String result = "simplify".equals(solvername) || solvername.startsWith("z3_4") || "yices2".equals(solvername) ? "sat" : "unknown";
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
		//if ("z3_4_4".equals(solvername)) result = "unknown"; // FIXME - Z3 4.4 problem
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

		String result = "sat";
		String result2 = "unsat";
		if ("test".equals(solvername)) result = result2 = "unknown";
		//if ("z3_4_4".equals(solvername) && Configuration.isVersion(SMTLIB.V20)) result =  "unknown"; // FIXME - this case is non-deterministic
		if ("cvc4".equals(solvername)) result =  "unknown";
		if ("cvc4b".equals(solvername)) result = "unknown";
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
		Assume.assumeTrue(!"yices2".equals(solvername)); // FIXME - yices2 does not implement quantifiers yet
		String result = solvername.equals("z3_2_11") 
				|| solvername.equals("yices") 
				? "unknown" : "unsat";  // FIXME - unknown vs. unsat ?????
		doCommand("(set-logic UF)");
		doCommand("(assert (forall ((q Bool)) (not q)))");
		doCommand("(check-sat)",result);
		doCommand("(exit)");
	}

	@Test
	public void forallBoolSat2() {
		Assume.assumeTrue(!"simplify".equals(solvername)); // FIXME - simplify does not implement Bool terms
		Assume.assumeTrue(!"yices2".equals(solvername)); // FIXME - yices2 does not implement quantifiers yet
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
		Assume.assumeTrue(!"yices2".equals(solvername)); // FIXME - yices2 does not implement quantifiers yet
		String result = "sat";
		doCommand("(set-logic UFLRA)");
		doCommand("(assert (forall ((q Bool)) (or q (not q))))");
		doCommand("(check-sat)",result);
		doCommand("(exit)");
	}

	@Test
	public void existsBoolSat() {
		Assume.assumeTrue(!"simplify".equals(solvername)); // FIXME - simplify does not implement Bool terms
		Assume.assumeTrue(!"yices2".equals(solvername)); // FIXME - yices2 does not implement quantifiers yet
		doCommand("(set-logic UFLRA)");
		doCommand("(assert (exists ((q Bool)) (not q)))");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}


	@Test
	public void existsBoolUnSat() {
		Assume.assumeTrue(!"simplify".equals(solvername)); // FIXME - simplify does not implement Bool terms
		Assume.assumeTrue(!"yices2".equals(solvername)); // FIXME - yices2 does not implement quantifiers yet
		doCommand("(set-logic UFLRA)");
		doCommand("(assert (exists ((q Bool)) (and q (not q))))");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}

}
