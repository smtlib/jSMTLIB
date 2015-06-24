package org.smtlib;

import org.junit.Assume;
import org.junit.Test;
import org.junit.runner.RunWith;

import tests.ParameterizedIgnorable;

@RunWith(ParameterizedIgnorable.class)
public class SatChecks extends LogicTests {

    public SatChecks(String solvername) {
    	this.solvername = solvername;
    }

	@Override
	public IResponse doCommand(String input, String result) {
		return super.doCommand(input,(solvername.equals("test") ? "unknown" : result));
	}

	@Test
	public void checkTransSat() {
		String result = "sat";
		doCommand("(set-logic QF_UF)");
		doCommand("(declare-fun x () Bool)");
		doCommand("(declare-fun y () Bool)");
		doCommand("(declare-fun z () Bool)");
		doCommand("(assert (and (=> x y) (=> y z)))");
		doCommand("(assert x)");
		doCommand("(assert z)");
		doCommand("(check-sat)",result);
		doCommand("(exit)");
	}

	@Test
	public void checkTransUnsat() {
		String result = "unsat";
		doCommand("(set-logic QF_UF)");
		doCommand("(declare-fun x () Bool)");
		doCommand("(declare-fun y () Bool)");
		doCommand("(declare-fun z () Bool)");
		doCommand("(assert (and (=> x y) (=> y z)))");
		doCommand("(assert x)");
		doCommand("(assert (not z))");
		doCommand("(check-sat)",result);
		doCommand("(exit)");
	}

	@Test
	public void checkXorSat() {
		doCommand("(set-logic QF_UF)");
		doCommand("(declare-fun x () Bool)");
		doCommand("(declare-fun y () Bool)");
		doCommand("(declare-fun z () Bool)");
		doCommand("(assert (xor x y))");
		doCommand("(assert x)");
		doCommand("(assert (not y))");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}

	@Test
	public void checkXorUnsat() {
		doCommand("(set-logic QF_UF)");
		doCommand("(declare-fun x () Bool)");
		doCommand("(declare-fun y () Bool)");
		doCommand("(declare-fun z () Bool)");
		doCommand("(assert (xor x y))");
		doCommand("(assert x)");
		doCommand("(assert y)");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}
	
	@Test
	public void checkXor3UnSat() {
		doCommand("(set-logic QF_UF)");
		doCommand("(declare-fun x () Bool)");
		doCommand("(declare-fun y () Bool)");
		doCommand("(declare-fun z () Bool)");
		doCommand("(assert (xor x y z))");
		doCommand("(assert x)");
		doCommand("(assert (not y))");
		doCommand("(assert z)");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}

	@Test
	public void checkXor3sat() {
		doCommand("(set-logic QF_UF)");
		doCommand("(declare-fun x () Bool)");
		doCommand("(declare-fun y () Bool)");
		doCommand("(declare-fun z () Bool)");
		doCommand("(assert (xor x y z))");
		doCommand("(assert x)");
		doCommand("(assert (not y))");
		doCommand("(assert (not z))");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}

	@Test
	public void checkLIASat() {
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun x () Int)");
		doCommand("(declare-fun y () Int)");
		doCommand("(declare-fun z () Int)");
		doCommand("(assert (= x (+ y 1)))");
		doCommand("(assert (= z (- y 2)))");
		doCommand("(assert (= x 4))");
		doCommand("(assert (= z 1))");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}

	@Test
	public void checkLIAUnsat() {
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun x () Int)");
		doCommand("(declare-fun y () Int)");
		doCommand("(declare-fun z () Int)");
		doCommand("(assert (= x (+ y 1)))");
		doCommand("(assert (= z (- y 2)))");
		doCommand("(assert (= x 4))");
		doCommand("(assert (= z 2))");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}

	@Test
	public void checkLIADistinct3Sat() {
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun x () Int)");
		doCommand("(declare-fun y () Int)");
		doCommand("(declare-fun z () Int)");
		doCommand("(declare-fun m () Int)");
		doCommand("(assert (and (> x 1) (> m x)))");
		doCommand("(assert (and (> y 1) (> m y)))");
		doCommand("(assert (and (> z 1) (> m z)))");
		doCommand("(assert (distinct x y z))");
		doCommand("(assert (= m 5))");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}

	@Test
	public void checkLIADistinctUnSat() {
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun x () Int)");
		doCommand("(declare-fun y () Int)");
		doCommand("(declare-fun z () Int)");
		doCommand("(assert (= x (+ y 1)))");
		doCommand("(assert (= z (- y 2)))");
		doCommand("(assert (= x 4))");
		doCommand("(assert (distinct z 1))");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}

	@Test
	public void checkLIADistinct3UnSat() {
		Assume.assumeTrue(!"simplify".equals(solvername)); // FIXME - simplify gets this one wrong
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun x () Int)");
		doCommand("(declare-fun y () Int)");
		doCommand("(declare-fun z () Int)");
		doCommand("(declare-fun m () Int)");
		doCommand("(assert (and (> x 1) (> m x)))");
		doCommand("(assert (and (> y 1) (> m y)))");
		doCommand("(assert (and (> z 1) (> m z)))");
		doCommand("(assert (distinct x y z))");
		doCommand("(assert (= m 4))");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}

	@Test
	public void checkLIADistinct3UnSatB() {
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun x () Int)");
		doCommand("(declare-fun y () Int)");
		doCommand("(declare-fun z () Int)");
		doCommand("(declare-fun m () Int)");
		doCommand("(assert (and (> x 1) (> y x)))");
		doCommand("(assert (and (> y 1) (> z y)))");
		doCommand("(assert (and (> z 1) (> m z)))");
		doCommand("(assert (distinct x y z))");
		doCommand("(assert (= m 4))");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}
	
	@Test
	public void add3argsSat() {
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun x () Int)");
		doCommand("(declare-fun y () Int)");
		doCommand("(assert (= x (+ 1 2 3)))");
		doCommand("(assert (= x 6)))");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}

	@Test
	public void add3argsUnSat() {
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun x () Int)");
		doCommand("(declare-fun y () Int)");
		doCommand("(assert (= x (+ 1 2 3)))");
		doCommand("(assert (= x 7)))");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}

	@Test
	public void negativeUnSat() {
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun x () Int)");
		doCommand("(declare-fun y () Int)");
		doCommand("(assert (distinct 0 (+ x (- x))))");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}

	@Test
	public void minus3argsSat() {
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun x () Int)");
		doCommand("(declare-fun y () Int)");
		doCommand("(assert (= x (- 3 2 1)))");
		doCommand("(assert (= x 0)))");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}

	@Test
	public void minus3argsUnSat() {
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun x () Int)");
		doCommand("(declare-fun y () Int)");
		doCommand("(assert (= x (- 8 4 2)))");
		doCommand("(assert (= x 3)))");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}

	@Test
	public void mult3argsSat() {
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun x () Int)");
		doCommand("(declare-fun y () Int)");
		doCommand("(assert (= x (* 1 2 3)))");
		doCommand("(assert (= x 6)))");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}

	@Test
	public void mult3argsUnSat() {
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun x () Int)");
		doCommand("(declare-fun y () Int)");
		doCommand("(assert (= x (* 1 2 3)))");
		doCommand("(assert (= x 7)))");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}

	// These work only for simplify
	
	@Test
	public void chainedLTunsat() {
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun x () Int)");
		doCommand("(declare-fun y () Int)");
		doCommand("(assert (< 1 x y 4))");
		doCommand("(assert (= x y))");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}

	@Test
	public void chainedLTsat() {
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun x () Int)");
		doCommand("(declare-fun y () Int)");
		doCommand("(assert (< 1 x y 4))");
		doCommand("(assert (= x 2))");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}

	@Test
	public void chainedGTunsat() {
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun x () Int)");
		doCommand("(declare-fun y () Int)");
		doCommand("(assert (> 4 x y 1))");
		doCommand("(assert (= x y))");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}

	@Test
	public void chainedGTsat() {
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun x () Int)");
		doCommand("(declare-fun y () Int)");
		doCommand("(assert (> 4 x y 1))");
		doCommand("(assert (= x 3))");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}
	
	@Test
	public void chainedLEunsat() {
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun x () Int)");
		doCommand("(declare-fun y () Int)");
		doCommand("(assert (<= 1 x y 4))");
		doCommand("(assert (> x y))");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}

	@Test
	public void chainedLEsat() {
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun x () Int)");
		doCommand("(declare-fun y () Int)");
		doCommand("(assert (<= 1 x y 4))");
		doCommand("(assert (= x 2))");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}

	@Test
	public void chainedGEunsat() {
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun x () Int)");
		doCommand("(declare-fun y () Int)");
		doCommand("(assert (>= 4 x y 1))");
		doCommand("(assert (< x y))");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}

	@Test
	public void chainedGEsat() {
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun x () Int)");
		doCommand("(declare-fun y () Int)");
		doCommand("(assert (>= 4 x y 1))");
		doCommand("(assert (= x 3))");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}

	@Test
	public void chainedEQunsat() {
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun x () Int)");
		doCommand("(declare-fun y () Int)");
		doCommand("(declare-fun z () Int)");
		doCommand("(assert (= z x y ))");
		doCommand("(assert (distinct z y))");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}

	@Test
	public void chainedEQsat() {
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun x () Int)");
		doCommand("(declare-fun y () Int)");
		doCommand("(declare-fun z () Int)");
		doCommand("(assert (= x y z))");
		doCommand("(assert (= x 3))");
		doCommand("(assert (= z 3))");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}

	
	@Test
	public void checkor3Sat() {
		doCommand("(set-logic QF_UF)");
		doCommand("(declare-fun x () Bool)");
		doCommand("(declare-fun y () Bool)");
		doCommand("(declare-fun z () Bool)");
		doCommand("(assert (or x y z))");
		doCommand("(assert x)");
		doCommand("(assert (not y))");
		doCommand("(assert (not z))");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}

	@Test
	public void checkor3Unsat() {
		doCommand("(set-logic QF_UF)");
		doCommand("(declare-fun x () Bool)");
		doCommand("(declare-fun y () Bool)");
		doCommand("(declare-fun z () Bool)");
		doCommand("(assert (or x y z))");
		doCommand("(assert (not x))");
		doCommand("(assert (not y))");
		doCommand("(assert (not z))");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}

	@Test
	public void checkand3Sat() {
		doCommand("(set-logic QF_UF)");
		doCommand("(declare-fun x () Bool)");
		doCommand("(declare-fun y () Bool)");
		doCommand("(declare-fun z () Bool)");
		doCommand("(assert (and x y z))");
		doCommand("(assert z)");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}

	@Test
	public void checkand3Unsat() {
		doCommand("(set-logic QF_UF)");
		doCommand("(declare-fun x () Bool)");
		doCommand("(declare-fun y () Bool)");
		doCommand("(declare-fun z () Bool)");
		doCommand("(assert (and x y z))");
		doCommand("(assert (not z))");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}

	@Test
	public void impliesIsRightAssoc() {
		doCommand("(set-logic QF_UF)");
		doCommand("(declare-fun x () Bool)");
		doCommand("(declare-fun y () Bool)");
		doCommand("(declare-fun z () Bool)");
		doCommand("(assert (=> x y z))");
		doCommand("(assert (not x))");
		doCommand("(assert (not z))");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}

	@Test
	public void impliesIsRightAssoc2() {
		doCommand("(set-logic QF_UF)");
		doCommand("(declare-fun x () Bool)");
		doCommand("(declare-fun y () Bool)");
		doCommand("(declare-fun z () Bool)");
		doCommand("(assert (=> x y z))");
		doCommand("(assert (not y))");
		doCommand("(assert x)");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}

	@Test
	public void impliesIsRightAssoc3() {
		doCommand("(set-logic QF_UF)");
		doCommand("(declare-fun x () Bool)");
		doCommand("(declare-fun y () Bool)");
		doCommand("(declare-fun z () Bool)");
		doCommand("(assert (=> x y z))");
		doCommand("(assert (not z))");
		doCommand("(assert x)");
		doCommand("(assert y)");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}
/*	     left-assoc		right-assoc		chained
		(x => y) => z   x => (y => z)  (x =>y) & (y => z)
TTT		T				T				T
TTF		F				F				F
TFT		T				T				F **
TFF		T				T				F **
FTT		T				T				T
FTF		F				T				F *
FFT		T				T				T
FFF		F				T				T *
*/
	

	@Test
	public void distinctBool() {
		doCommand("(set-logic QF_UF)");
		doCommand("(declare-fun x () Bool)");
		doCommand("(declare-fun y () Bool)");
		doCommand("(declare-fun z () Bool)");
		doCommand("(assert (distinct x y ))");
		doCommand("(assert x)");
		doCommand("(assert y)");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}

	@Test
	public void distinctBoolSat() {
		doCommand("(set-logic QF_UF)");
		doCommand("(declare-fun x () Bool)");
		doCommand("(declare-fun y () Bool)");
		doCommand("(declare-fun z () Bool)");
		doCommand("(assert (distinct x y ))");
		doCommand("(assert x)");
		doCommand("(assert (not y))");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}

	@Test
	public void distinctBool3() {
		doCommand("(set-logic QF_UF)");
		doCommand("(declare-fun x () Bool)");
		doCommand("(declare-fun y () Bool)");
		doCommand("(declare-fun z () Bool)");
		doCommand("(assert (distinct x y z))");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}

	@Test
	public void eqBool() {
		doCommand("(set-logic QF_UF)");
		doCommand("(declare-fun x () Bool)");
		doCommand("(declare-fun y () Bool)");
		doCommand("(declare-fun z () Bool)");
		doCommand("(assert (= x y ))");
		doCommand("(assert x)");
		doCommand("(assert (not y))");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}

	@Test
	public void eqBoolSat() {
		doCommand("(set-logic QF_UF)");
		doCommand("(declare-fun x () Bool)");
		doCommand("(declare-fun y () Bool)");
		doCommand("(declare-fun z () Bool)");
		doCommand("(assert (= x y ))");
		doCommand("(assert (not x))");
		doCommand("(assert (not y))");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}

	@Test
	public void eqBool3() {
		doCommand("(set-logic QF_UF)");
		doCommand("(declare-fun x () Bool)");
		doCommand("(declare-fun y () Bool)");
		doCommand("(declare-fun z () Bool)");
		doCommand("(assert (= x y z))");
		doCommand("(assert (not x))");
		doCommand("(assert z)");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}

	@Test
	public void eqBool3Sat() {
		doCommand("(set-logic QF_UF)");
		doCommand("(declare-fun x () Bool)");
		doCommand("(declare-fun y () Bool)");
		doCommand("(declare-fun z () Bool)");
		doCommand("(assert (= x y z))");
		doCommand("(assert (not x))");
		doCommand("(assert (not z))");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}


	@Test
	public void iteBoolSat() {
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun x () Int)");
		doCommand("(declare-fun y () Int)");
		doCommand("(assert (ite p (and (> x 0) (< x 0)) (= x 0)))");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}

	@Test
	public void iteBoolUnSat() {
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun x () Int)");
		doCommand("(declare-fun y () Int)");
		doCommand("(assert (ite p (and (> x 0) (< x 0)) (and (< x y)(> x y)) ))");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}

	@Test
	public void iteBoolBoolSat() {
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun x () Bool)");
		doCommand("(declare-fun y () Bool)");
		doCommand("(assert (ite p (and x (not x)) y))");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}

	// FIXME - in these four, simplify does not implement ite
	@Test
	public void iteBoolBoolUnSat() {
		if ("simplify".equals(solver)) return;
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun x () Bool)");
		doCommand("(declare-fun y () Bool)");
		doCommand("(assert (ite p (and x (not x)) (and y (not y)) ))");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}
	
	@Test
	public void iteTermSat() {
		Assume.assumeTrue(!"simplify".equals(solvername)); // FIXME - simplify does not allow Boolean terms
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun x () Int)");
		doCommand("(declare-fun y () Int)");
		doCommand("(assert (= (+ 1 (ite p x (+ x 2))) 7  ))");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}
	
	@Test
	public void iteTermSat2() {
		Assume.assumeTrue(!"simplify".equals(solvername)); // FIXME - simplify does not allow Boolean terms
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun x () Int)");
		doCommand("(declare-fun y () Int)");
		doCommand("(assert (= (+ 1 (ite p x (+ x 2))) (+ x 3)  ))");
		doCommand("(check-sat)","sat");
		doCommand("(exit)");
	}
	
	@Test
	public void iteTermUnSat() {
		Assume.assumeTrue(!"simplify".equals(solvername)); // FIXME - simplify does not allow Boolean terms
		doCommand("(set-logic QF_LIA)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun x () Int)");
		doCommand("(declare-fun y () Int)");
		doCommand("(assert (= (+ 1 (ite p x (+ x 2))) x  ))");
		doCommand("(check-sat)","unsat");
		doCommand("(exit)");
	}
	

	// TODO: test = distinct on new types and on Real
	// TODO: test if-then-else (for various types)
	// TODO: test + - * / mod integer div (int and real)
	// TODO: test < <= > >= (for real)
	// TODO: test new arbitrary types
	// TODO: test new parameterized types
	// TODO: test exists let
	// TODO: test exists forall and or xor implies not prop= prop-distinct as terms
	// TODO: test bitvector types and operations
	// TODO: test created functions
	// TODO: test array operations
}
