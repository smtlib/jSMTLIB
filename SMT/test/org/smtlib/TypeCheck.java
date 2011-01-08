package org.smtlib;

import java.util.Iterator;
import java.util.List;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.smtlib.IPos.ISource;
import org.smtlib.impl.TypeChecker;
import org.smtlib.solvers.Solver_test;

// FIXME - need to check complex sorts; parameterized definitions; Int and NUMERAL types; variadic functions; parameterized function sorts
// FIXME - need to implement checking of sort expressions

public class TypeCheck {
	IParser p;
	Solver_test solver;
	SMT smt;
	JUnitListener listener;
	
	@Before
	public void setup() {
		smt = new SMT();
		smt.smtConfig.logicPath = "logics";
		listener = new JUnitListener();
		smt.smtConfig.log.addListener(listener);
		solver = new Solver_test(smt.smtConfig,null);
		solver.start();
		checkResponse(solver.set_logic("QF_UF",null));
	}
	
	@After
	public void teardown() {
		solver.exit();
	}
	
	public void checkResponse(IResponse res) {
		if (res != null && res.isError()) Assert.assertTrue(((IResponse.IError)res).errorMsg(),false);
	}
	
	public void checkResponse(IResponse res, String expected) {
		if (res == null || !res.isError()) Assert.assertTrue("Expected an error",false);
		Assert.assertEquals(expected,((IResponse.IError)res).errorMsg());
	}
	
	public ICommand parseCommand(String input) {
		try {
			ISource source = smt.smtConfig.smtFactory.createSource(input,null);
			IParser p = new org.smtlib.sexpr.Parser(smt.smtConfig,source);
			return p.parseCommand();
		} catch (Exception e) {
			return null;
		}
	}
	
	public void doCommand(String input) {
		ICommand command = parseCommand(input);
		Assert.assertEquals(null,listener.msg);
		checkResponse(command.execute(solver));
		Assert.assertEquals(null,listener.msg);
	}
	
	public void doCommand(String input, String expectedError) {
		ICommand command = parseCommand(input);
		Assert.assertEquals(null,listener.msg);
		checkResponse(command.execute(solver),expectedError);
		Assert.assertEquals(null,listener.msg);

	}
	
	public IExpr parseExpr(String input) {
		try {
			ISource source = smt.smtConfig.smtFactory.createSource(input,null);
			IParser p = new org.smtlib.sexpr.Parser(smt.smtConfig,source);
			return p.parseExpr();
		} catch (Exception e) {
			return null;
		}
	}
	
	public void check(String input,String... error) {
		try {
			ISource source = smt.smtConfig.smtFactory.createSource(input,null);
			IParser p = new org.smtlib.sexpr.Parser(smt.smtConfig,source);
			IExpr e = p.parseExpr();
			if (e == null) {
				Assert.assertTrue("Null expression and null error message - internal bug",listener.msg != null);
				Assert.assertTrue(((IResponse.IError)listener.msg).errorMsg(),false);
			}
			List<IResponse> errors = TypeChecker.check(solver.symTable,e,null); 
			Iterator<IResponse> iter = errors.iterator();
			for (String er: error) {
				Assert.assertEquals(er,!iter.hasNext() ? null : ((IResponse.IError)iter.next()).errorMsg());
			}
			if (iter.hasNext()) {
				Assert.assertTrue(((IResponse.IError)iter.next()).errorMsg(), iter.hasNext());
			}
		} catch (Exception e) {
			System.out.println("EXCEPTION " + e);
			e.printStackTrace(System.out);
			Assert.assertTrue("Unexpected exception",false);
		}

	}
	
	@Test
	public void checkTrue() {
		check("true");
	}

	@Test
	public void checkBadVar() {
		check("p","Unknown constant symbol p");
	}
	
	@Test
	public void checkBoolVar() {
		doCommand("(declare-fun p () Bool)");
		check("p");
	}
	
	@Test
	public void checkBoolFcn() {
		doCommand("(declare-sort X 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () Bool)");
		check("(or p q)");
	}
	
	@Test
	public void checkBadFcn() {
		doCommand("(declare-sort X 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () X)");
		check("(or p q)","Unknown predicate symbol or with argument types Bool X");
	}
	
	@Test
	public void checkBadSort() {
		doCommand("(declare-sort X 0)");
		doCommand("(declare-fun p () X)");
		check("p","Expected an expression with Bool sort, not X");
	}
	
	@Test
	public void checkLet() {
		doCommand("(declare-sort X 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () X)");
		check("(let ((r true)(s q)) (not r))");
	}
	
	@Test
	public void checkBadLet() {
		doCommand("(declare-sort X 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () X)");
		check("(let ((r true)(s q)) (not s))","Unknown predicate symbol not with argument types X");
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
	
	@Test
	public void checkNamed() {
		doCommand("(declare-sort X 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () X)");
		check("(and (! p :named P) (! (not p) :named Q))");
	}
	
	@Test
	public void checkBadNamed() {
		doCommand("(declare-sort X 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () X)");
		check("(and (! p :named P) (! (not t) :named Q))",
				"Unknown constant symbol t");
	}
	
	@Test
	public void checkGenericType() {
		doCommand("(declare-sort X 1)");
		doCommand("(declare-sort Y 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () (X Y))");
		doCommand("(declare-fun qb () (X Bool))");
		doCommand("(declare-fun r () Y)");
		doCommand("(declare-fun f (Y (X Y)) Bool)");
		doCommand("(declare-fun ff (Y (X Bool)) Bool)");
		check("(f r q)");
	}
	
	@Test
	public void checkGenericType2() {
		doCommand("(declare-sort X 1)");
		doCommand("(declare-sort Y 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () (X Y))");
		doCommand("(declare-fun qb () (X Bool))");
		doCommand("(declare-fun r () Y)");
		doCommand("(declare-fun f (Y (X Y)) Bool)");
		doCommand("(declare-fun ff (Y (X Bool)) (X Y))");
		check("(f r qb)",
				"Unknown predicate symbol f with argument types Y (X Bool)");
	}
	
	@Test
	public void checkGenericType3() {
		doCommand("(declare-sort X 1)");
		doCommand("(declare-sort Y 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () (X Y))");
		doCommand("(declare-fun qb () (X Bool))");
		doCommand("(declare-fun r () Y)");
		doCommand("(declare-fun f (Y X) Bool)","The sort symbol X expects 1 arguments, not 0");
	}
	
	@Test
	public void checkGenericType4() {
		doCommand("(declare-sort X 1)");
		doCommand("(declare-sort Y 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () (X Y))");
		doCommand("(declare-fun qb () (X Bool))");
		doCommand("(declare-fun r () Y)");
		doCommand("(declare-fun f (Y (X Y)) Bool)");
		doCommand("(declare-fun ff (Y (X Bool)) (X Y))");
		check("(f r (ff r qb))");
	}
	
	@Test
	public void checkGenericType5() {
		doCommand("(declare-sort X 1)");
		doCommand("(declare-sort Y 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () (X Y))");
		doCommand("(declare-fun qb () (X Bool))");
		doCommand("(declare-fun r () Y)");
		doCommand("(declare-fun f ((Y Y)) Bool)","The sort symbol Y expects 0 arguments, not 1");
	}
	
	@Test
	public void checkGenericType6() {
		doCommand("(declare-sort X 1)");
		doCommand("(declare-sort Y 0)");
		doCommand("(declare-fun p () Bool)");
		doCommand("(declare-fun q () (X Y))");
		doCommand("(declare-fun qb () (X Bool))");
		doCommand("(declare-fun r () Y)");
		doCommand("(declare-fun f () X)","The sort symbol X expects 1 arguments, not 0");
	}
	
	@Test
	public void checkTypeAbbrev() {
		doCommand("(declare-sort X 1)");
		doCommand("(declare-sort Y 0)");
		doCommand("(define-sort Z () (X Y))");
		doCommand("(declare-fun q () (X Y))");
		doCommand("(declare-fun qb () Z)");
		doCommand("(assert (= q qb))");
	}
	
	@Test
	public void checkTypeAbbrev1() {
		doCommand("(declare-sort X 1)");
		doCommand("(declare-sort Y 0)");
		doCommand("(define-sort Z (A) (X A))");
		doCommand("(declare-fun q () (X Y))");
		doCommand("(declare-fun qb () (Z Y))");
		doCommand("(assert (= q qb))");
	}
	
	@Test
	public void checkTypeAbbrev2() {
		doCommand("(declare-sort X 1)");
		doCommand("(declare-sort Y 0)");
		doCommand("(define-sort Z (A) (X A))");
		doCommand("(declare-fun q () (X Y))");
		doCommand("(declare-fun qb () (Z A))","No such sort symbol declared: A");
	}
	
	@Test
	public void checkTypeAbbrev3() {
		doCommand("(declare-sort X 1)");
		doCommand("(declare-sort Y 0)");
		doCommand("(define-sort Z (A) (X A))");
		doCommand("(declare-fun q () (X Y))");
		doCommand("(declare-fun qb () (Z Bool))");
		doCommand("(assert (= q qb))","Mismatched sorts of arguments: (X Y) vs. (Z Bool)");
	}
	

}
