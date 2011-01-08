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

public class TupeCheckInt {
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
		checkResponse(solver.set_logic("QF_LIA",null));
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
	public void checkFcnDef() {
		doCommand("(declare-fun q () Int)");
		doCommand("(declare-fun r () Int)");
		doCommand("(define-fun f ((a Int)(b Int)) Int (+ a b))");
		doCommand("(assert (= (f 1 2) 3))");
	}
	
	@Test
	public void checkFcnDef1() {
		doCommand("(declare-fun q () Int)");
		doCommand("(declare-fun r () Int)");
		doCommand("(define-fun f ((a Int)(b Int)) Int (+ a b))");
		doCommand("(assert (= (f 1 2) true))","Mismatched sorts of arguments: Int vs. Bool");
	}
	
	@Test
	public void checkFcnDef2() {
		doCommand("(define-sort Z () Int)");
		doCommand("(declare-fun q () Int)");
		doCommand("(declare-fun r () Int)");
		doCommand("(define-fun f ((a Int)(b Z)) Int (+ a b))");
		doCommand("(assert (= (f 1 2) true))","Mismatched sorts of arguments: Int vs. Bool");
	}
	

}
