package org.smtlib;

import java.util.Iterator;
import java.util.List;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.smtlib.solvers.Solver_test;

public class TypeCheckRoot {

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
		else Assert.assertEquals(expected,((IResponse.IError)res).errorMsg());
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
		Assert.assertTrue(listener.msgs.isEmpty());
		checkResponse(command.execute(solver));
		Assert.assertTrue(listener.msgs.isEmpty());
	}
	
	public void doCommand(String input, String expectedError) {
		ICommand command = parseCommand(input);
		Assert.assertTrue(listener.msgs.isEmpty());
		checkResponse(command.execute(solver),expectedError);
		Assert.assertTrue(listener.msgs.isEmpty());

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
				Assert.assertTrue("Null expression and null error message - internal bug",!listener.msgs.isEmpty());
				Assert.assertTrue(((IResponse.IError)listener.msgs.get(0)).errorMsg(),false);
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
	

}
