package org.smtlib;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.util.Arrays;
import java.util.Collection;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.runners.Parameterized.Parameters;


public class LogicTests {

    @Parameters
    public static Collection<String[]> data() {
            return Arrays.asList(new String[][] 
                { { "test"}, { "z3_4_3" }, { "z3_2_11" }, { "yices" }, {"cvc"}, {"simplify"} } );
    }

    String solvername;
	IParser p;
	ISolver solver;
	SMT smt;
	JUnitListener listener;
	
	@Before
	public void setup() {
		//System.out.println(solvername);
		init();
	}
	
	@After
	public void teardown() {
	}
	
	public void init() {
		smt = new SMT();
		// We're not reading the command-line so we have to set items ourselves
		// Executable paths are taken from the properties
		smt.props = smt.readProperties();
		listener = new JUnitListener();
		smt.smtConfig.log.clearListeners();
		smt.smtConfig.log.addListener(listener);
		smt.smtConfig.solvername = solvername;
		ISolver s = smt.startSolver(smt.smtConfig,solvername,null);
		if (s == null) throw new RuntimeException("Failed to create or start solver");
		solver = s;
	}
	
	/** Checks response against result, issuing a JUnit Assert if they do not match appropriately */
	public void checkResponse(IResponse res, /*@Nullable*/String result) {
		if (res == null) {
			Assert.assertTrue("Response is null",false);
		} else if (result != null) {
			Assert.assertEquals(result,smt.smtConfig.defaultPrinter.toString(res));
		} else if (res.isError()) {
			Assert.assertTrue(((IResponse.IError)res).errorMsg(),false);
		}
	}
	
	/** Parses a command */
	public /*@Nullable*/ ICommand parseCommand(String input) {
		try {
			ISource source = smt.smtConfig.smtFactory.createSource(input,null);
			IParser p = new org.smtlib.sexpr.Parser(smt.smtConfig,source);
			return p.parseCommand();
		} catch (Exception e) {
			return null;
		}
	}
	
	/** Parses, executes and checks a command */
	public IResponse doCommand(String input) {
		ICommand command = parseCommand(input);
		if (command == null) throw new RuntimeException("Failed to create command");
		IResponse r;
		checkResponse(r=command.execute(solver),null);
		return r;
	}
	
	/** Parses, executes and checks a command against given result. */
	public IResponse doCommand(String input, String result) {
		ICommand command = parseCommand(input);
		if (command == null) throw new RuntimeException("Failed to create command");
		IResponse r;
		checkResponse(r=command.execute(solver),result);
		return r;
	}
	
	/** Executes a script, capturing all the output and returning it. */
	public String doScript(String input) {
		ByteArrayOutputStream ba = new ByteArrayOutputStream();
		PrintStream savedOut = System.out;
		System.setOut(new PrintStream(ba));
		try {
			SMT smt = new SMT();
			smt.props = smt.readProperties();
			smt.smtConfig.text = input;
			smt.smtConfig.log.out = new PrintStream(ba);
			smt.smtConfig.solvername = solvername;
			smt.exec();
			return ba.toString();
		} catch (Exception e) {
			return e.toString();
		} finally {
			System.setOut(savedOut);
		}
	}
	

}
