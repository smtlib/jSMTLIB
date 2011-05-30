package org.smtlib;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.io.StringWriter;
import java.util.Arrays;
import java.util.Collection;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.runners.Parameterized.Parameters;
import org.smtlib.IExpr.IKeyword;


public class LogicTests {

    @Parameters
    public static Collection<String[]> data() {
            return Arrays.asList(new String[][] 
                { { "test"}, { "z3" }, { "yices" }, {"cvc"}, {"simplify"} } );
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
	
	public void checkResponse(IResponse res, /*@Nullable*/String result) {
		if (res == null) {
			Assert.assertTrue("Response is null",false);
		} else if (result != null) {
			Assert.assertEquals(result,smt.smtConfig.defaultPrinter.toString(res));
		} else if (res.isError()) {
			Assert.assertTrue(((IResponse.IError)res).errorMsg(),false);
		}
	}
	
	public /*@Nullable*/ ICommand parseCommand(String input) {
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
		if (command == null) throw new RuntimeException("Failed to create command");
		checkResponse(command.execute(solver),null);
	}
	
	public IResponse doCommand(String input, String result) {
		ICommand command = parseCommand(input);
		if (command == null) throw new RuntimeException("Failed to create command");
		IResponse r;
		checkResponse(r=command.execute(solver),result);
		return r;
	}
	
	public String doScript(String input) {
//		StringBuilder sb = new StringBuilder();
//		StringWriter ss = new StringWriter();
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
//			IKeyword psKeyword = smt.smtConfig.exprFactory.keyword(Utils.PRINT_SUCCESS,null);
//			ISource source = smt.smtConfig.smtFactory.createSource(input,null);
//			IParser p = new org.smtlib.sexpr.Parser(smt.smtConfig,source);
//			ICommand cmd;
//			while (!p.isEOD()) {
//				cmd = p.parseCommand();
//				if (cmd != null) {
//					IResponse res = cmd.execute(solver);
//					IPos pos = res.isError() ? ((IResponse.IError)res).pos() : null;
//					if (pos != null && pos.source() != null) {
//						sb.append(Log.locationIndication(pos,smt.smtConfig.prompt,smt.smtConfig));
//						sb.append("\n");
//					}
//					if (!res.isOK() || solver.get_option(psKeyword).toString().equals("true")) {
//						sb.append(smt.smtConfig.defaultPrinter.toString(res));
//						sb.append("\n");
//					}
//				} else {
//					IPos pos = listener.msg.isError() ? ((IResponse.IError)listener.msg).pos() : null;
//					if (pos != null && pos.source() != null) {
//						sb.append(Log.locationIndication(pos,smt.smtConfig.prompt,smt.smtConfig));
//						sb.append("\n");
//					}
//
//					sb.append(smt.smtConfig.defaultPrinter.toString(listener.msg));
//					sb.append("\n");
//				}
//			}
//			return sb.toString();
		} catch (Exception e) {
			return e.toString();
		} finally {
			System.setOut(savedOut);
		}
	}
	

}
