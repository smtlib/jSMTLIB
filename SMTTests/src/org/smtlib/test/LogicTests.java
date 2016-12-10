package org.smtlib.test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.runners.Parameterized.Parameters;
import org.smtlib.ICommand;
import org.smtlib.IParser;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.ISource;
import org.smtlib.SMT;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IParser.ParserException;


public class LogicTests {
	static final int v20 = 0;
	static final int v25 = 1;
	static final int v26 = 2;
	
	static int smtlib_version = v20;

	public static final String[] solvers = new String[] {
            "test", 
            "z3_4_3", 
            "z3_4_3_2", 
            "z3_4_4", 
            /*"z3_2_11", "yices",*/ 
            //"yices2", 
            "cvc4", 
            "cvc4b", 
            /*"cvc"}, */
            "simplify", 
            } ;
	
    @Parameters
    public static Collection<String[]> data() {
    	List<String[]> list = new ArrayList<>(solvers.length * 3);
    	for (String solver: solvers) {
    		list.add(new String[]{solver, "V2.0"});
    		list.add(new String[]{solver, "V2.5"});
    	}
        return list;
    }

    String solvername;
	IParser p;
	ISolver solver;
	SMT smt;
	JUnitListener listener;
	String version;
	
	@Before
	public void setup() {
		//System.out.println(solvername);
		init();
	}
	
	@After
	public void teardown() {
	}
	
	public void init() {
		SMT.Configuration.smtlib = version;
		smt = new SMT();
		// We're not reading the command-line so we have to set items ourselves
		// Executable paths are taken from the properties
		smt.props = smt.readProperties();
		listener = new JUnitListener();
		smt.smtConfig.log.clearListeners();
		smt.smtConfig.log.addListener(listener);
		smt.smtConfig.solvername = solvername;
		smt.smtConfig.logfile = "solver.out";
		smt.smtConfig.smtlib = version; // FIXME - is this needed?
		ISolver s = smt.startSolver(smt.smtConfig,solvername,null);
		if (s == null) throw new RuntimeException("Failed to create or start solver");
		solver = s;
	}
	
	/** Checks response against result, issuing a JUnit Assert if they do not match appropriately */
	public void checkResponse(IResponse res, /*@Nullable*/String result) {
		if (res == null) {
			Assert.assertTrue("Response is null",false);
		} else if (result == null) {
			if (res.isError()) Assert.assertTrue(((IResponse.IError)res).errorMsg(),false);
		} else if (result.isEmpty() && res.isOK()) {
			ISource source = smt.smtConfig.smtFactory.createSource(":print-success",null);
			IParser p = smt.smtConfig.smtFactory.createParser(smt.smtConfig,source);
			try {
				IKeyword k = p.parseKeyword();
				IResponse r = solver.get_option(k);
				if (!r.toString().equals("false")) {
					Assert.assertEquals(result,smt.smtConfig.defaultPrinter.toString(res));
				}
			} catch (ParserException e) {
				Assert.assertTrue(e.toString(),false);
			}
		} else {
			Assert.assertEquals(result,smt.smtConfig.defaultPrinter.toString(res));
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
			smt.smtConfig.log.diag = smt.smtConfig.log.out;
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
