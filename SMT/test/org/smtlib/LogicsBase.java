package org.smtlib;

import java.util.Arrays;
import java.util.Collection;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.runners.Parameterized.Parameters;

public class LogicsBase {

    @Parameters
    public static Collection<String[]> data() {
            return Arrays.asList(new String[][]{ 
            		{ "QF_UF" }, { "QF_LIA" }, {"QF_IDL"}, {"QF_RDL"} ,
            		{ "QF_ABV" }, { "QF_AUFBV" }, {"QF_AUFLIA"}, {"QF_AX"} ,
            		{ "QF_BV" }, { "QF_LRA" }, {"QF_NIA"}, {"QF_UFIDL"} ,
            		{ "AUFLIA" }, { "AUFLIRA" }, {"AUFNIRA"}, {"LRA"} ,
            		{ "ZZZ" } } );
    }
    
    String solvername = "test";
    String logicname;
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
	
	// NOTE - duplicates stuff in LogicTests.java
	
	public void init() {
		smt = new SMT();
		listener = new JUnitListener();
		smt.smtConfig.log.clearListeners();
		smt.smtConfig.log.addListener(listener);
		smt.smtConfig.solvername = solvername;
		smt.smtConfig.logfile = "solver.out." + solvername;
		ISolver s = smt.startSolver(smt.smtConfig,solvername,null);
		if (s == null) throw new RuntimeException("Failed to create or start solver");
		solver = s;
	}
	
	public void checkResponse(IResponse res, /*@Nullable*/String result) {
		if (res == null) {
			Assert.assertTrue("Response is null",false);
		} else if (res.isError()) {
			Assert.assertEquals(result,((IResponse.IError)res).errorMsg());
		} else if (listener.msgs.size() > 0  && listener.msgs.get(0) instanceof IResponse.IError) { // FIXME - check all the messages?
			Assert.assertEquals(result,((IResponse.IError)listener.msgs.get(0)).errorMsg());
		} else if (!res.isOK() && result != null) {
			Assert.assertEquals(result,res.toString());
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
	

}
