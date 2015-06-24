package org.smtlib;

import java.io.StringWriter;

import org.junit.*;

/** Tests parsing commands, without invoking solvers */
public class ParseCommand {
	
	final String eol = System.getProperty("line.separator");
	JUnitListener listener;
	SMT.Configuration config;
	
	@Before
	public void init() {
		config = new SMT.Configuration();
		listener = new JUnitListener();
		config.log.clearListeners();
		config.log.addListener(listener);
	}
	
	public void testCommand(String input) throws Exception {
		ISource source = config.smtFactory.createSource(input,null);
		IParser p = new org.smtlib.sexpr.Parser(config,source);
		ICommand e = p.parseCommand();
		StringWriter sw = new StringWriter();
		if (e != null) org.smtlib.sexpr.Printer.write(sw,e);
		// Expecting success
		Assert.assertTrue(listener.msgs.isEmpty() ? "": listener.msgs.get(0).toString(),listener.msgs.isEmpty());
		Assert.assertEquals(input,sw.toString()); // expected,actual
		Assert.assertTrue(e != null);
	}

	public void testCommand(String input, String errormsg) throws Exception {
		ISource source = config.smtFactory.createSource(input,null);
		IParser p = new org.smtlib.sexpr.Parser(config,source);
		ICommand e = p.parseCommand();
		StringWriter sw = new StringWriter();
		if (e != null) org.smtlib.sexpr.Printer.write(sw,e);
		// Expecting an error 
		Assert.assertTrue("Expected an error message",!listener.msgs.isEmpty());
		Assert.assertEquals(errormsg,((IResponse.IError)listener.msgs.get(0)).errorMsg()); // FIXME - check other messages?
		Assert.assertTrue(e == null);
	}

	@Test
	public void assertExpr() throws Exception {
		testCommand("(assert true)");
	}

	@Test
	public void check_sat() throws Exception {
		testCommand("(check-sat)");
	}

	@Test
	public void extra() throws Exception {
		testCommand("(check-sat zzz)","A check-sat command takes no arguments");
	}

	@Test
	public void norp() throws Exception {
		testCommand("(check-sat ","The input ends with an unmatched left parenthesis");
	}

	@Test
	public void noparen() throws Exception {
		testCommand("check-sat ","Expected a left parenthesis here, instead of a symbol");
	}

	@Test
	public void declare_fun() throws Exception {
		testCommand("(declare-fun > () Bool)");
	}

	@Test
	public void declare_fun_badsymbol() throws Exception {
		testCommand("(declare-fun |@x| () Bool)","User-defined symbols may not begin with . or @");
	}

	@Test
	public void declare_fun2() throws Exception {
		testCommand("(declare-fun c (Bool ) Bool)");
	}

	@Test
	public void declare_sort() throws Exception {
		testCommand("(declare-sort MyInt 0)");
	}

	@Test
	public void declare_sort_badsymbol() throws Exception {
		testCommand("(declare-sort |.XX| 0)","User-defined symbols may not begin with . or @");
	}

	@Test
	public void declare_sort2() throws Exception {
		testCommand("(declare-sort MyInt 3)");
	}

	@Test
	public void define_fun() throws Exception {
		testCommand("(define-fun f ((p Bool)(q Bool)) Bool (and p q))");
	}

	@Test
	public void define_fun_badsymbol() throws Exception {
		testCommand("(define-fun .x ((p Bool)(q Bool)) Bool (and p q))","User-defined symbols may not begin with . or @");
	}

	@Test
	public void define_fun_duplicate() throws Exception {
		testCommand("(define-fun x ((p Bool)(|p| Bool)) Bool (and p q))","A name is duplicated in the parameter list: |p|");
	}

	@Test
	public void define_fun_reserved_word() throws Exception {
		testCommand("(define-fun check-sat ((p Bool)(q Bool)) Bool (and p q))","A reserved word may not be used as a symbol here: check-sat");
	}

	@Test
	public void define_fun_reserved_word_ok() throws Exception {
		config.relax = true;
		testCommand("(define-fun check-sat ((p Bool)(q Bool)) Bool (and p q))");
	}

	@Test
	public void define_sort() throws Exception {
		testCommand("(define-sort || (B ) Bool)");
	}

	@Test
	public void define_sort_badsymbol() throws Exception {
		testCommand("(define-sort |@z| (B ) Bool)","User-defined symbols may not begin with . or @");
	}

	@Test
	public void define_sort_duplicate() throws Exception {
		testCommand("(define-sort |@z| (B |B| ) Bool)","A name is duplicated in the parameter list: |B|");
	}

	@Test
	public void define_sort_reserved_word() throws Exception {
		testCommand("(define-sort par (B ) Bool)","A reserved word may not be used as a symbol here: par");
	}

	@Test
	public void define_sort_reserved_word_ok() throws Exception {
		config.relax = true;
		testCommand("(define-sort check-sat (B ) Bool)");
	}

	@Test
	public void exec() throws Exception {
		config.relax = true;
		testCommand("(exec ("+eol+"(exit)"+eol+"))");
	}
	
	@Test
	public void execWithFilename() throws Exception {
		config.relax = true;
		testCommand("(exec \"execfile\")");
	}
	
	@Test
	public void exit() throws Exception {
		testCommand("(exit)");
	}

	@Test
	public void get_assertions() throws Exception {
		testCommand("(get-assertions)");
	}

	@Test
	public void get_info() throws Exception {
		testCommand("(get-info :status)");
	}

	@Test
	public void get_option() throws Exception {
		testCommand("(get-option :print-success)");
	}

	@Test
	public void pop() throws Exception {
		testCommand("(pop 0)");
	}

	@Test
	public void push() throws Exception {
		testCommand("(push 10)");
	}

	@Test
	public void set_logic() throws Exception {
		testCommand("(set-logic QF_UF)");
	}

	@Test
	public void set_option() throws Exception {
		testCommand("(set-option :print-success true)");
	}

	@Test
	public void set_info() throws Exception {
		testCommand("(set-info :x sat)");
	}

	@Test
	public void get_proof() throws Exception {
		testCommand("(get-proof)");
	}

	@Test
	public void get_proof_err() throws Exception {
		testCommand("(get-proof x)","A get-proof command takes no arguments");
	}

	@Test
	public void get_unsat_core() throws Exception {
		testCommand("(get-unsat-core)");
	}

	@Test
	public void get_unsat_core_err() throws Exception {
		testCommand("(get-unsat-core x)","A get-unsat-core command takes no arguments");
	}

	@Test
	public void get_assignment() throws Exception {
		testCommand("(get-assignment)");
	}

	@Test
	public void get_assignment_err() throws Exception {
		testCommand("(get-assignment x)","A get-assignment command takes no arguments");
	}

	@Test
	public void get_value() throws Exception {
		testCommand("(get-value ( x))");
	}

	@Test
	public void what() throws Exception {
		config.relax = true;
		testCommand("(what a b)");
	}

}
