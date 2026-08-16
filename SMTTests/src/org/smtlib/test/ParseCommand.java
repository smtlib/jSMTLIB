package org.smtlib.test;

import java.io.StringWriter;
import java.util.List;
import java.util.concurrent.TimeUnit;

import org.junit.*;
import org.junit.rules.Timeout;
import org.smtlib.ICommand;
import org.smtlib.IParser;
import org.smtlib.IResponse;
import org.smtlib.ISource;
import org.smtlib.SMT;
import org.smtlib.TypeChecker;

/** Tests parsing commands, without invoking solvers */
public class ParseCommand {

	@Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

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
	
	/** Parses input as a single command and checks the result: with no errormsgs, expects
	 *  parsing/validation to succeed and the command to print back out as input; with one or
	 *  more errormsgs, expects exactly that many errors to have been logged (by the parser
	 *  and/or by TypeChecker.validate, which itself can report more than one problem for a
	 *  single command -- see e.g. its declare-const branch), checked in order against
	 *  listener.msgs. A single-arg overload would previously only ever check msgs.get(0),
	 *  silently ignoring any further errors; varargs keeps every existing call site (0 or 1
	 *  error message) source- and binary-compatible while also supporting more. */
	public void testCommand(String input, String... errormsgs) throws Exception {
		ISource source = config.smtFactory.createSource(input,null);
		IParser p = new org.smtlib.sexpr.Parser(config,source);
		ICommand e = p.parseCommand();
		if (e != null) {
			List<IResponse> errs = TypeChecker.validate(config, e);
			for (IResponse err : errs) config.log.logError((IResponse.IError)err);
			if (!errs.isEmpty()) e = null;
		}
		StringWriter sw = new StringWriter();
		if (e != null) org.smtlib.sexpr.Printer.write(sw,e);
		if (errormsgs.length == 0) {
			// Expecting success
			Assert.assertTrue(listener.msgs.isEmpty() ? "": listener.msgs.get(0).toString(),listener.msgs.isEmpty());
			Assert.assertEquals(input,sw.toString()); // expected,actual
			Assert.assertTrue(e != null);
		} else {
			// Expecting exactly errormsgs.length errors, in order
			Assert.assertEquals("Wrong number of error messages", errormsgs.length, listener.msgs.size());
			for (int i = 0; i < errormsgs.length; i++) {
				Assert.assertEquals(errormsgs[i], ((IResponse.IError)listener.msgs.get(i)).errorMsg());
			}
			Assert.assertTrue(e == null);
		}
	}

	/** declare-const's TypeChecker.validate branch calls requireVersion and validateUserId
	 *  unconditionally, one after the other with no intervening errors.isEmpty() guard -- so a
	 *  pre-V2.5 declare-const with a bad symbol genuinely reports two errors from one command.
	 *  Exercises the multi-message path of testCommand(String, String...) end to end. */
	@Test
	public void declare_const_reports_version_and_badsymbol_errors() throws Exception {
		config.smtlib = "V2.0";
		testCommand("(declare-const .x Bool)",
			"The declare-const command requires SMT-LIB V2.5 or later",
			"User-defined symbols may not begin with . or @");
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
		testCommand("(define-sort MySort (B ) Bool)");
	}

	@Test
	public void define_sort_badsymbol() throws Exception {
		testCommand("(define-sort |@z| (B ) Bool)","User-defined symbols may not begin with . or @");
	}

	@Test
	public void define_sort_duplicate() throws Exception {
		testCommand("(define-sort MySort (B B) Bool)","A name is duplicated in the parameter list: B");
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

	@Test
	public void declare_const() throws Exception {
		testCommand("(declare-const x Bool)");
	}

	@Test
	public void define_const() throws Exception {
		testCommand("(define-const x Bool true)");
	}

	@Test
	public void declare_datatype_nonpar() throws Exception {
		testCommand("(declare-datatype Color ((red) (green) (blue) ))");
	}

	@Test
	public void declare_datatype_par() throws Exception {
		testCommand("(declare-datatype Option ( par (A ) ((some (val A)) (none) ) ))");
	}

	@Test
	public void declare_datatypes() throws Exception {
		testCommand("(declare-datatypes ( (Color 0)) ( ((red) (green) (blue) )))");
	}

	@Test
	public void declare_datatypes_empty_sort_list() throws Exception {
		testCommand("(declare-datatypes () (((red) )))",
				"Expected at least one sort declaration in declare-datatypes");
	}

	@Test
	public void declare_datatypes_size_mismatch() throws Exception {
		testCommand("(declare-datatypes ( (Color 0) (Shape 0)) ( ((red) ) ))",
				"Number of sort declarations (2) does not match number of datatype declarations (1)");
	}

	@Test
	public void define_funs_rec() throws Exception {
		testCommand("(define-funs-rec ((f () Bool) ) (true ))");
	}

	@Test
	public void define_funs_rec_size_mismatch() throws Exception {
		testCommand("(define-funs-rec ((f () Bool) ) (true false ))",
				"The number of function declarations (1) must equal the number of bodies (2)");
	}

	@Test
	public void declare_sort_parameter() throws Exception {
		testCommand("(declare-sort-parameter A)");
	}

	@Test
	public void declare_sort_parameter_badsymbol() throws Exception {
		testCommand("(declare-sort-parameter |.XX|)","User-defined symbols may not begin with . or @");
	}

	@Test
	public void define_fun_rec_duplicate() throws Exception {
		testCommand("(define-fun-rec f ((p Bool)(|p| Bool)) Bool (and p q))",
				"A name is duplicated in the parameter list: |p|");
	}

	@Test
	public void define_fun_rec_badsymbol() throws Exception {
		testCommand("(define-fun-rec .f () Bool true)",
				"User-defined symbols may not begin with . or @");
	}

	@Test
	public void declare_datatypes_badsymbol() throws Exception {
		testCommand("(declare-datatypes ( (|.X| 0)) ( ((red) )))",
				"User-defined symbols may not begin with . or @");
	}

	@Test
	public void check_sat_assuming_not_literal() throws Exception {
		config.smtlib = "V2.6";
		testCommand("(check-sat-assuming ((and p q)))",
				"Arguments to check-sat-assuming must be a symbol or (not symbol) in SMT-LIB V2.6 and earlier");
	}

	@Test
	public void declare_datatype_recursive_wellfounded() throws Exception {
		testCommand("(declare-datatype List ((nil) (cons (head Int) (tail List)) ))");
	}

	@Test
	public void declare_datatype_not_wellfounded() throws Exception {
		testCommand("(declare-datatype Bad ((mk (sel Bad) ) ))",
				"Datatype Bad is not well-founded (no finite base case)");
	}

	/** parseResponse() is only otherwise called from solver backends reading real process
	 * output - exercise it directly here since it has no other test coverage. */
	@Test
	public void parseResponseError() throws Exception {
		String response = "(error \"boom\")";
		org.smtlib.sexpr.Parser p = new org.smtlib.sexpr.Parser(config, config.smtFactory.createSource(response, null));
		IResponse r = p.parseResponse(response);
		Assert.assertTrue(r instanceof IResponse.IError);
		Assert.assertEquals("boom", ((IResponse.IError) r).errorMsg());
	}

}
