package org.smtlib.test;

import java.io.StringWriter;

import org.junit.*;
import org.smtlib.IAttributeValue;
import org.smtlib.IExpr;
import org.smtlib.IParser;
import org.smtlib.IPos;
import org.smtlib.IResponse;
import org.smtlib.ISource;
import org.smtlib.SMT;
import org.smtlib.IParser.ParserException;

/** Tests parsing invalid expressions, without invoking solvers */
public class ParseExpressionErrors {
	
	static JUnitListener listener;
	String version;
	
	@Before
	public void init() {
		listener = new JUnitListener(); 
	}

	public void testExpr(String input, String msg, int start, int end) throws Exception {
		SMT.Configuration config = new SMT.Configuration();
		config.smtlib = version;
		config.log.clearListeners();
		config.log.addListener(listener);
		ISource source = config.smtFactory.createSource(input,null);
		IParser p = new org.smtlib.sexpr.Parser(config,source);
		IExpr e = null;
		try {
			e = p.parseExpr();
		} catch (ParserException ex) {
			// A null message means the error was already logged (e.g. by the lexer);
			// a non-null message is reported here, at the top level, as parseCommand() does.
			if (ex.getMessage() != null) config.log.logError(config.responseFactory.error(ex.getMessage(),ex.pos()));
		}
		Assert.assertTrue("Response was not an error",listener.msgs.get(0) instanceof IResponse.IError);
		Assert.assertEquals(msg,((IResponse.IError)listener.msgs.get(0)).errorMsg());// expected,actual
		IPos pos = ((IResponse.IError)listener.msgs.get(0)).pos();
		Assert.assertEquals(start,pos.charStart());
		Assert.assertEquals(end,pos.charEnd());
		Assert.assertTrue(e == null || e instanceof IExpr.IError); 
	}

	public void testSExpr(String input, String output) throws Exception {
		SMT.Configuration config = new SMT.Configuration();
		config.smtlib = version;
		config.log.clearListeners();
		config.log.addListener(listener);
		ISource source = config.smtFactory.createSource(input,null);
		IParser p = new org.smtlib.sexpr.Parser(config,source);
		IAttributeValue e = null;
		try {
			e = p.parseAttributeValue();
		} catch (ParserException ex) {
			// A null message means the error was already logged (e.g. by the lexer);
			// a non-null message is reported here, at the top level, as parseCommand() does.
			if (ex.getMessage() != null) config.log.logError(config.responseFactory.error(ex.getMessage(),ex.pos()));
		}
		StringWriter sw = new StringWriter();
		if (e != null) org.smtlib.sexpr.Printer.write(sw,e);
		if (!listener.msgs.isEmpty()) sw.append(config.defaultPrinter.toString(listener.msgs.get(0))); // FIXME - append them all?
		Assert.assertEquals(output,sw.toString()); // expected,actual
	}

	@Test
	public void empty() throws Exception {
		testExpr("","Expected an expression here",0,1);
	}

	@Test
	public void leadingZero() throws Exception {
		testExpr("00","Incorrect format for a number - no leading zeros allowed: 00",0,2);
	}

	@Test
	public void leadingZero2() throws Exception {
		testExpr("0123","Incorrect format for a number - no leading zeros allowed: 0123",0,4);
	}

	@Test
	public void barsymbolError() throws Exception {
		testExpr("|a ","Bar(|)-enclosed symbol is not terminated: |a ",0,3);
	}

	@Test
	public void sexprStringError() throws Exception {
		testSExpr("\"asddfg","(error \"String literal is not terminated: \"\"asddfg\")");
	}
	@Test
	public void sexprStringErrorA() throws Exception {
		version = "V2.0";
		testSExpr("\"asddfg","(error \"String literal is not terminated: \\\"asddfg\")");
	}

	@Test
	public void errorLeadingZero() throws Exception {
		testSExpr("01","(error \"Incorrect format for a number - no leading zeros allowed: 01\")");
	}
	
	@Test
	public void errorBadSymbol() throws Exception {
		testSExpr("0abc","(error \"Invalid token: 0abc\")");
	}

	@Test
	public void errorBadSymbol2() throws Exception {
		testSExpr(",","(error \"Invalid token: ,\")");
	}

	@Test
	public void errorBadSymbol3() throws Exception {
		testSExpr("#","(error \"Invalid token: #\")");
	}

	@Test
	public void errorBadSymbol4() throws Exception {
		testSExpr("[","(error \"Invalid token: [\")");
	}

	@Test
	public void errorBadSymbol5() throws Exception {
		testSExpr("]","(error \"Invalid token: ]\")");
	}

	@Test
	public void errorBadSymbol6() throws Exception {
		testSExpr("}","(error \"Invalid token: }\")");
	}

	@Test
	public void errorBadSymbol7() throws Exception {
		testSExpr("{","(error \"Invalid token: {\")");
	}

	@Test
	public void errorBadSymbol8() throws Exception {
		testSExpr("\\","(error \"Invalid token: \\\")");
	}
	@Test
	public void errorBadSymbol8a() throws Exception {
		version = "V2.0";
		testSExpr("\\","(error \"Invalid token: \\\\\")");
	}

	@Test
	public void errorBadSymbol9() throws Exception {
		testSExpr("`","(error \"Invalid token: `\")");
	}

	@Test
	public void errorBadSymbol10() throws Exception {
		testSExpr("'","(error \"Invalid token: '\")");
	}
	
	@Test
	public void errorBadSymbol11() throws Exception {
		testSExpr(":","(error \"Invalid token: :\")");
	}

	@Test
	public void errorBadSymbol12() throws Exception {
		testSExpr("\"","(error \"String literal is not terminated: \"\"\")");
	}
	@Test
	public void errorBadSymbol12a() throws Exception {
		version = "V2.0";
		testSExpr("\"","(error \"String literal is not terminated: \\\"\")");
	}

	@Test
	public void errorBadSymbol13() throws Exception {
		testSExpr("|","(error \"Bar(|)-enclosed symbol is not terminated: |\")");
	}

	// forall/exists/let duplicate-parameter-name errors moved to TypeChecks.java: that check
	// lives in TypeChecker (scope tracking across bindings), not in Parser, so parseExpr()
	// alone never produces them -- see forallDuplicateName/existsDuplicateName/letDuplicateName.

}
