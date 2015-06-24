package org.smtlib;

import java.io.StringWriter;

import org.junit.*;
import org.smtlib.IExpr.IAttributeValue;
import org.smtlib.IParser.ParserException;

/** Tests parsing valid expressions without invoking solvers */
public class ParseExpressions {

	static JUnitListener listener;
	
	@Before
	public void init() {
		listener = new JUnitListener(); 
	}

	@After
	public void tearDown() throws Exception {
	}
	
	public void testExpr(String input) throws Exception {
		testExpr(input,input);
	}
	
	// FIXME - need to catch logged error messages and ParserExceptions
	
	public void testExpr(String input, String output) throws Exception {
		SMT.Configuration config = new SMT.Configuration();
		ISource source = config.smtFactory.createSource(input,null);
		IParser p = new org.smtlib.sexpr.Parser(config,source);
		IExpr e = p.parseExpr();
		StringWriter sw = new StringWriter();
		if (e != null) org.smtlib.sexpr.Printer.write(sw,e);
		Assert.assertEquals(output,sw.toString()); // expected,actual
		Assert.assertTrue("Did not expect an error",listener.msgs.isEmpty());
	}

	public void testSExpr(String input) throws Exception {
		testSExpr(input,input);
	}
	
	public void testSExpr(String input, String output) throws Exception {
		try {
			SMT.Configuration config = new SMT.Configuration();
			ISource source = config.smtFactory.createSource(input,null);
			IParser p = new org.smtlib.sexpr.Parser(config,source);
			IAttributeValue e = p.parseAttributeValue();
			StringWriter sw = new StringWriter();
			if (e != null) org.smtlib.sexpr.Printer.write(sw,e);
			Assert.assertEquals(output,sw.toString()); // expected,actual
		} catch (ParserException e) {
			Assert.assertEquals(output,"ParserException: " + e.getMessage()); // expected,actual
		}
	}

	@Test
	public void symbol() throws Exception {
		testExpr("a");
	}

	@Test
	public void symbol2() throws Exception {
		testExpr("~!@$%^&*_-+/?.=<>");
	}

	@Test
	public void barsymbol() throws Exception {
		testExpr("|a|");
	}

	@Test
	public void barsymbol2() throws Exception {
		testExpr("|a \n\t\r\nb|");
	}

	@Test
	public void numeral() throws Exception {
		//testExpr("1234567891234567890");
		testExpr("1");
	} 

	@Test
	public void decimal() throws Exception {
		testExpr("10.02");
	}

	@Test
	public void binaryLiteral() throws Exception {
		testExpr("#b1010111100001010111100001000100010001000");
	}

	@Test
	public void hexLiteral() throws Exception {
		testExpr("#xaaaabbbb");
	}

	@Test
	public void stringLiteral() throws Exception {
		testExpr("\"asd\""); // String content is a\\s\"d
	}

	@Test
	public void stringLiteralEscapes() throws Exception {
		testExpr("\"a\\\\s\\\"d\""); // String content is a\\s\"d
	}

	@Test
	public void id() throws Exception {
		testExpr("(_ a 4)");
	}

	@Test
	public void or() throws Exception {
		testExpr("(or a a)");
	}

	@Test
	public void orid() throws Exception {
		testExpr("((_ x 5) a a)");
	}

	@Test
	public void forall() throws Exception {
		testExpr("(forall ((a Bool) ) (or a b))");
	}

	@Test
	public void exists() throws Exception {
		testExpr("(exists ((a Bool) (b Bool) ) (or a b))");
	}

	@Test
	public void let() throws Exception {
		testExpr("(let ((a 5) (b true) ) (ite b a 9))");
	}

	@Test
	public void named() throws Exception {
		testExpr("(! x :named |y|)");
	}

	@Test
	public void sexprSeq() throws Exception {
		testSExpr("( x 1 2.3 \"qwe\" #b10 #xab )");
	}

	@Test
	public void sexprNumeral() throws Exception {
		testSExpr("2");
	}

	@Test
	public void sexprDecimal() throws Exception {
		testSExpr("2.4");
	}

	@Test
	public void sexprString() throws Exception {
		testSExpr("\"asd\\\"sdf\\\\dfg\"");
	}

	@Test
	public void sexprBinary() throws Exception {
		testSExpr("#b1010");
	}

	@Test
	public void sexprHex() throws Exception {
		testSExpr("#xdeaf");
	}
	
}
