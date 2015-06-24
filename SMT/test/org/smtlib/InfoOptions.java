package org.smtlib;

import java.util.List;

import org.junit.Assert;
import org.junit.Assume;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.impl.Response;
import tests.ParameterizedIgnorable;

@RunWith(ParameterizedIgnorable.class)
public class InfoOptions  extends LogicTests {

	boolean isTest;
	
    public InfoOptions(String solvername) {
    	this.solvername = solvername; 
    	this.isTest = "test".equals(solvername);
    }
    
    public void checkGetInfo(String keyword, String expected) {
		IResponse r = doCommand("(get-info " + keyword + ")");
		if (r instanceof Response.Seq) {
			List<IAttribute<?>> list = ((Response.Seq)r).attributes();
			Object o = list.get(0).attrValue();
			if (o instanceof IStringLiteral) {
				String n = ((IStringLiteral)o).value();
				if (expected != null) Assert.assertEquals(expected,n);
				else Assert.assertTrue(n != null);
				return;
			}
		}
		Assert.assertTrue("Response is wrong " + r,false);
    }
    
	@Test
	public void checkAuthors() {
		checkGetInfo(":authors",
				(solvername.equals("test") ? "David R. Cok"
				: solvername.equals("simplify") ? "David Detlefs and Greg Nelson and James B. Saxe"
				: solvername.startsWith("yices") ? "SRI"
				: solvername.equals("cvc") ? "Clark Barrett, Cesare Tinelli, and others"
				: solvername.equals("cvc4") ? null // Long text that we don't check // TODO
				: solvername.startsWith("z3") ? "Leonardo de Moura and Nikolaj Bjorner"
				: "???" )
				);
	}
    
	@Test
	public void checkVersion() {
		checkGetInfo(":version",
				(solvername.equals("test") ? "0.0"
				: solvername.equals("simplify") ? "1.5.4"
				: solvername.equals("yices") ? "1.0.28"
				: solvername.equals("yices2") ? "2.1"
				: solvername.equals("cvc") ? "2.2"
				: solvername.equals("cvc4") ? "1.4-prerelease"
				: solvername.equals("z3_4_3") ? "4.3"
				: solvername.equals("z3_2_11") ? "2.11"
				: "???" )
				);
	}
    
	@Test
	public void checkName() {
		checkGetInfo(":name",
						solvername.equals("test") ? "test"
						: solvername.equals("simplify") ? "simplify"
						: solvername.equals("yices") ? "yices"
						: solvername.equals("yices2") ? "yices2"
						: solvername.equals("cvc") ? "CVC3"
						: solvername.equals("cvc4") ? "cvc4"
						: solvername.equals("z3_4_3") ? "Z3"
						: solvername.equals("z3_2_11") ? "z3-2.11"
						: "???" );
	}
    
	// FIXME - no sure what this really should be
//	@Test
//	public void checkErrorBehavior() {
//		doCommand("(get-info :error-behavior)","(:error-behavior continued-execution )");
//	}
	
	// FIXME - need a test for :reason-unknown

	@Test
	public void checkSetName() {
		doCommand("(set-info :name \"xx\")",
				"(error \"Setting the value of a pre-defined keyword is not permitted: :name\")");
	}
	
	@Test
	public void checkSetAuthors() {
		doCommand("(set-info :authors \"xx\")",
				"(error \"Setting the value of a pre-defined keyword is not permitted: :authors\")");
	}
	
	@Test
	public void checkPrintSuccess() {
		doCommand("(get-option :print-success)", 
				"true"
				);
	}
	
	@Test
	public void checkSetPrintSuccess() {
		doCommand("(set-option :print-success false)", 
				"");
		doCommand("(get-option :print-success)", 
				"false");
		doCommand("(set-option :print-success true)", 
				"success");
		doCommand("(get-option :print-success)", 
				"true");
	}
	
	@Test
	public void checkRegularOutput() {
		doCommand("(get-option :regular-output-channel)", 
				solvername.equals("cvc4")? "unsupported"
						: "\"stdout\""
				);
	}
	
	@Test
	public void checkSetRegularOutput() {
		Assume.assumeTrue(false);
		doCommand("(set-option :regular-output-channel \"test-output\")", "success"); // FIXME - writes success to test-output? - hangs for z3_4_3 ?
		doCommand("(get-option :regular-output-channel)", "\"test-output\"");
		doCommand("(set-option :regular-output-channel \"stdout\")", "success");
		doCommand("(get-option :regular-output-channel)", "\"stdout\"");
	}
	
	@Test
	public void checkInteractiveMode() {
		doCommand("(get-option :interactive-mode)", 
				"cvc4".equals(solvername) ? "true" : "false"
				);
	}
	
	@Test
	public void checkSetInteractiveMode() {
		doCommand("(set-option :interactive-mode true)", 
				"success");
		doCommand("(get-option :interactive-mode)", 
				"true");
		doCommand("(set-option :interactive-mode false)", 
				"success");
		doCommand("(get-option :interactive-mode)", 
				"false");
	}
	
	@Test
	public void checkProduceProofs() {
		doCommand("(get-option :produce-proofs)", 
				"false"
				);
	}
	
	@Test
	public void checkSetProduceProofs() {
		doCommand("(set-option :produce-proofs true)", 
				isTest? "success" 
						: solvername.equals("cvc4")? "(error \"Error in option parsing: option `produce-proofs' requires a proofs-enabled build of CVC4; this binary was not built with proof support\")"
						:  "unsupported");
		doCommand("(get-option :produce-proofs)", 
				isTest? "true"
				:  "false");
		doCommand("(set-option :produce-proofs false)", 
				isTest? "success" 
						: solvername.equals("cvc4")? "success"
						:  "unsupported");
		doCommand("(get-option :produce-proofs)", 
				"false");
	}
	
	@Test
	public void checkProduceModels() {
		doCommand("(get-option :produce-models)", 
				"false"
				);
	}
	
	@Test
	public void checkSetProduceModels() {
		boolean support = isTest || solvername.startsWith("z3") || "cvc".equals(solvername) || "cvc4".equals(solvername) || "yices2".equals(solvername);
		doCommand("(set-option :produce-models true)", 
				support? "success" 
						: "unsupported");
		doCommand("(get-option :produce-models)", 
				support? "true" 
						:  "false");
		doCommand("(set-option :produce-models false)", 
				support? "success" 
						: "unsupported");
		doCommand("(get-option :produce-models)", 
				"false");
	}
	
	@Test
	public void checkProduceAssignments() {
		doCommand("(get-option :produce-assignments)", 
				"false"
				);
	}
	
	@Test
	public void checkSetProduceAssignments() {
		boolean supported = isTest || solvername.equals("cvc4");
		
		doCommand("(set-option :produce-assignments true)",
					supported? "success" 
						: "unsupported");
		doCommand("(get-option :produce-assignments)", 
				supported? "true" 
						:"false");
		doCommand("(set-option :produce-assignments false)",
						supported? "success" 
						: "unsupported");
		doCommand("(get-option :produce-assignments)", 
				"false");
	}
	
	@Test
	public void checkProduceUnsatCores() {
		doCommand("(get-option :produce-unsat-cores)", 
				"false"
				);
	}
	
	@Test
	public void checkSetProduceUnsatCores() {
		boolean supported = isTest || solvername.equals("yices2");
		doCommand("(set-option :produce-unsat-cores true)",
				supported ? "success" 
						:  "unsupported");
		doCommand("(get-option :produce-unsat-cores)", 
				supported? "true" 
						: "false");
		doCommand("(set-option :produce-unsat-cores false)",
				supported? "success" 
						: solvername.equals("cvc4") ? "success"
						:  "unsupported");
		doCommand("(get-option :produce-unsat-cores)", 
				"false");
	}
	
	@Test
	public void checkExpandDefinitions() {
		doCommand("(get-option :expand-definitions)", 
				"false"
				);
	}
	
	@Test
	public void checkSetExpandDefinitions() {
		doCommand("(set-option :expand-definitions true)", "success");
		doCommand("(get-option :expand-definitions)", 
				"true");
		doCommand("(set-option :expand-definitions false)", "success");
		doCommand("(get-option :expand-definitions)", 
				"false");
	}
	
	@Test
	public void checkRandomSeed() {
		Assume.assumeTrue(!"cvc4".equals(solvername)); // FIXME - cvc4 does not handle randome seed correctly
		doCommand("(get-option :random-seed)", 
				"0"
				);
	}
	
	@Test
	public void checkSetRandomSeed() {
		Assume.assumeTrue(!"cvc4".equals(solvername)); // FIXME - cvc4 does not handle randome seed correctly
		doCommand("(set-option :random-seed 1)", "success");
		doCommand("(get-option :random-seed)", 
				"cvc4".equals(solvername) ? "0" :
				"1");
		doCommand("(set-option :random-seed 2)", "success");
		doCommand("(get-option :random-seed)", 
				"cvc4".equals(solvername) ? "0" :
				"2");
	}
	
	@Test
	public void checkVerbosity() {
		doCommand("(get-option :verbosity)", 
				"0"
				);
	}
	
	@Test
	public void checkSetVerbosity() {
		doCommand("(set-option :verbosity 1)", 
				"success");
		doCommand("(get-option :verbosity)", 
				"1");
		doCommand("(set-option :verbosity 2)", 
				"success");
		doCommand("(get-option :verbosity)", 
				"2");
	}
}

