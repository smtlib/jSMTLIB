package org.smtlib;

import java.util.List;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IAttributeValue;
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.impl.Response;

@RunWith(Parameterized.class)
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
				: solvername.equals("yices") ? "SRI"
				: solvername.equals("cvc") ? "Clark Barrett, Cesare Tinelli, and others"
				: solvername.equals("cvc4") ? null // Long text that we don't check
				: solvername.equals("z3") ? "Leonardo de Moura and Nikolaj Bjorner"
				: "???" )
				);
	}
    
	@Test
	public void checkVersion() {
		checkGetInfo(":version",
				(solvername.equals("test") ? "0.0"
				: solvername.equals("simplify") ? "1.5.4"
				: solvername.equals("yices") ? "1.0.28"
				: solvername.equals("cvc") ? "2.2"
				: solvername.equals("cvc4") ? "0.0prerelease"
				: solvername.equals("z3") ? "2.11-0.0"
				: "???" )
				);
	}
    
	@Test
	public void checkName() {
		checkGetInfo(":name",
						solvername.equals("test") ? "test"
						: solvername.equals("simplify") ? "simplify"
						: solvername.equals("yices") ? "yices"
						: solvername.equals("cvc") ? "CVC3"
						: solvername.equals("cvc4") ? "cvc4"
						: solvername.equals("z3") ? "z3"
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
		doCommand("(set-info :name \"xx\")","(error \"Setting the value of a pre-defined keyword is not permitted: :name\")");
	}
	
	@Test
	public void checkSetAuthors() {
		doCommand("(set-info :authors \"xx\")","(error \"Setting the value of a pre-defined keyword is not permitted: :authors\")");
	}
	
	@Test
	public void checkPrintSuccess() {
		doCommand("(get-option :print-success)", 
				"true"
				);
	}
	
	@Test
	public void checkSetPrintSuccess() {
		doCommand("(set-option :print-success false)", "success");
		doCommand("(get-option :print-success)", "false");
		doCommand("(set-option :print-success true)", "success");
		doCommand("(get-option :print-success)", "true");
	}
	
	@Test
	public void checkRegularOutput() {
		doCommand("(get-option :regular-output-channel)", 
				"\"stdout\""
				);
	}
	
	@Test
	public void checkSetRegularOutput() {
		doCommand("(set-option :regular-output-channel \"xx\")", "success");
		doCommand("(get-option :regular-output-channel)", "\"xx\"");
		doCommand("(set-option :regular-output-channel \"stdout\")", "success");
		doCommand("(get-option :regular-output-channel)", "\"stdout\"");
	}
	
	@Test
	public void checkInteractiveMode() {
		doCommand("(get-option :interactive-mode)", 
				"false"
				);
	}
	
	@Test
	public void checkSetInteractiveMode() {
		doCommand("(set-option :interactive-mode true)", "success");
		doCommand("(get-option :interactive-mode)", "true");
		doCommand("(set-option :interactive-mode false)", "success");
		doCommand("(get-option :interactive-mode)", "false");
	}
	
	@Test
	public void checkProduceProofs() {
		doCommand("(get-option :produce-proofs)", 
				"false"
				);
	}
	
	@Test
	public void checkSetProduceProofs() {
		doCommand("(set-option :produce-proofs true)", isTest? "success" :  "unsupported");
		doCommand("(get-option :produce-proofs)", isTest? "true" :  "false");
		doCommand("(set-option :produce-proofs false)", isTest? "success" :  "unsupported");
		doCommand("(get-option :produce-proofs)", "false");
	}
	
	@Test
	public void checkProduceModels() {
		doCommand("(get-option :produce-models)", 
				"false"
				);
	}
	
	@Test
	public void checkSetProduceModels() {
		boolean support = isTest || "z3".equals(solvername) || "cvc".equals(solvername);
		doCommand("(set-option :produce-models true)", support? "success" : "unsupported");
		doCommand("(get-option :produce-models)", support? "true" :  "false");
		doCommand("(set-option :produce-models false)", support? "success" : "unsupported");
		doCommand("(get-option :produce-models)", "false");
	}
	
	@Test
	public void checkProduceAssignments() {
		doCommand("(get-option :produce-assignments)", 
				"false"
				);
	}
	
	@Test
	public void checkSetProduceAssignments() {
		doCommand("(set-option :produce-assignments true)",isTest? "success" : "unsupported");
		doCommand("(get-option :produce-assignments)", isTest? "true" :"false");
		doCommand("(set-option :produce-assignments false)",isTest? "success" : "unsupported");
		doCommand("(get-option :produce-assignments)", "false");
	}
	
	@Test
	public void checkProduceUnsatCores() {
		doCommand("(get-option :produce-unsat-cores)", 
				"false"
				);
	}
	
	@Test
	public void checkSetProduceUnsatCores() {
		doCommand("(set-option :produce-unsat-cores true)",isTest? "success" :  "unsupported");
		doCommand("(get-option :produce-unsat-cores)", isTest? "true" : "false");
		doCommand("(set-option :produce-unsat-cores false)",isTest? "success" :  "unsupported");
		doCommand("(get-option :produce-unsat-cores)", "false");
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
		doCommand("(get-option :expand-definitions)", "true");
		doCommand("(set-option :expand-definitions false)", "success");
		doCommand("(get-option :expand-definitions)", "false");
	}
	
	@Test
	public void checkRandomSeed() {
		doCommand("(get-option :random-seed)", 
				"0"
				);
	}
	
	@Test
	public void checkSetRandomSeed() {
		doCommand("(set-option :random-seed 1)", "success");
		doCommand("(get-option :random-seed)", "1");
		doCommand("(set-option :random-seed 2)", "success");
		doCommand("(get-option :random-seed)", "2");
	}
	
	@Test
	public void checkVerbosity() {
		doCommand("(get-option :verbosity)", 
				"0"
				);
	}
	
	@Test
	public void checkSetVerbosity() {
		doCommand("(set-option :verbosity 1)", "success");
		doCommand("(get-option :verbosity)", "1");
		doCommand("(set-option :verbosity 2)", "success");
		doCommand("(get-option :verbosity)", "2");
	}
}

