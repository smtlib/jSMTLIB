package org.smtlib;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

@RunWith(Parameterized.class)
public class InfoOptions  extends LogicTests {

    public InfoOptions(String solvername) {
    	this.solvername = "test"; // solvername; FIXME
    }
    
	@Test
	public void checkAuthors() {
		doCommand("(get-info :authors)","(:authors \"" + 
				(solvername.equals("test") ? "David R. Cok"
				: solvername.equals("simplify") ? ""
				: solvername.equals("yices") ? ""
				: solvername.equals("cvc") ? ""
				: solvername.equals("z3") ? ""
				: "???" )
				+ "\" )");
	}
    
	@Test
	public void checkVersion() {
		doCommand("(get-info :version)","(:version \"" + 
				(solvername.equals("test") ? "0.0"
				: solvername.equals("simplify") ? "0.0"
				: solvername.equals("yices") ? "0.0"
				: solvername.equals("cvc") ? "0.0"
				: solvername.equals("z3") ? "0.0"
				: "???" )
				+ "\" )");
	}
    
	@Test
	public void checkName() {
		doCommand("(get-info :name)","(:name \"" + 
				(solvername.equals("test") ? "test"
				: solvername.equals("simplify") ? "simplify"
				: solvername.equals("yices") ? "yices"
				: solvername.equals("cvc") ? ""
				: solvername.equals("z3") ? "Z3"
				: "???" )
				+ "\" )");
	}
    
	// FIXME - no sure what this really should be
	@Test
	public void checkErrorBehavior() {
		doCommand("(get-info :error-behavior)","(:error-behavior continued-execution )");
	}
	
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
		doCommand("(set-option :produce-proofs true)", "success");
		doCommand("(get-option :produce-proofs)", "true");
		doCommand("(set-option :produce-proofs false)", "success");
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
		doCommand("(set-option :produce-models true)", "success");
		doCommand("(get-option :produce-models)", "true");
		doCommand("(set-option :produce-models false)", "success");
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
		doCommand("(set-option :produce-assignments true)", "success");
		doCommand("(get-option :produce-assignments)", "true");
		doCommand("(set-option :produce-assignments false)", "success");
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
		doCommand("(set-option :produce-unsat-cores true)", "success");
		doCommand("(get-option :produce-unsat-cores)", "true");
		doCommand("(set-option :produce-unsat-cores false)", "success");
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

