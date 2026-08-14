package org.smtlib.test;

import java.util.List;

import org.junit.Assert;
import org.junit.Assume;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.*;
import org.smtlib.IResponse;
import org.smtlib.SMT;
import org.smtlib.SMT.Configuration.SMTLIB;
import org.smtlib.Utils;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.impl.Response;

@RunWith(ParameterizedWithNames.class)
public class InfoOptions  extends LogicTests {

	boolean isTest;
	/** True for the minimal AbstractSolver-based adapter used by recent z3 releases
	 *  (Solver_z3_recent, registered as "z3-VERSION" -- distinct from the legacy z3_4_x
	 *  adapters, which carry their own client-side workarounds). "z3-4.3" is excluded even
	 *  though it now shares the same dash-prefixed naming convention: it still resolves to
	 *  the legacy Solver_z3_4_3 adapter, not Solver_z3_recent. */
	boolean isZ3Recent;
	/** True for yices2-2.6.5/2.7.0 (registered as "yices2-VERSION") -- distinct from the
	 *  bare "yices2" name, whose behavior these checks otherwise assume. */
	boolean isYices2Recent;
	/** True for smtinterpol-2.5 (Solver_smtinterpol, a Java solver launched as
	 *  "java -jar ..."). */
	boolean isSmtInterpol;

    public InfoOptions(String solvername, String version) {
    	this.solvername = solvername;
    	this.version = version;
    	this.isTest = "test".equals(solvername);
    	this.isZ3Recent = solvername.startsWith("z3-") && !solvername.equals("z3-4.3");
    	this.isYices2Recent = solvername.startsWith("yices2-");
    	this.isSmtInterpol = solvername.startsWith("smtinterpol");
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
				: solvername.startsWith("yices2-") ? "Bruno Dutertre, Dejan Jovanović, Ian A. Mason, Stéphane Graham-Lengrand"
				: solvername.startsWith("yices") ? "Bruno Dutertre"
				: solvername.equals("cvc") ? "Clark Barrett, Cesare Tinelli, and others"
				: solvername.startsWith("cvc") ? null // Long text that we don't check // TODO
				: solvername.equals("z3-4.3") || solvername.startsWith("z3_4_3") ? "Leonardo de Moura and Nikolaj Bjorner"
				: solvername.startsWith("z3_") ? "Leonardo de Moura, Nikolaj Bjorner and Christoph Wintersteiger"
				: solvername.equals("z3-4.14.1") ? "Leonardo de Moura, Nikolaj Bjorner, Lev Nachmanson and Christoph Wintersteiger"
				: solvername.equals("z3-4.16.0") ? "Leonardo de Moura, Nikolaj Bjorner, Lev Nachmanson and Christoph Wintersteiger"
				: isZ3Recent ? "Leonardo de Moura, Nikolaj Bjorner and Christoph Wintersteiger" // z3-4.8.12/4.10.2/4.12.6: authors text before "Lev Nachmanson" was added
				: solvername.startsWith("z3") ? "Leonardo de Moura and Nikolaj Bjorner"
				: isSmtInterpol ? "Juergen Christ, Jochen Hoenicke, Alexander Nutz, and Tanja Schindler"
				: "???" )
				);
	}

	@Test
	public void checkVersion() {
		checkGetInfo(":version",
				(solvername.equals("test") ? "0.0"
				: solvername.equals("simplify") ? "1.5.4"
				: solvername.equals("yices2") ? "2.3.1"
				: solvername.equals("yices2-2.6.5") ? "2.6.5"
				: solvername.equals("yices2-2.7.0") ? "2.7.0"
				: solvername.equals("cvc5") ? "1.8"
				: solvername.equals("cvc5") ? "0.0.2"
				: solvername.equals("cvc5-1.3.2") ? "1.3.2"
				: solvername.equals("z3-4.3") ? "4.3"
				: solvername.equals("z3_4_3_2") ? "4.3.2"
				: solvername.equals("z3_4_4") ? "4.4.0"
				: solvername.equals("z3_4_5") ? "4.5.0"
				: solvername.equals("z3_4_6") ? "4.6.0"
				: solvername.equals("z3_4_7") ? "4.7.1"
				: solvername.equals("z3_4_8") ? "4.8.12"
				: solvername.equals("z3_2_11") ? "2.11"
				: solvername.equals("z3-4.8.12") ? "4.8.12"
				: solvername.equals("z3-4.10.2") ? "4.10.2"
				: solvername.equals("z3-4.12.6") ? "4.12.6"
				: solvername.equals("z3-4.14.1") ? "4.14.1"
				: solvername.equals("z3-4.16.0") ? "4.16.0"
				: isSmtInterpol ? "2.5-1453-gedae1f37"
				: "???" )
				);
	}

	@Test
	public void checkName() {
		checkGetInfo(":name",
						solvername.equals("test") ? "test"
						: solvername.equals("simplify") ? "simplify"
						: isSmtInterpol ? "SMTInterpol"
						: solvername.startsWith("yices2") ? "Yices"
						: solvername.equals("cvc") ? "CVC3"
						: solvername.startsWith("cvc5") ? "cvc5"
						: solvername.startsWith("cvc5") ? "cvc5"
						: solvername.equals("z3_2_11") ? "z3-2.11"
						: solvername.startsWith("z3") ? "Z3"
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
//				solvername.equals("z3_4_4") ? "success" :
				solvername.equals("yices2") || isYices2Recent ? "(error \"can't overwrite :name\")" :
				solvername.equals("cvc5-1.3.2") ? "success" : // cvc5-1.3.2 permits setting pre-defined info keywords
				isZ3Recent ? "success" : // z3-4.8.12+ silently accepts (and ignores) this rather than erroring -- a real non-conformance
				isSmtInterpol ? "success" : // smtinterpol-2.5 silently accepts (and ignores) this rather than erroring -- a real non-conformance
				"(error \"Setting the value of a pre-defined keyword is not permitted: :name\")");
	}

	@Test
	public void checkSetAuthors() {
		doCommand("(set-info :authors \"xx\")",
//				solvername.equals("z3_4_4") ? "success" :
				solvername.equals("yices2") || isYices2Recent ?
				"(error \"can't overwrite :authors\")" :
				solvername.equals("cvc5-1.3.2") ? "success" : // cvc5-1.3.2 permits setting pre-defined info keywords
				isZ3Recent ? "success" : // z3-4.8.12+ silently accepts (and ignores) this rather than erroring -- a real non-conformance
				isSmtInterpol ? "success" : // smtinterpol-2.5 silently accepts (and ignores) this rather than erroring -- a real non-conformance
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
		// The correct result is a quote-delimited string
		doCommand("(get-option :regular-output-channel)",
						solvername.equals("cvc5-1.3.2") || isZ3Recent ? "stdout" : // returned unquoted, before any set-option
						"\"stdout\""
				);
	}
	
	@Test
	public void checkSetRegularOutput() {
		Assume.assumeTrue(false);
		doCommand("(set-option :regular-output-channel \"test-output\")", "success"); // FIXME - writes success to test-output? - hangs for z3-4.3 ?
		doCommand("(get-option :regular-output-channel)", "\"test-output\"");
		doCommand("(set-option :regular-output-channel \"stdout\")", "success");
		doCommand("(get-option :regular-output-channel)", "\"stdout\"");
	}
	
	@Test
	public void checkDiagnosticOutput() {
		// The correct result is a quote-delimited string
		doCommand("(get-option :diagnostic-output-channel)",
//				solvername.startsWith("cvc5")? "unsupported" :
						solvername.equals("cvc5-1.3.2") || isZ3Recent ? "stderr" : // returned unquoted, before any set-option
						"\"stderr\""
				);
	}
	
	@Test
	public void checkSetDiagnosticOutput() {
		Assume.assumeTrue(false);
		doCommand("(set-option :regular-diagnostic-channel \"test-output\")", "success"); // FIXME - writes success to test-output? - hangs for z3-4.3 ?
		doCommand("(get-option :regular-diagnostic-channel)", "\"test-output\"");
		doCommand("(set-option :regular-diagnostic-channel \"stderr\")", "success");
		doCommand("(get-option :regular-diagnostic-channel)", "\"stderr\"");
	}
	
    @Test
    public void checkInteractiveMode() {
        Assume.assumeTrue(version.equals("V2.0")||version.equals("V2.5"));
        boolean supported = !solvername.equals("yices2") && !isYices2Recent && !solvername.equals("cvc5");
        doCommand("(get-option :interactive-mode)",
                !supported ? "unsupported" :
                solvername.equals("cvc5-1.3.2") ? "true" : // cvc5-1.3.2 defaults this true (a side effect of the required --interactive startup flag)
                "false"
                );
    }
    
    @Test
    public void checkProduceAssertions() {
        Assume.assumeTrue(!version.equals("V2.0")&&!version.equals("V2.5"));
        boolean supported = !solvername.equals("yices2") && !isYices2Recent;
        doCommand("(get-option :produce-assertions)",
                !supported ? "unsupported" :
                solvername.equals("cvc5-1.3.2") ? "true" : // cvc5-1.3.2 defaults this true (a side effect of the required --interactive startup flag)
                "false"
                );
    }
    
    @Test
    public void checkSetInteractiveMode() {
        Assume.assumeTrue(version.equals("V2.0")||version.equals("V2.5"));
        boolean supported = !solvername.equals("yices2") && !isYices2Recent && !solvername.equals("cvc5");
        doCommand("(set-option :interactive-mode true)",
                !supported ? "unsupported" :
                "success");
        doCommand("(get-option :interactive-mode)", 
                !supported ? "unsupported" :
                "true");
        doCommand("(set-option :interactive-mode false)", 
                !supported ? "unsupported" :
                "success");
        doCommand("(get-option :interactive-mode)", 
                !supported ? "unsupported" :
                "false");
    }
    
    @Test
    public void checkSetProduceAssertions() {
        Assume.assumeTrue(!version.equals("V2.0")&&!version.equals("V2.5"));
        doCommand("(set-option :produce-assertions true)", 
                solvername.equals("yices2") || isYices2Recent ? "unsupported" :
                "success");
        doCommand("(get-option :produce-assertions)",
                solvername.equals("yices2") || isYices2Recent ? "unsupported" :
                "true");
        doCommand("(set-option :produce-assertions false)",
                solvername.equals("yices2") || isYices2Recent ? "unsupported" :
                "success");
        doCommand("(get-option :produce-assertions)",
                solvername.equals("yices2") || isYices2Recent ? "unsupported" :
                "false");
    }
    
	@Test
	public void checkProduceProofs() {
		boolean supported = !solvername.equals("yices2") && !isYices2Recent;
		doCommand("(get-option :produce-proofs)",
				!supported ? "unsupported" : "false"
				);
	}
	
	@Test
	public void checkSetProduceProofs() {
		boolean supported = isTest ||  solvername.startsWith("z3_")
		                        || isZ3Recent
		                        || isSmtInterpol
		                        || solvername.startsWith("cvc");
		doCommand("(set-option :produce-proofs true)", 
				supported ? "success" 
						: solvername.startsWith("cvc5")? "success"
						:  "unsupported");
		doCommand("(get-option :produce-proofs)",
				supported ? "true"
			    : solvername.equals("yices2") || isYices2Recent ? "unsupported"
				:  "false");
		doCommand("(set-option :produce-proofs false)",
				supported ? "success"
						: solvername.startsWith("cvc5")? "success"
						:  "unsupported");
		doCommand("(get-option :produce-proofs)",
			    solvername.equals("yices2") || isYices2Recent ? "unsupported" :
				"false");
	}
	
	@Test
	public void checkProduceModels() {
		doCommand("(get-option :produce-models)",
		        solvername.equals("cvc5-1.3.2") ? "false" : // defaults false here; other cvc-family adapters force it on via a startup flag
		        solvername.startsWith("cvc") ? "true" : // FIXME - is this automatically true?
		        isZ3Recent ? "true" : // z3-4.8.12+ defaults this true, not the spec's false -- no known CLI flag to change it
				"false"
				);
	}
	
	@Test
	public void checkSetProduceModels() {
		boolean support = isTest || solvername.startsWith("z3") || solvername.startsWith("cvc") || "yices2".equals(solvername) || isYices2Recent || isSmtInterpol;
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
		boolean supported = isTest || solvername.startsWith("cvc") || solvername.equals("yices2") || isYices2Recent || solvername.startsWith("z3_") || isZ3Recent || isSmtInterpol ;

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
		boolean unsupported = solvername.equals("yices2");
		doCommand("(get-option :produce-unsat-cores)", 
				unsupported ? "unsupported" : "false"
				);
	}
	
	@Test
	public void checkSetProduceUnsatCores() {
		Assume.assumeTrue(!solvername.equals("cvc5b"));
		boolean supported = isYices2Recent || (!solvername.equals("z3-4.3") && !solvername.startsWith("yices"));
		doCommand("(set-option :produce-unsat-cores true)",
				supported ? "success" 
						:  "unsupported");
		doCommand("(get-option :produce-unsat-cores)", 
				solvername.equals("yices2") ? "unsupported" :
				supported? "true" 
						: "false");
		doCommand("(set-option :produce-unsat-cores false)",
				supported? "success" 
						:  "unsupported");
		doCommand("(get-option :produce-unsat-cores)",
				solvername.equals("yices2") ? "unsupported" :
				isZ3Recent ? "true" : // genuine z3-4.8.12+ bug: get-option keeps reporting the earlier "true" even after this set to false
				"false"
				);
	}
	
	@Test
	public void checkExpandDefinitions() {
		//boolean supported = smt.smtConfig.isVersion(SMT.Configuration.SMTLIB.V20) && !solvername.equals("yices2");
		boolean supported = !solvername.equals("yices2");
		supported |= solvername.startsWith("cvc5"); // cvc5 supports option in V2.5
		supported &= !solvername.equals("cvc5-1.3.2"); // cvc5-1.3.2 does not implement this deprecated V2.0-era option
		supported &= !isZ3Recent; // z3-4.8.12+ does not implement this deprecated option (self-consistently unsupported for both get and set)
		supported &= !isYices2Recent; // yices2-2.6.5+ does not implement this deprecated option either
		supported &= !isSmtInterpol; // smtinterpol-2.5 does not implement this deprecated option either
		doCommand("(get-option :expand-definitions)",
				supported ? "false" : "unsupported"
				);
	}
		
	@Test
	public void checkSetExpandDefinitions() {
		boolean supported = smt.smtConfig.isVersion(SMT.Configuration.SMTLIB.V20) && !solvername.equals("yices2") && !solvername.equals("z3_4_4") && !solvername.equals("z3_4_5");
		supported = true; // FIXME - it is optional, but it is permitted to set
		supported &= !solvername.equals("cvc5-1.3.2"); // cvc5-1.3.2 does not implement this deprecated V2.0-era option
		supported &= !isZ3Recent; // z3-4.8.12+ does not implement this deprecated option (self-consistently unsupported for both get and set)
		supported &= !isYices2Recent; // yices2-2.6.5+ does not implement this deprecated option either
		supported &= !isSmtInterpol; // smtinterpol-2.5 does not implement this deprecated option either
		doCommand("(set-option :expand-definitions true)",
				!supported ? "unsupported" : "success");
		doCommand("(get-option :expand-definitions)",
				!supported ? "unsupported" : "true");
		doCommand("(set-option :expand-definitions false)",
				!supported ? "unsupported" : "success");
		doCommand("(get-option :expand-definitions)",
				!supported ? "unsupported" : "false");
	}
	
	@Test
	public void checkRandomSeed() {
		Assume.assumeTrue(!"cvc5".equals(solvername)); // FIXME - cvc5 does not handle random seed correctly
		doCommand("(get-option :random-seed)",
				isSmtInterpol ? "11350294" : // smtinterpol-2.5's default is some fixed non-zero value, not the spec's 0 -- but deterministic (confirmed across repeated runs)
				"0"
				);
	}
	
	@Test
	public void checkSetRandomSeed() {
		Assume.assumeTrue(!"cvc5".equals(solvername)); // FIXME - cvc5 does not handle random seed correctly
		doCommand("(set-option :random-seed 1)", "success");
		doCommand("(get-option :random-seed)", 
				"cvc5".equals(solvername) ? "0" :
				"1");
		doCommand("(set-option :random-seed 2)", "success");
		doCommand("(get-option :random-seed)", 
				"cvc5".equals(solvername) ? "0" :
				"2");
	}
	
	@Test
	public void checkVerbosity() {
		doCommand("(get-option :verbosity)",
		        "cvc5".equals(solvername) ? "-1" : // FIXME - why this difference
		        "cvc5-1.3.2".equals(solvername) ? "-1" :
		        isSmtInterpol ? "2" : // smtinterpol-2.5's default is 2, not the spec's 0
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

