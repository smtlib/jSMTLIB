package org.smtlib.test;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Reader;
import java.util.ArrayList;
import java.util.Collection;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Assume;
import org.junit.Test;
import org.junit.Rule;
import org.junit.rules.Timeout;
import org.junit.runner.RunWith;
import org.junit.runners.ParameterizedWithNames;
import org.junit.runners.Parameterized.Parameters;

@RunWith(ParameterizedWithNames.class)
public class FileTestsOK  extends LogicTests {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES); // limit on entire test, not on each proof attempt

	static Collection<String[]> data = datax();
	
    @Parameters
    static public  Collection<String[]> datax() {
    	Collection<String[]> data = new ArrayList<String[]>(1000);
    	File f = new File("tests");
    	String[] files = f.list();
    	for (String ff: files) { 
    		if (ff.endsWith(".tst") && ff.startsWith("ok")) {
    			for (String s : solvers) {
    				data.add(new String[]{s,ff});
    			}
    		}
//    		if (ff.getName().endsWith(".tst")) {
//    			data.add(new String[]{"test",ff.getName()}); 
//    			if (
//    					!ff.getName().equals("err_getValueTypes.tst") // Crashes CVC4
//    					&& !ff.getName().equals("err_setLogic.tst")
//				) {
//    			data.add(new String[]{"cvc4",ff.getName()}); 
//    			}
//    			data.add(new String[]{"simplify",ff.getName()}); 
//    			if (
//    					!ff.getName().equals("ok_regularOutput.tst") &&
//    					!ff.getName().equals("err_bv2.tst") &&
//    					!ff.getName().equals("err_bv.tst") &&
//    					!ff.getName().equals("ok_bv2.tst") 
//    					) {
//    				data.add(new String[]{"z3_4_3",ff.getName()}); // FIXME - z3 crashes or hangs or is non-deterministic 
//    			}
////    			if (
////    					!ff.getName().equals("err_namedExpr2.tst")
////    					) {
////    				data.add(new String[]{"z3_2_11",ff.getName()}); // FIXME - z3 crashes 
////    			}
////    			data.add(new String[]{"cvc",ff.getName()}); 
////    			data.add(new String[]{"yices",ff.getName()});
////    			data.add(new String[]{"yices2",ff.getName()});
//    		}
    	}
//    	data.clear();
//		data.add(new String[]{"yices","ok_ite.tst"}); 
    	return data;
    }
    
    protected String testfile;
    
    public FileTestsOK(String solvername, String testfile) {
        this.solvername = solvername;
        this.testfile = testfile;
    }
  
    /** Reads a file into a String */
	public String readFile(String filename) {
		char[] b = new char[100000];
		Reader r = null;
		try {
			r = new FileReader(filename);
			int i = 0;
			int ii = 0;
			while ((ii = r.read(b,i,b.length-i)) > 0) {
				i += ii;
				if (i >= b.length) throw new RuntimeException("File too large");
			}
			return new String(b,0,i);
		} catch (IOException e) {
			throw new RuntimeException(e);
		} finally {
			if (r != null) try { r.close(); } catch (IOException ee) {}
		}
	}
	
	static String shortname(String name) {
		if (name.startsWith("z3")) return "z3";
		return name;
	}
    
	@Test
	public void checkFile() {
		Assert.assertFalse("err_tokens.tst".equals(testfile));
		Assert.assertFalse("ok_getInfo2.tst".equals(testfile) && "z3_4_5".equals(solvername));
		Assert.assertFalse("err_namedExpr2.tst".equals(testfile) && "yices2".equals(solvername)); // FIXME - yices2 does not support Boolean quantifiers
		Assert.assertFalse("ok_regularOutput.tst".equals(testfile) && solvername.startsWith("z3")); // FIXME - appears to hang
		Assert.assertFalse("err_declareFun.tst".equals(testfile) && "z3_4_5".equals(solvername)); // FIXME - appears to hang
// TYhe above hang probably because no ojtput is sent to listen to
		
//		System.out.println("File: " + testfile + "  Solver: " + solvername);
		String script = readFile("tests/" + testfile);
		String outname = "tests/" + testfile + ".out";
		String altname = outname + "." + solvername;
		String altname2 = outname + "." + shortname(solvername);
		Assume.assumeTrue(! (new File(altname + ".skip").exists()) );
		String[] names = new String[]{ altname + "." + version + ".bad", altname + ".bad", altname + "." + version, altname2 + "." + version, altname2 + ".bad", altname, altname2, outname + "." + version + ".bad", outname + ".bad", outname  + "." + version, outname};
		for (String name: names) {
			if (new File(name).exists()) { outname = name; break; }
		}

		File actualFile = new File("tests/" + testfile + ".out." + solvername + "." + version + ".actual");
		String actual = doScript(script).replace("\r\n","\n");
		if (!new File(outname).exists()) {
			try {
				BufferedWriter w = new BufferedWriter(new FileWriter(actualFile));
				w.write(actual);
				w.close();
			} catch (IOException e) {
				// ignore
			}
			Assert.fail("No output file found");
		} else {
			String output = readFile(outname).replace("\r\n","\n");
			if (!output.equals(actual)) {
				try {
					BufferedWriter w = new BufferedWriter(new FileWriter(actualFile));
					w.write(actual);
					w.close();
				} catch (IOException e) {
					// ignore
				}
			} else {
				if (actualFile.exists()) actualFile.delete();
			}
			output = testfile + " " + solvername + "\n" + output;
			actual = testfile + " " + solvername + "\n" + actual;
			Assert.assertEquals(output,actual);
		}
	}
}