package org.smtlib.test;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Reader;
import java.util.ArrayList;
import java.util.Collection;

import org.junit.Assert;
import org.junit.Assume;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.ParameterizedWithNames;
import org.junit.runners.Parameterized.Parameters;

@RunWith(ParameterizedWithNames.class)
public class FileTests  extends LogicTests {

	static Collection<String[]> data = datax();
	
    @Parameters
    static public  Collection<String[]> datax() {
    	Collection<String[]> data = new ArrayList<String[]>(1000);
    	File f = new File("tests");
    	String[] files = f.list();
    	for (String ff: files) { 
    		if (ff.endsWith(".tst")) {
    			for (String[] s : solvers) {
    				data.add(new String[]{s[0],ff});
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
    
    public FileTests(String solvername, String testfile) {
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
    
	@Test
	public void checkFile() {
		Assume.assumeTrue(!("err_namedExpr2.tst".equals(testfile) && "yices2".equals(solvername))); // FIXME - yices2 does not support Boolean quantifiers
		Assume.assumeTrue(!("ok_regularOutput.tst".equals(testfile))); // FIXME - appears to hang

		
//		System.out.println("File: " + testfile + "  Solver: " + solvername);
		String script = readFile("tests/" + testfile);
		String outname = "tests/" + testfile + ".out";
		String altname = outname + "." + solvername;
		Assume.assumeTrue(! (new File(altname + ".skip").exists()) );
		if (new File(altname).isFile()) outname = altname;
		else if (new File(altname.replace("z3_4_3", "z3")).isFile()) outname = altname.replace("z3_4_3", "z3");
		else if (new File(altname.replace("z3_2_11", "z3")).isFile()) outname = altname.replace("z3_2_11", "z3");
		altname = altname + ".bad";
		if (new File(altname).isFile()) outname = altname;
		else if (new File(altname.replace("z3_4_3", "z3")).isFile()) outname = altname.replace("z3_4_3", "z3");
		else if (new File(altname.replace("z3_2_11", "z3")).isFile()) outname = altname.replace("z3_2_11", "z3");
		File actualFile = new File("tests/" + testfile + ".out." + solvername + ".actual");
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