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

	private static File findTestsFolder() {
		//This is slightly hacked, as it relies on the existence of 'err_array.tst' to reach the right directory.
	    try {
	        String resource = FileTests.class.getClassLoader().getResource("err_array.tst").getPath();
	        if (resource == null) {
	            resource = "tests/";
	        } else {
	            resource = new File(resource).getParent();
	        }
	        return new File(resource);
	    } catch (Exception e) {
	        return new File ("/Users/davidcok/cok/projects/jSMTLIB/SMTTests/tests");
	    }
	}

	@Parameters
    static public  Collection<String[]> datax() {
    	Collection<String[]> data = new ArrayList<String[]>(1000);
		File f = findTestsFolder();
    	String[] files = f.list();
    	for (String ff: files) { 
    		if (ff.endsWith(".tst") && !ff.startsWith("ok")) {
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
    
    public FileTests(String solvername, String testfile) {
    	this.solvername = solvername;
    	this.testfile = testfile;
    }

	/**
	 * Packaging the jar along with the resources allows to read files form the resource folder. This method determines
	 * whether it can read the file from the resource folder and tries the old location otherwise.
	 *
	 * @param filename file that should be read from resource folder
	 * @return path to file
	 */
	private String resolveFileName(final String filename) {
		final String resolvedFile;
		if (new File(filename).exists()) {
			resolvedFile = filename;
		} else if (this.getClass().getClassLoader().getResource(filename) == null) {
			resolvedFile = "tests/" + filename;
		} else {
			resolvedFile = this.getClass().getClassLoader().getResource(filename).getPath();
		}
		return resolvedFile;
	}

	/**
	 * Reads a file into a String
	 */
	public String readFile(String filename) {
		char[] b = new char[100000];
		Reader r = null;
		try {
			r = new FileReader(resolveFileName(filename));
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
        Assert.assertFalse("ok_getInfo2.tst".equals(testfile) && "z3_4_5".equals(solvername));
        Assert.assertFalse("ok_getInfo2.tst".equals(testfile) && "z3_4_6".equals(solvername));
		Assert.assertFalse("ok_getInfo2.tst".equals(testfile) && "z3_4_8_5".equals(solvername));
        Assert.assertFalse("err_getInfo2.tst".equals(testfile) && "z3_4_5".equals(solvername));
        Assert.assertFalse("err_getInfo2.tst".equals(testfile) && "z3_4_6".equals(solvername));
		Assert.assertFalse("err_getInfo2.tst".equals(testfile) && "z3_4_8_5".equals(solvername));
        Assert.assertFalse("err_setInfo3.tst".equals(testfile) && "z3_4_5".equals(solvername));
        Assert.assertFalse("err_setInfo3.tst".equals(testfile) && "z3_4_6".equals(solvername));
		Assert.assertFalse("err_setInfo3.tst".equals(testfile) && "z3_4_8_5".equals(solvername));
		Assert.assertFalse("err_tokens.tst".equals(testfile) && "z3_4_3".equals(solvername));

		Assume.assumeTrue(!("err_declareFun.tst".equals(testfile) &&
							"z3_4_5".equals(solvername))); // FIXME - appears to hang
		Assert.assertFalse("err_declareFun.tst".equals(testfile) && "z3_4_6".equals(solvername));  // FIXME - hangs
		Assert.assertFalse("err_declareFun.tst".equals(testfile) && "z3_4_8_5".equals(solvername));  // FIXME - hangs

		Assume.assumeTrue(!("err_namedExpr2.tst".equals(testfile) && "yices2".equals(solvername))); // FIXME - yices2 does not support Boolean quantifiers
		Assume.assumeTrue(!("ok_regularOutput.tst".equals(testfile))); // FIXME - appears to hang
		Assume.assumeTrue(!("ok_getInfo2.tst".equals(testfile)));

		Assume.assumeFalse("err_getProof3.tst".equals(testfile) &&
						   "z3_4_8_5".equals(solvername)); //FIXME Segfault in z3 4.8.5 not handled!
		
//		System.out.println("File: " + testfile + "  Solver: " + solvername);
		String script = readFile(testfile);
		String outname = resolveFileName(testfile + ".out");
		String altname = outname + "." + solvername;
		String altname2 = outname + "." + shortname(solvername);
		Assume.assumeTrue(! (new File(altname + ".skip").exists()) );
		String[] names = new String[]{ altname + "." + version + ".bad", altname + ".bad", altname + "." + version, altname2 + "." + version, altname2 + ".bad", altname, altname2, outname + "." + version + ".bad", outname + ".bad", outname  + "." + version, outname};
		for (String name: names) {
			if (new File(name).exists()) { outname = name; break; }
		}

		File actualFile = new File(resolveFileName(testfile + ".out." + solvername + "." + version + ".actual"));
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
