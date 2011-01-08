package org.smtlib;

import java.io.*;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public class FileTests  extends LogicTests {

 static Collection<String[]> data = datax();
	
    @Parameters
    static public  Collection<String[]> datax() {
    	Collection<String[]> data = new ArrayList<String[]>(1000);
    	File f = new File("tests");
    	File[] files = f.listFiles();
    	for (File ff: files) { 
    		if (ff.getName().endsWith(".tst")) {
    			data.add(new String[]{"test",ff.getName()}); 
    			data.add(new String[]{"simplify",ff.getName()}); 
    			//data.add(new String[]{"yices",ff.getName()}); // FIXME - add other solvers - add them from array
    		}
    	}
//    	data.clear();
//		data.add(new String[]{"test","err_assertBadExpr.tst"}); 
    	return data;
    }
    
    String testfile;
    
//  public FileTests(String solvername) {
//	this.solvername = "test"; // solvername;  FIXME
//}
  public FileTests(String solvername, String testfile) {
	this.solvername = solvername; // solvername;  FIXME
	this.testfile = testfile; //data.iterator().next()[0];
}
  
	public String readFile(String filename) {
		char[] b = new char[100000];
		try {
			Reader r = new FileReader(filename);
			int i = 0;
			int ii = 0;
			while ((ii = r.read(b,i,b.length-i)) > 0) {
				i += ii;
				if (i >= b.length) throw new RuntimeException("File too large");
			}
			return new String(b,0,i);
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
	}
    
	@Test
	public void checkFile() {
		if ("ok_printSuccess.tst".equals(testfile)) return; // FIXME - skip this
		if ("ok_regularOutput.tst".equals(testfile)) return; // FIXME - skip this
		if ("ok_setRequiredOptions.tst".equals(testfile)) return; // FIXME - skip this
		String script = readFile("tests/" + testfile);
		String outname = "tests/" + testfile + ".out";
		String altname = outname + "." + solvername;
		if (new File(altname).isFile()) outname = altname;
		altname = altname + ".bad";
		if (new File(altname).isFile()) outname = altname;
		String output = readFile(outname);
		String actual = doScript(script);
		output = output.replace("\r\n","\n");
		actual = actual.replace("\r\n","\n");
		if (output.contains("error")) return; // FIXME - fix this along with error stuff
		Assert.assertEquals(output,actual);
	}
	
}