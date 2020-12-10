package org.smtlib.test;

import static org.smtlib.test.FileTestHelper.findTestsFolder;
import static org.smtlib.test.FileTestHelper.readFile;
import static org.smtlib.test.FileTestHelper.resolveFileName;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import org.junit.Assert;
import org.junit.Assume;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.junit.runners.ParameterizedWithNames;

@RunWith(ParameterizedWithNames.class)
public class FileTests extends LogicTests {

  static Collection<String[]> data = datax();
  protected String testfile;

  public FileTests(String solvername, String testfile) {
    this.solvername = solvername;
    this.testfile = testfile;
  }

  @Parameters
  public static Collection<String[]> datax() {
    Collection<String[]> data = new ArrayList<String[]>(1000);
    File f = findTestsFolder();
    String[] files = f.list();
    for (String ff : files) {
      if (ff.endsWith(".tst") && !ff.startsWith("ok")) {
        for (String s : solvers) {
          data.add(new String[] {s, ff});
        }
      }
    }
    return data;
  }

  static String shortname(String name) {
    if (name.startsWith("z3")) return "z3";
    return name;
  }

  @Test
  public void checkFile() {
    Assert.assertFalse("ok_getInfo2.tst".equals(testfile) && "z3_4_5".equals(solvername));
    Assert.assertFalse("ok_getInfo2.tst".equals(testfile) && "z3_4_6".equals(solvername));
    Assume.assumeFalse("ok_getInfo2.tst".equals(testfile) && "z3_4_8_5".equals(solvername));
    Assert.assertFalse("err_getInfo2.tst".equals(testfile) && "z3_4_5".equals(solvername));
    Assert.assertFalse("err_getInfo2.tst".equals(testfile) && "z3_4_6".equals(solvername));
    Assume.assumeFalse("err_getInfo2.tst".equals(testfile) && "z3_4_8_5".equals(solvername));
    Assert.assertFalse("err_setInfo3.tst".equals(testfile) && "z3_4_5".equals(solvername));
    Assert.assertFalse("err_setInfo3.tst".equals(testfile) && "z3_4_6".equals(solvername));
    Assume.assumeFalse("err_setInfo3.tst".equals(testfile) && "z3_4_8_5".equals(solvername));
    Assert.assertFalse("err_tokens.tst".equals(testfile) && "z3_4_3".equals(solvername));

    Assume.assumeTrue(
        !("err_declareFun.tst".equals(testfile)
            && "z3_4_5".equals(solvername))); // FIXME - appears to hang
    Assert.assertFalse(
        "err_declareFun.tst".equals(testfile) && "z3_4_6".equals(solvername)); // FIXME - hangs
    Assume.assumeFalse(
        "err_declareFun.tst".equals(testfile) && "z3_4_8_5".equals(solvername)); // FIXME - hangs

    Assume.assumeTrue(
        !("err_namedExpr2.tst".equals(testfile)
            && "yices2".equals(solvername))); // FIXME - yices2 does not support Boolean quantifiers
    Assume.assumeTrue(!("ok_regularOutput.tst".equals(testfile))); // FIXME - appears to hang
    Assume.assumeTrue(!("ok_getInfo2.tst".equals(testfile)));

    Assume.assumeFalse(
        "err_getProof3.tst".equals(testfile)
            && "z3_4_8_5".equals(solvername)); // FIXME Segfault in z3 4.8.5 not handled!

    //		System.out.println("File: " + testfile + "  Solver: " + solvername);
    String script = readFile(testfile);
    String outname = resolveFileName(testfile + ".out");
    if (outname.startsWith("tests")) {
      outname = resolveFileName(testfile) + ".out";
    }
    String altname = outname + "." + solvername;
    String altname2 = outname + "." + shortname(solvername);
    Assume.assumeTrue(!(new File(altname + ".skip").exists()));
    String[] names =
        new String[] {
          altname + "." + version + ".bad",
          altname + ".bad",
          altname + "." + version,
          altname2 + "." + version,
          altname2 + ".bad",
          altname,
          altname2,
          outname + "." + version + ".bad",
          outname + ".bad",
          outname + "." + version,
          outname
        };
    for (String name : names) {
      if (new File(name).exists()) {
        outname = name;
        break;
      }
    }
    File actualFile =
        new File(resolveFileName(testfile + ".out." + solvername + "." + version + ".actual"));
    String actual = doScript(script).replace("\r\n", "\n");
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
      String output = readFile(outname).replace("\r\n", "\n");
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
      Assert.assertEquals(output, actual);
    }
  }
}
