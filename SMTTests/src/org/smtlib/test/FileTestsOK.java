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
import java.util.concurrent.TimeUnit;
import org.junit.Assert;
import org.junit.Assume;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.junit.runners.ParameterizedWithNames;

@RunWith(ParameterizedWithNames.class)
public class FileTestsOK extends LogicTests {

  static Collection<String[]> data = datax();

  @Rule
  public Timeout timeout =
      new Timeout(1, TimeUnit.MINUTES); // limit on entire test, not on each proof attempt

  protected String testfile;

  public FileTestsOK(String solvername, String testfile) {
    this.solvername = solvername;
    this.testfile = testfile;
  }

  @Parameters
  public static Collection<String[]> datax() {
    Collection<String[]> data = new ArrayList<String[]>(1000);
    File f = findTestsFolder();
    System.out.println(f.getAbsolutePath());
    String[] files = f.list();
    for (String ff : files) {
      if (ff.endsWith(".tst") && ff.startsWith("ok_regularOutput")) {
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
    Assert.assertFalse("err_tokens.tst".equals(testfile));
    Assert.assertFalse("ok_getInfo2.tst".equals(testfile) && "z3_4_5".equals(solvername));
    Assert.assertFalse(
        "err_namedExpr2.tst".equals(testfile)
            && "yices2".equals(solvername)); // FIXME - yices2 does not support Boolean quantifiers
    Assume.assumeFalse(
        "ok_regularOutput.tst".equals(testfile)
            && solvername.startsWith("z3")); // FIXME - appears to hang
    Assert.assertFalse(
        "err_declareFun.tst".equals(testfile)
            && "z3_4_5".equals(solvername)); // FIXME - appears to hang
    // TYhe above hang probably because no ojtput is sent to listen to

    //		System.out.println("File: " + testfile + "  Solver: " + solvername);
    String script = readFile(testfile);
    String outname = resolveFileName(testfile + ".out");
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
