package org.smtlib.test;

import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;

public class FileTestHelper {
  public static File findTestsFolder() {
    // This is slightly hacked, as it relies on the existence of 'err_array.tst' to reach the right
    // directory.
    try {
      String resource = FileTests.class.getClassLoader().getResource("err_array.tst").getPath();
      if (resource == null) {
        resource = "tests/";
      } else {
        resource = new File(resource).getParent();
      }
      return new File(resource);
    } catch (Exception e) {
      return new File("/Users/davidcok/cok/projects/jSMTLIB/SMTTests/tests");
    }
  }

  /**
   * Packaging the jar along with the resources allows to read files form the resource folder. This
   * method determines whether it can read the file from the resource folder and tries the old
   * location otherwise.
   *
   * @param filename file that should be read from resource folder
   * @return path to file
   */
  public static String resolveFileName(final String filename) {
    final String resolvedFile;
    if (new File(filename).exists()) {
      resolvedFile = filename;
    } else if (FileTestHelper.class.getClassLoader().getResource(filename) == null) {
      resolvedFile = "tests/" + filename;
    } else {
      resolvedFile = FileTestHelper.class.getClassLoader().getResource(filename).getPath();
    }
    return resolvedFile;
  }

  /** Reads a file into a String */
  public static String readFile(String filename) {
    char[] b = new char[100000];
    Reader r = null;
    try {
      r = new FileReader(resolveFileName(filename));
      int i = 0;
      int ii = 0;
      while ((ii = r.read(b, i, b.length - i)) > 0) {
        i += ii;
        if (i >= b.length) throw new RuntimeException("File too large");
      }
      return new String(b, 0, i);
    } catch (IOException e) {
      throw new RuntimeException(e);
    } finally {
      if (r != null)
        try {
          r.close();
        } catch (IOException ee) {
        }
    }
  }
}
