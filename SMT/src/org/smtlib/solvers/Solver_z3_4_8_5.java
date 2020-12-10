package org.smtlib.solvers;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.attribute.PosixFilePermission;
import java.util.Set;
import org.smtlib.SMT;

public class Solver_z3_4_8_5 extends Solver_z3_4_5 {
  private static String resolvedExecutable = "";
  protected String NAME_VALUE = "z3-4.8.5";

  /** Creates an instance of the Z3 solver */
  public Solver_z3_4_8_5(final SMT.Configuration smtConfig, /*@NonNull*/ final String executable) {
    super(smtConfig, executable);
  }

  public Solver_z3_4_8_5(final SMT.Configuration smtConfig) {
    this(smtConfig, resolveExecutable());
  }

  /** Creates an instance of the Z3 solver */
  public Solver_z3_4_8_5(final SMT.Configuration smtConfig, /*@NonNull*/ final String[] command) {
    super(smtConfig, command);
  }

  private static String resolveExecutable() {
    final String os = System.getProperty("os.name").toLowerCase();
    final InputStream executable;
    final ClassLoader loader = Solver_z3_4_8_5.class.getClassLoader();
    String executableName = "z3-4.8.5";
    if (!resolvedExecutable.equals("")) {
      return resolvedExecutable;
    }
    if (os.contains("win")) {
      executable = loader.getResourceAsStream("windows/z3-4.8.5/z3-4.8.5.exe");
      executableName += ".exe";
    } else if (os.contains("mac")) {
      executable = loader.getResourceAsStream("mac/z3-4.8.5/z3-4.8.5.macosx");
      executableName += ".macosx";
    } else {
      executable = loader.getResourceAsStream("linux/z3-4.8.5/z3-4.8.5.linux");
      executableName += ".linux";
    }
    try {
      Path tmpSolverDir = Files.createTempDirectory("jSMTLIB-solver");
      Runtime.getRuntime().addShutdownHook(deleteTempDirWithContent(tmpSolverDir));
      Path newSolverPath = Paths.get(tmpSolverDir.toString(), executableName);
      Files.copy(executable, newSolverPath);
      executable.close();
      Set<PosixFilePermission> perms = Files.getPosixFilePermissions(newSolverPath);
      perms.add(PosixFilePermission.OWNER_EXECUTE);
      Files.setPosixFilePermissions(newSolverPath, perms);
      resolvedExecutable = newSolverPath.toString();
      return resolvedExecutable;
    } catch (IOException e) {
      e.printStackTrace();
      throw new RuntimeException("Failed to create Z3 4.8.5");
    }
  }

  private static Thread deleteTempDirWithContent(Path tmpSolverDir) {
    return new Thread(
        () -> {
          File tmpDir = tmpSolverDir.toFile();
          for (File f : tmpDir.listFiles()) {
            f.delete();
          }
          tmpDir.delete();
        });
  }
}
