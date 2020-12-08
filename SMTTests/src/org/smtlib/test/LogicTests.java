package org.smtlib.test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Properties;
import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.runners.Parameterized.Parameters;
import org.smtlib.ICommand;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IParser;
import org.smtlib.IParser.ParserException;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.ISource;
import org.smtlib.SMT;

public class LogicTests {
  public static final String[] solvers =
      new String[] {
        "test",
        //          "z3_4_3",
        "z3_4_8_5",
        //           "z3_4_5",
        //          "z3_4_6",
        //          "z3_4_7",
        // "yices",
        //            "cvc4",
        //            "simplify",
      };
  static final int v20 = 0;
  static final int v25 = 1;
  static final int v26 = 2;
  static int smtlib_version = v20;
  String solvername;
  IParser p;
  ISolver solver;
  SMT smt;
  JUnitListener listener;
  String version;

  @Parameters
  public static Collection<String[]> data() {
    List<String[]> list = new ArrayList<>(solvers.length * 3);
    for (String solver : solvers) {
      list.add(new String[] {solver, "V2.0"});
      list.add(new String[] {solver, "V2.5"});
    }
    return list;
  }

  @Before
  public void setup() {
    // System.out.println(solvername);
    init();
  }

  @After
  public void teardown() {}

  private void loadSimplifyBinary(Properties props) {
    final String os = System.getProperty("os.name").toLowerCase();
    final String solver_binary_location;
    final ClassLoader loader = this.getClass().getClassLoader();

    if (os.contains("win")) {
      solver_binary_location = loader.getResource("windows/Simplify-1.5.4.exe").getPath();
    } else if (os.contains("mac")) {
      solver_binary_location = loader.getResource("mac/Simplify-1.5.5.macosx").getPath();
    } else {
      solver_binary_location = loader.getResource("linux/Simplify-1.5.4.linux").getPath();
    }
    props.setProperty("org.smtlib.solver_simplify.exec", solver_binary_location);
  }

  private void loadZ3Binary(Properties props) {
    final String os = System.getProperty("os.name").toLowerCase();
    final String solver_binary_location;
    final ClassLoader loader = this.getClass().getClassLoader();

    if (os.contains("win")) {
      solver_binary_location = loader.getResource("windows/z3-4.8.5/z3-4.8.5.exe").getPath();
    } else if (os.contains("mac")) {
      solver_binary_location = loader.getResource("mac/z3-4.8.5/z3-4.8.5.macosx").getPath();
    } else {
      solver_binary_location = loader.getResource("linux/z3-4.8.5/z3-4.8.5.linux").getPath();
    }
    props.setProperty("org.smtlib.solver_z3_4_8_5.exec", solver_binary_location);
  }

  private Properties readPropertiesAndAddDefaults(SMT smt) {
    Properties props = smt.readProperties();
    if (props.isEmpty()) {
      loadSimplifyBinary(props);
      loadZ3Binary(props);
    }
    return props;
  }

  public void init() {
    SMT.Configuration.smtlib = version;
    smt = new SMT();
    // We're not reading the command-line so we have to set items ourselves
    // Executable paths are taken from the properties
    smt.props = readPropertiesAndAddDefaults(smt);
    listener = new JUnitListener();
    smt.smtConfig.log.clearListeners();
    smt.smtConfig.log.addListener(listener);
    smt.smtConfig.solvername = solvername;
    smt.smtConfig.logfile = "solver.out";
    smt.smtConfig.smtlib = version; // FIXME - is this needed?
    ISolver s = smt.startSolver(smt.smtConfig, solvername, null);
    if (s == null) throw new RuntimeException("Failed to create or start solver");
    solver = s;
  }

  /** Checks response against result, issuing a JUnit Assert if they do not match appropriately */
  public void checkResponse(IResponse res, /*@Nullable*/ String result) {
    if (res == null) {
      Assert.assertTrue("Response is null", false);
    } else if (result == null) {
      if (res.isError()) Assert.assertTrue(((IResponse.IError) res).errorMsg(), false);
    } else if (result.isEmpty() && res.isOK()) {
      ISource source = smt.smtConfig.smtFactory.createSource(":print-success", null);
      IParser p = smt.smtConfig.smtFactory.createParser(smt.smtConfig, source);
      try {
        IKeyword k = p.parseKeyword();
        IResponse r = solver.get_option(k);
        if (!r.toString().equals("false")) {
          Assert.assertEquals(result, smt.smtConfig.defaultPrinter.toString(res));
        }
      } catch (ParserException e) {
        Assert.assertTrue(e.toString(), false);
      }
    } else {
      Assert.assertEquals(result, smt.smtConfig.defaultPrinter.toString(res));
    }
  }

  /** Parses a command */
  public /*@Nullable*/ ICommand parseCommand(String input) {
    try {
      ISource source = smt.smtConfig.smtFactory.createSource(input, null);
      IParser p = new org.smtlib.sexpr.Parser(smt.smtConfig, source);
      return p.parseCommand();
    } catch (Exception e) {
      return null;
    }
  }

  /** Parses, executes and checks a command */
  public IResponse doCommand(String input) {
    ICommand command = parseCommand(input);
    if (command == null) throw new RuntimeException("Failed to create command");
    IResponse r;
    checkResponse(r = command.execute(solver), null);
    return r;
  }

  /** Parses, executes and checks a command against given result. */
  public IResponse doCommand(String input, String result) {
    ICommand command = parseCommand(input);
    if (command == null) throw new RuntimeException("Failed to create command");
    IResponse r;
    checkResponse(r = command.execute(solver), result);

    return r;
  }

  /** Executes a script, capturing all the output and returning it. */
  public String doScript(String input) {
    ByteArrayOutputStream ba = new ByteArrayOutputStream();
    PrintStream savedOut = System.out;
    System.setOut(new PrintStream(ba));
    try {
      SMT smt = new SMT();
      smt.props = readPropertiesAndAddDefaults(smt);
      smt.smtConfig.text = input;
      smt.smtConfig.log.out = new PrintStream(ba);
      smt.smtConfig.log.diag = smt.smtConfig.log.out;
      smt.smtConfig.solvername = solvername;
      smt.exec();
      return ba.toString();
      //			IKeyword psKeyword = smt.smtConfig.exprFactory.keyword(Utils.PRINT_SUCCESS,null);
      //			ISource source = smt.smtConfig.smtFactory.createSource(input,null);
      //			IParser p = new org.smtlib.sexpr.Parser(smt.smtConfig,source);
      //			ICommand cmd;
      //			while (!p.isEOD()) {
      //				cmd = p.parseCommand();
      //				if (cmd != null) {
      //					IResponse res = cmd.execute(solver);
      //					IPos pos = res.isError() ? ((IResponse.IError)res).pos() : null;
      //					if (pos != null && pos.source() != null) {
      //						sb.append(Log.locationIndication(pos,smt.smtConfig.prompt,smt.smtConfig));
      //						sb.append("\n");
      //					}
      //					if (!res.isOK() || solver.get_option(psKeyword).toString().equals("true")) {
      //						sb.append(smt.smtConfig.defaultPrinter.toString(res));
      //						sb.append("\n");
      //					}
      //				} else {
      //					IPos pos = listener.msg.isError() ? ((IResponse.IError)listener.msg).pos() : null;
      //					if (pos != null && pos.source() != null) {
      //						sb.append(Log.locationIndication(pos,smt.smtConfig.prompt,smt.smtConfig));
      //						sb.append("\n");
      //					}
      //
      //					sb.append(smt.smtConfig.defaultPrinter.toString(listener.msg));
      //					sb.append("\n");
      //				}
      //			}
      //			return sb.toString();
    } catch (Exception e) {
      return e.toString();
    } finally {
      System.setOut(savedOut);
    }
  }
}
