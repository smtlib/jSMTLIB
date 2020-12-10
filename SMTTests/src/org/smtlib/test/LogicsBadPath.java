package org.smtlib.test;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.ParameterizedWithNames;
import org.smtlib.SMT;
import org.smtlib.SMT.Configuration.SMTLIB;

@RunWith(ParameterizedWithNames.class)
public class LogicsBadPath extends LogicTests {

  public LogicsBadPath(String solver, String version) {
    solvername = solver;
    this.version = version;
  }

  @Override
  public void init() {
    super.init();
    smt.smtConfig.logicPath = "xxx";
    SMT.Configuration.smtlib = version;
  }

  @Test
  public void testLogic() {
    doCommand(
        "(set-logic QF_UF)",
        solvername.startsWith("z3")
                || solvername.startsWith("cvc4")
                || solvername.startsWith("yices2")
                || solvername.startsWith("test")
            ? "success"
            : // FIXME
            smt.smtConfig.isVersion(SMTLIB.V20)
                ? "(error \"No logic file found for QF_UF on path \\\"xxx\\\"\")"
                : "(error \"No logic file found for QF_UF on path \"\"xxx\"\"\")");
  }
}
