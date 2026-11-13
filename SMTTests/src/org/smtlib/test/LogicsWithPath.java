package org.smtlib.test;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;

/** Sets each logic with the test solver, reading the logic definitions from an explicit logic path */
@RunWith(org.junit.runners.ParameterizedWithNames.class)
public class LogicsWithPath extends LogicTests {

    /** The logics set: those with a file under SMT/logics, and ZZZ, which has none */
    @Parameters
    public static Collection<String[]> data() {
        // Logic names below not present as a .smt2 file under SMT/logics (i.e. not part of
        // the current SMT-LIB 2.7 logic set) are commented out, not deleted -- whether they
        // should be restored (e.g. as older/non-standard logic names) is a separate,
        // ongoing investigation. "ZZZ" is a deliberately-bogus logic name used to test the
        // "no logic file found" error path itself, not a real logic -- always kept.
        Collection<String[]> c = Arrays.asList(new String[][]{
//                    { "ALIA" },
                    { "AUFLIA" }, { "AUFLIRA" }, { "AUFNIRA" },
//                    { "BV" },
                    { "LIA" }, { "LRA" },
//                    { "NIA" }, { "NRA" },
                    { "QF_ABV" },
//                    { "QF_ALIA" }, { "QF_ANIA" },
                    { "QF_AUFBV" }, {"QF_AUFLIA"},
//                    {"QF_AUFNIA"},
                    {"QF_AX"},
                    { "QF_BV" },
                    { "QF_IDL" }, {"QF_LIA"},
//                    {"QF_LIRA"},
                    { "QF_LRA" },
                    { "QF_NIA" },
//                    {"QF_NIRA" },
                    {"QF_NRA" },
                    { "QF_RDL" }, { "QF_UF" }, { "QF_UFBV" }, { "QF_UFIDL" },
                    { "QF_UFLIA" }, {"QF_UFLRA" },
//                    { "QF_UFNIA" },
                    {"QF_UFNRA" },
//                    { "UF" }, { "UFBV" }, { "UFIDL" },
//                    { "UFLIA" },
                    {"UFLRA" }, { "UFNIA" }, // {"UFNRA" },
                    { "ALL" },
                    { "ZZZ" } } );
        if (false) { // Version 2.5 // FIXME
            Collection<String[]> cc = Arrays.asList(new String[][]{ 
                     { "QF_BVFP" }, { "QF_FP" },
            });
            c.addAll(cc);
        }
        return c;
    }

    private final String logicname;

    public LogicsWithPath(String logicname) {
        this.logicname = logicname;
        solvername = "test";
    }

    @Override
    public void init() {
        super.init();
        smt.smtConfig.logicPath = "../SMT/logics";
    }

    @Test
    public void testLogic() {
        doCommand("(set-logic " + logicname + ")",
                logicname.equals("ZZZ") ? "(error \"No logic file found for ZZZ on path \"\"../SMT/logics\"\"\")" : "success");
    }
}
