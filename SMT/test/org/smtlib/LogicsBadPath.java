package org.smtlib;

import java.io.File;

import org.junit.Test;


public class LogicsBadPath extends LogicsBase {

	public void init() {
		super.init();
		smt.smtConfig.logicPath = "xxx";
	}

    public LogicsBadPath() {
    }

	@Test
	public void testLogic() {
		doCommand("(set-logic QF_UF)","No logic file found for QF_UF on path \"xxx\"");
	}
}
