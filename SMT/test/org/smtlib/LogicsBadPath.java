package org.smtlib;

import org.junit.Test;

// FIXME - which solver is this using?

public class LogicsBadPath extends LogicsBase {

	@Override
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
