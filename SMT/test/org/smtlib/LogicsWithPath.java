package org.smtlib;

import java.io.File;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;


@RunWith(Parameterized.class)
public class LogicsWithPath extends LogicsBase {

	public void init() {
		super.init();
		smt.smtConfig.logicPath = "logics";
	}

    public LogicsWithPath(String logicname) {
    	this.logicname = logicname;
    }

	@Test
	public void testLogic() {
		doCommand("(set-logic " + logicname + ")",
				logicname.equals("ZZZ") ? "No logic file found for ZZZ on path \"logics\"" : "success");
	}
}
