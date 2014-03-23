package org.smtlib;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import tests.ParameterizedIgnorable;

@RunWith(ParameterizedIgnorable.class)
public class Logics extends LogicsBase {

    public Logics(String logicname) {
    	this.logicname = logicname;
    }

	@Test
	public void testLogic() {
		doCommand("(set-logic " + logicname + ")",
				logicname.equals("ZZZ") ? "No logic file found for ZZZ" : "success");
	}
}
