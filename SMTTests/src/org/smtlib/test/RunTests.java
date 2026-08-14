package org.smtlib.test;


import java.io.File;
import java.util.concurrent.TimeUnit;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;

public class RunTests {

	@Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

	@Before
	public void setUp() throws Exception {
	}

	@After
	public void tearDown() throws Exception {
	}
	
	//  Note - the script compiles jSMTLIB.jar
	// FIXME: Need to compare against oracle output
	@Test
	public void apiExample() {
		try {
			ProcessBuilder pb = new ProcessBuilder("bash", "api.sh");
			pb.directory(new File("tests"));
			Process p = pb.start();
		} catch (java.io.IOException e) {
			Assert.fail(e.getMessage());
		}
	}

}
