package org.smtlib.test.bugs;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.PrintStream;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.IResponse;
import org.smtlib.SMT;

/** Regression test for #118: solver text that is not SMT-LIB and begins with an invalid token
 *  (e.g. bitwuzla's "[error] ...") was parsed into a response that is an error but not an
 *  IResponse.IError, and the command-line tool then failed with a ClassCastException. */
public class NonSmtlibResponseBugTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    private static final String TEXT = "[error] <stdin>:2:9: expected Bool term";

    @Test
    public void parsedAsAnError() throws Exception {
        SMT smt = new SMT();
        smt.smtConfig.log.setChannels(new PrintStream(new ByteArrayOutputStream()), new PrintStream(new ByteArrayOutputStream()));
        IResponse r = new org.smtlib.sexpr.Parser(smt.smtConfig, new org.smtlib.impl.Pos.Source(TEXT, null)).parseResponse(TEXT);
        Assert.assertTrue(String.valueOf(r), r instanceof IResponse.IError);
        Assert.assertTrue(((IResponse.IError)r).errorMsg(), ((IResponse.IError)r).errorMsg().contains(TEXT));
    }

    /** Through the command-line tool, with a solver (NonSmtlibErrorProcess) that answers the
     *  assert with that text */
    @Test
    public void reportedAsAnError() {
        String javaBin = System.getProperty("java.home") + File.separator + "bin" + File.separator + "java";
        SMT smt = new SMT();
        smt.smtConfig.props = smt.smtConfig.readProperties();
        smt.smtConfig.props.setProperty("org.smtlib.solver_nonsmtlib.command",
                javaBin + ",-cp," + System.getProperty("java.class.path") + ",org.smtlib.test.NonSmtlibErrorProcess");
        ByteArrayOutputStream outBuf = new ByteArrayOutputStream();
        PrintStream out = new PrintStream(outBuf);
        smt.smtConfig.log.setChannels(out, out);
        smt.smtConfig.stdout = out;
        smt.smtConfig.stderr = out;
        int exitCode = smt.exec(new String[]{"--solver", "nonsmtlib", "--text",
                "(set-logic QF_UF)\n(assert true)\n(check-sat)\n"});
        smt.cleanup();
        out.flush();
        String output = outBuf.toString().replace("\r\n", "\n");
        Assert.assertTrue(output, output.contains("(error \"Unexpected response from the solver: " + TEXT + "\")"));
        Assert.assertTrue(output, output.endsWith("sat\n"));
        Assert.assertEquals(output, 1, exitCode);
    }
}
