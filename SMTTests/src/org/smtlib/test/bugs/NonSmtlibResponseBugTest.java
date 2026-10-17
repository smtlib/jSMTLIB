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
}
