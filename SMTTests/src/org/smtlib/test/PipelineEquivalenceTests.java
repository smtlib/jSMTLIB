package org.smtlib.test;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.PrintStream;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Assume;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.junit.runners.ParameterizedWithNames;
import org.smtlib.SMT;

/** Runs each test in tests/pipeline with and without --pipeline, for each solver in
 *  SMT_TEST_SOLVERS that pipelines, and requires the same output and exit code. Unlike the
 *  goldens, this needs no expected output, so it also checks solvers whose goldens for these
 *  tests are skipped (e.g. bitwuzla, which supports no integer logic). */
@RunWith(ParameterizedWithNames.class)
public class PipelineEquivalenceTests {

    @Rule public Timeout timeout = new Timeout(2, TimeUnit.MINUTES);

    private final String solvername;
    private final File tstFile;

    public PipelineEquivalenceTests(String solvername, String tstFilePath) {
        this.solvername = solvername;
        this.tstFile = new File(tstFilePath);
    }

    @Parameters
    public static Collection<String[]> data() {
        File dir = new File("tests/pipeline");
        if (!dir.isDirectory()) dir = new File("SMTTests/tests/pipeline");
        File[] files = dir.listFiles((d, name) -> name.endsWith(".tst"));
        List<String[]> list = new ArrayList<>();
        if (files == null) return list;
        Arrays.sort(files);
        for (File f : files) {
            for (String s : LogicTests.solvers) list.add(new String[]{s, f.getPath()});
        }
        return list;
    }

    /** Output (regular, then diagnostic) and exit code of running the text with the given options */
    private String run(String text, List<String> options) {
        SMT smt = new SMT();
        smt.smtConfig.props = smt.smtConfig.readProperties();
        smt.smtConfig.testing = true;
        ByteArrayOutputStream outBuf = new ByteArrayOutputStream();
        ByteArrayOutputStream errBuf = new ByteArrayOutputStream();
        PrintStream out = new PrintStream(outBuf);
        PrintStream err = new PrintStream(errBuf);
        smt.smtConfig.log.setChannels(out, err);
        smt.smtConfig.stdout = out;
        smt.smtConfig.stderr = err;
        List<String> args = new ArrayList<>(List.of("--solver", solvername));
        args.addAll(options);
        args.addAll(List.of("--text", text));
        int rc = smt.exec(args.toArray(new String[0]));
        smt.cleanup();
        out.flush();
        err.flush();
        return (outBuf + "--- diagnostic output ---\n" + errBuf + "--- exit code " + rc + "\n").replace("\r\n", "\n");
    }

    @Test
    public void sameOutputWithPipelining() throws Exception {
        // Solvers not run as a process, and z3-4.3, whose adapter does not pipeline
        Assume.assumeFalse(solvername.equals("test") || solvername.equals("simplify")
                || solvername.startsWith("z3-4.3") || solvername.startsWith("z3_4_3"));
        String text = new String(Files.readAllBytes(tstFile.toPath()));
        List<String> options = new ArrayList<>();
        if (text.startsWith("; OPTIONS:")) {
            int eol = text.indexOf('\n');
            for (String o : text.substring("; OPTIONS:".length(), eol < 0 ? text.length() : eol).trim().split("\\s+")) {
                if (!o.isEmpty() && !o.equals("--pipeline")) options.add(o);
            }
        }
        String unpipelined = run(text, options);
        options.add("--pipeline");
        Assert.assertEquals(tstFile.getName() + " with --pipeline", unpipelined, run(text, options));
    }
}
