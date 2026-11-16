package org.smtlib.test;

import java.io.File;
import java.io.OutputStream;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.smtlib.IPos;
import org.smtlib.IResponse;
import org.smtlib.Log;
import org.smtlib.SMT;

/** Each warning reaches Log listeners with the position of the text it concerns (#220). JUnit because the
 *  positions are seen only through the listener API; the command-line display is covered by goldens. */
public class PositionedWarningsTests {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    /** Records each warning as "message @ text at its position" ("@ -" without a position) */
    static class Recorder implements Log.IListener {
        final List<String> warnings = new ArrayList<>();
        final List<String> diags = new ArrayList<>();
        @Override public void logOut(String msg) {}
        @Override public void logOutNoln(String msg) {}
        @Override public void logOut(IResponse result) {}
        @Override public void logError(String msg) {}
        @Override public void logError(IResponse.IError result) {}
        @Override public void logDiag(String msg) { diags.add(msg); }
        @Override public void indent(String chars) {}
        @Override public void logWarning(String msg, IPos pos) {
            String text = pos == null || pos.source() == null ? "-"
                    : pos.source().chars().subSequence(pos.charStart(), pos.charEnd()).toString();
            warnings.add(msg + " @ " + text);
        }
    }

    /** Runs the arguments with the test solver, returning the recorder */
    private static Recorder run(String... args) {
        SMT smt = new SMT();
        try {
            PrintStream sink = new PrintStream(OutputStream.nullOutputStream());
            smt.smtConfig.stdout = sink;
            smt.smtConfig.stderr = sink;
            smt.smtConfig.log.setChannels(sink, sink);
            Recorder recorder = new Recorder();
            smt.smtConfig.log.addListener(recorder);
            String[] all = new String[args.length + 2];
            all[0] = "--solver";
            all[1] = "test";
            System.arraycopy(args, 0, all, 2, args.length);
            smt.exec(all);
            return recorder;
        } finally {
            smt.cleanup();
        }
    }

    @Test public void nonstandardSetInfo() {
        Recorder r = run("--text", "(set-info :foo 1)");
        Assert.assertEquals(List.of(":foo is not a standard set-info attribute @ :foo"), r.warnings);
        Assert.assertEquals(List.of(), r.diags);
    }

    @Test public void unknownVersion() {
        Recorder r = run("--text", "(set-info :smt-lib-version 2.8)");
        Assert.assertEquals(List.of("SMT-LIB version 2.8 is not one jSMTLIB knows; using V2.7 @ 2.8"), r.warnings);
    }

    @Test public void namedLetBound() {
        Recorder r = run("--relax", "--text", "(set-logic ALL)(assert (let ((y true)) (! (and y y) :named b)))");
        Assert.assertEquals(List.of("The expression being named is not closed - this symbol is a let-bound variable: y @ y"),
                r.warnings);
    }

    /** The QF_RDL logic checks terms through a cloned configuration (#221) */
    @Test public void qfRdlDecimal() {
        Recorder r = run("--relax", "--text",
                "(set-logic QF_RDL)(declare-fun x () Real)(assert (< (- x x) 1.5))(assert (< (- x x) (- 0.5)))");
        Assert.assertEquals(List.of(
                "A QF_RDL constant should be a numeral or a negated numeral, not a decimal: (< (- x x) 1.5) @ 1.5",
                "A QF_RDL constant should be a numeral or a negated numeral, not a decimal: (< (- x x) (- 0.5)) @ (- 0.5)"),
                r.warnings);
    }

    @Test public void parenthesizedNullaryPattern() {
        Recorder r = run("--relax", "--text", "(set-logic ALL)(declare-datatype L ((nil) (cons (hd Int) (tl L))))"
                + "(declare-const l L)(assert (match l (((nil) true) ((cons h t) false))))");
        Assert.assertEquals(List.of("A parenthesized pattern should have at least one variable: (nil) @ (nil)"),
                r.warnings);
    }

    @Test public void sortAttributeInTheory() throws Exception {
        File dir = Files.createTempDirectory("smttheory").toFile();
        File theory = new File(dir, "T.smt2");
        File logic = new File(dir, "L.smt2");
        try {
            try (PrintWriter pw = new PrintWriter(theory)) {
                pw.println("(theory T :smt-lib-version 2.7 :sorts ((P 2 :left-assoc)) :definition \"test\")");
            }
            try (PrintWriter pw = new PrintWriter(logic)) {
                pw.println("(logic L :smt-lib-version 2.7 :theories (Core T) :language \"test\")");
            }
            Recorder r = run("-L", dir.getAbsolutePath(), "--text", "(set-logic L)");
            Assert.assertEquals(List.of("The :left-assoc attribute has no meaning on a sort declaration and is ignored"
                    + " (sort P, in theory T) @ :left-assoc"), r.warnings);
        } finally {
            theory.delete();
            logic.delete();
            dir.delete();
        }
    }

    /** A warning about the command line itself has no position */
    @Test public void pipelineIgnored() {
        java.io.InputStream stdin = System.in;
        Recorder r;
        try {
            System.setIn(new java.io.ByteArrayInputStream("(exit)\n".getBytes()));
            r = run("--pipeline");
        } finally {
            System.setIn(stdin);
        }
        Assert.assertEquals(1, r.warnings.size());
        Assert.assertTrue(r.warnings.get(0), r.warnings.get(0).startsWith("--pipeline applies only to files"));
        Assert.assertTrue(r.warnings.get(0), r.warnings.get(0).endsWith(" @ -"));
    }

    /** A listener that does not implement logWarning receives it as a WARNING diagnostic */
    @Test public void defaultLogWarningLogsADiagnostic() {
        List<String> diags = new ArrayList<>();
        Log.IListener listener = new Log.IListener() {
            @Override public void logOut(String msg) {}
            @Override public void logOutNoln(String msg) {}
            @Override public void logOut(IResponse result) {}
            @Override public void logError(String msg) {}
            @Override public void logError(IResponse.IError result) {}
            @Override public void logDiag(String msg) { diags.add(msg); }
            @Override public void indent(String chars) {}
        };
        listener.logWarning("something", null);
        Assert.assertEquals(List.of("WARNING: something"), diags);
    }
}
