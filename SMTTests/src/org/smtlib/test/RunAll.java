package org.smtlib.test;

import java.io.File;
import java.io.FileWriter;
import java.io.Writer;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;

import org.junit.internal.TextListener;
import org.junit.runner.JUnitCore;
import org.junit.runner.Result;

/** Drop-in replacement for `java org.junit.runner.JUnitCore <classes>` that additionally
 *  attaches a {@link LoggingRunListener} so failures (and progress) are visible in a log
 *  file as they happen, not just in the final summary -- the stock JUnitCore CLI entry
 *  point has no flag to attach a custom listener, so it has to be done programmatically.
 *
 *  Usage: java org.smtlib.test.RunAll <logdir> <class1> [class2 ...]
 *  The log file is timestamped (like time-solvers-logs/) so a second, concurrently
 *  started run doesn't collide with or overwrite the first one's log.
 */
public class RunAll {
    public static void main(String[] args) throws Exception {
        if (args.length < 1) {
            System.err.println("Usage: RunAll <logdir> <class1> [class2 ...]");
            System.exit(2);
        }
        String logDir = args[0];
        new File(logDir).mkdirs();
        String ts = new SimpleDateFormat("yyyyMMdd-HHmmss").format(new Date());
        File logFile = new File(logDir, "junit-" + ts + ".log");
        System.out.println("JUnit progress/failure log: " + logFile.getPath());

        List<Class<?>> classes = new ArrayList<Class<?>>();
        for (int i = 1; i < args.length; i++) {
            classes.add(Class.forName(args[i]));
        }

        try (Writer w = new FileWriter(logFile)) {
            JUnitCore core = new JUnitCore();
            core.addListener(new LoggingRunListener(w));
            core.addListener(new TextListener(System.out)); // keep the familiar dots + final summary
            Result result = core.run(classes.toArray(new Class<?>[0]));
            System.exit(result.wasSuccessful() ? 0 : 1);
        }
    }
}
