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

        // Heartbeat disabled: it did its job diagnosing the Linux hang (now fixed, see
        // Solver_z3_recent.java) but fires on essentially every run regardless of health --
        // a full suite routinely runs past the 60s interval on its own, so the dump was
        // never actually a hang signal, just noise on every green run. Left in place
        // (commented, not deleted) in case a future hang investigation wants it back.
        // Thread mainThread = Thread.currentThread();
        // Thread heartbeat = startHeartbeat(mainThread);

        try (Writer w = new FileWriter(logFile)) {
            JUnitCore core = new JUnitCore();
            core.addListener(new LoggingRunListener(w));
            core.addListener(new TextListener(System.out)); // keep the familiar dots + final summary
            Result result = core.run(classes.toArray(new Class<?>[0]));
            // heartbeat.interrupt();
            System.exit(result.wasSuccessful() ? 0 : 1);
        }
    }

    /** Dumps the main thread's stack trace to stdout every 60s until interrupted. A CI hang
     *  (two 6-hour job timeouts so far, cause unknown -- see runs 32097690084, 32208754026)
     *  produced literally zero output between "Running unit tests..." and cancellation: not
     *  one TextListener dot, meaning the JVM never even finished a single test. That leaves
     *  no way to tell "stuck in a @Parameters method during test discovery" from "stuck
     *  inside the very first test" from logs alone. This gives that answer directly, and
     *  for free even on a normal run: printing to stdout (not the JUnit log file) means it
     *  shows up in the CI step's own log regardless of which phase the hang is in, and a
     *  daemon thread with no shared state keeps reporting even if the main thread is
     *  wedged on blocking I/O (e.g. a solver subprocess) that a JUnit @Rule Timeout's
     *  watcher-thread approach can abandon but not actually interrupt. */
    private static Thread startHeartbeat(Thread mainThread) {
        Thread heartbeat = new Thread(() -> {
            while (true) {
                try {
                    Thread.sleep(60_000);
                } catch (InterruptedException e) {
                    return;
                }
                System.out.println("[heartbeat] main thread stack trace:");
                for (StackTraceElement el : mainThread.getStackTrace()) {
                    System.out.println("    at " + el);
                }
            }
        });
        heartbeat.setDaemon(true);
        heartbeat.setName("heartbeat");
        heartbeat.start();
        return heartbeat;
    }
}
