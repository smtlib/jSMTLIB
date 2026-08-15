package org.smtlib.test;

import java.io.PrintWriter;
import java.io.Writer;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import org.junit.runner.Description;
import org.junit.runner.notification.Failure;
import org.junit.runner.notification.RunListener;

/** JUnit RunListener that logs progress and failures to a file as they happen, so the
 *  log can be tailed live. The stock JUnitCore CLI only accumulates failures internally
 *  and prints them in a summary at the very end of the run, which is not useful for
 *  watching a long multi-solver run in progress. */
public class LoggingRunListener extends RunListener {

    private final PrintWriter out;
    private final Set<String> failed = Collections.synchronizedSet(new HashSet<String>());

    public LoggingRunListener(Writer w) {
        this.out = new PrintWriter(w, true); // autoFlush on println
    }

    @Override
    public void testStarted(Description description) {
        out.println("RUNNING " + description.getDisplayName());
    }

    @Override
    public void testFailure(Failure failure) {
        failed.add(failure.getDescription().getDisplayName());
        out.println("FAIL " + failure.getDescription().getDisplayName() + ": " + failure.getMessage());
    }

    /** Fires for Assume.assumeTrue(false) -- how FileTests.checkSkip() implements a skip. */
    @Override
    public void testAssumptionFailure(Failure failure) {
        out.println("SKIP " + failure.getDescription().getDisplayName() + ": " + failure.getMessage());
    }

    @Override
    public void testIgnored(Description description) {
        out.println("IGNORED " + description.getDisplayName());
    }

    @Override
    public void testFinished(Description description) {
        if (!failed.contains(description.getDisplayName())) {
            out.println("PASS " + description.getDisplayName());
        }
    }
}
