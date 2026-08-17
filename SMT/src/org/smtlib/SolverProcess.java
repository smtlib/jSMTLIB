/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

import java.io.BufferedReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.nio.charset.Charset;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.TimeUnit;
import java.util.function.Function;

/** This class implements launching, writing to, and reading responses from a
 * launched process (in particular, solver processes).
 * @author David Cok
 */
public class SolverProcess {

    /** How long (ms) to wait for error-stream text to arrive before concluding a command
     * produced none, and (once some has arrived) how much longer to wait for further
     * stragglers before returning it. There is no OS-level signal tying completeness of
     * stderr to the recognized end marker on stdout, so this is a bounded best-effort wait,
     * not a guarantee; see StreamGobbler.drain() for why even the first check needs this,
     * not just the straggler wait -- it is paid on every command, including ones with no
     * error to find, not only when error text is actually flowing. */
    public long errorSettleMillis = 20;

    /** Set true by a caller for the duration of a single command whose expected response
     * text may contain literal, non-SMT-LIB unbalanced parentheses (e.g. some z3
     * :reason-unknown text), so the end-marker recognizer does not wait forever for
     * parentheses to balance. */
    public boolean badFormat = false;

	final static protected String eol = System.getProperty("line.separator");

	protected StreamGobbler standardOut;
	protected StreamGobbler errorOut;

	/** Wraps an exception thrown because of a failure in the prover */
	public static class ProverException extends RuntimeException {
		private static final long serialVersionUID = 1L;

		public ProverException(String s) { super(s); }
	}

	/** The command-line arguments that launch a new process */
	protected String[] app;

	/** The charset used to encode text sent to the process and decode text read back from it */
	protected Charset charset;

	/** The text that marks the end of the text returned from the process */
	protected String endMarker;

	/** The Java process object (initialized by start() )*/
	protected Process process;

	/** The Writer object that writes to the spawned process (initialized by start() )*/
	protected Writer toProcess;

	/** A place (e.g., log file), if non-null, to write all outbound communications for diagnostic purposes */
	public /*@Nullable*/Writer log;


	/** Constructs a SolverProcess object, without actually starting the process as yet.
	 * @param cmd the command-line that will launch the desired process
	 * @param endMarker text that marks the end of text returned from the process, e.g. the end of the
	 * prompt for new input
	 * @param logfile if not null, the name of a file to log communications to, for diagnostic purposes
	 */
	public SolverProcess(String[] cmd, String endMarker, /*@Nullable*/String logfile) {
		this(cmd, endMarker, logfile, Charset.defaultCharset());
	}

	/** As {@link #SolverProcess(String[], String, String)}, but explicitly setting the charset
	 * used to encode text sent to the process and decode text read back from it.
	 * @param charset the charset to use for the process's stdin/stdout/stderr
	 */
	public SolverProcess(String[] cmd, String endMarker, /*@Nullable*/String logfile, Charset charset) {
		this.endMarker = endMarker;
		this.charset = charset;
		try {
			if (logfile != null) {
				log = new FileWriter(logfile);
			} else {
//			    log = pw == null ? (pw = new java.io.PrintWriter(System.out)) : pw;
			}
		} catch (IOException e) {
			System.err.println("Failed to create solver log file " + logfile + ": " + e);
		}
		setCmd(cmd);
	}

	/** The charset being used to encode text sent to the process and decode text read back from it */
	public Charset getCharset() {
		return charset;
	}

	/** Enables changing the command-line; must be called prior to start() */
	public void setCmd(String[] cmd) {
		this.app = cmd;
		try {
			if (log != null && cmd != null) {
				// TODO: Might be nicer to escape any backslashes and enclose strings in quotes, in case arguments contain spaces or special characters
				log.write(";; ");
				for (String s: cmd) { log.write(s); log.write(" "); }
				log.write(eol);
			}
		} catch (IOException e) {
			System.err.println("Failed to write to solver log file : " + e);
		}
	}

	protected Thread shutdownThread = null;

	/** Starts the process; if the argument is true, then also listens to its output until a prompt is read.
	 * @param listen true if the process prints banner/greeting text of its own before it is ready to
	 * read commands (e.g. a version line, a copyright notice) that must be read and discarded before the
	 * first real command is sent, lest it be mistaken for that command's response; listen() blocks until
	 * the end marker is recognized, however long the banner actually takes to arrive, so this does not
	 * need -- and must not be replaced by -- a fixed delay. Pass false when the process prints nothing
	 * until it has consumed its first command (true of every solver currently adapted here; each launches
	 * with a quiet/non-interactive flag specifically to suppress any such banner at the source).
	 * @throws ProverException if this SolverProcess has already been started (each instance is single-use;
	 * solver adapters construct a fresh SolverProcess per start() rather than reusing one) */
    public void start(boolean listen) throws ProverException {
    	if (process != null) throw new ProverException("SolverProcess.start() called on an already-started process");
    	try {
            process = Runtime.getRuntime().exec(app);
    		// Captured into a local rather than reading the 'process' field from within run():
    		// exit() nulls that field before this process has necessarily finished dying, and if
    		// the hook fires (JVM shutdown racing ahead of the async removal below) after that
    		// field is null, reading it from the field would NPE instead of harmlessly re-killing
    		// an already-dying process.
    		final Process p = process;
    		shutdownThread = new Thread() { public void run() { p.destroyForcibly(); }};
    		Runtime.getRuntime().addShutdownHook( shutdownThread );
    		// Removing the hook only when we ourselves call exit() would leave it (and the
    		// SolverProcess it closes over, per the comment on unregisterShutdownHook()) pinned
    		// in memory for the rest of the JVM's life if the process instead dies on its own
    		// (crash, killed externally, etc.), since nothing else calls exit() in that case.
    		// onExit() completes on process termination for any reason, so this is the one place
    		// that reliably detects "the process is gone" regardless of why.
    		process.onExit().thenRun(this::unregisterShutdownHook);
    		toProcess = new OutputStreamWriter(process.getOutputStream(), charset);
            errorOut = new StreamGobbler(process.getErrorStream(), null, charset);
            standardOut = new StreamGobbler(process.getInputStream(), s->endsWith(s,endMarker), charset);
            errorOut.log = log;
            standardOut.log = log;
            errorOut.setName("stderr-gobbler");
            standardOut.setName("stdout-gobbler");
            errorOut.start();
            standardOut.start();
    		if (listen) listen();
    	} catch (IOException e) {
    		// Java 21.0.3+ changed the IOException message format for exec failures from
    		// "error=N, description" to "Exec failed, error: N (description) ".
    		// Normalize to the older form so test output is stable across JVM versions.
    		String msg = e.getMessage().replaceAll("Exec failed, error: (\\d+) \\((.+?)\\)\\s*$", "error=$1, $2");
    		throw new ProverException(msg);
    	} catch (RuntimeException e) {
    		throw new ProverException(e.getMessage());
    	}
    }

    boolean endsWith(StringBuilder sb, String endMarker) {
        int sblen = sb.length();
        int len = endMarker.length();
        int i = len;
        while (i > 0 && endMarker.charAt(len-i) == sb.charAt(sblen-i)) --i;
        if (i != 0) return false;
        // In some cases, the endMarker is just an eol, but the ojutput can be a long
        // S-expression broken up with eols. SO we must recognize an end of input only
        // if the parentheses are balanced.
        i = sb.indexOf("(");
        if (i < 0) return true;
        int count = 1;
        // Tracks whether the scan is currently inside a double-quoted string literal, so
        // that a stray '(' or ')' in a solver's own error-message prose (e.g. z3's
        // "Expecting sort list '(': ...") doesn't permanently unbalance the paren count and
        // make this recognizer wait forever. A doubled "" (SMT-LIB's escaped-quote form)
        // toggles twice with nothing in between, so this naive per-character toggle still
        // ends up in the right state without needing full escape-aware parsing. Scanning
        // from the start of the buffer (not just from i) keeps the in-string state correct
        // even if a quote appears before the first '('.
        boolean inString = false;
        for (int j = 0; j < i; ++j) {
            if (sb.charAt(j) == '"') inString = !inString;
        }
        i++;
        for (; i < sblen; ++i) {
            char c = sb.charAt(i);
            if (c == '"') {
                inString = !inString;
            } else if (!inString) {
                if (c == '(') count++;
                else if (c == ')') count--;
            }
        }
        // badFormat lets a caller (e.g. get_info on :reason-unknown) declare in advance that
        // the upcoming response text may contain literal unbalanced parentheses, so we do not
        // wait forever for a balance that will never come.
        return badFormat || count == 0;
    }

    /** Listens to the process's standard output until the designated endMarker is read,
     * combined with whatever error output has arrived. If there is error output, it is
     * returned; otherwise the standard output is returned.
     */
	public String listen() throws IOException {
		String out = standardOut.take(); // blocks until the end marker is recognized, or the process dies
		// errorOut has no end marker of its own -- there is no OS-level guarantee that error
		// text for this command has already been fully written and read by the time
		// standardOut's end marker shows up, so this is a bounded best-effort drain of
		// whatever has arrived, not a proof of completeness.
		String err = errorOut.drain(errorSettleMillis);
	    if (log != null) {
	        if (!out.isEmpty()) { log.write(";OUT: "); log.write(out); log.write(eol); log.flush(); } // input usually ends with a prompt and no line terminator
	        if (!err.isEmpty()) { log.write(";ERR: "); log.write(err); } // input usually ends with a line terminator, we think
	    }
        // In some cases (yices2) the prompt is on the error stream. Our heuristic is that then there is no line-termination
        if (err.endsWith("\n") || out.isEmpty()) {
            return err.isEmpty() || err.charAt(0) == ';' ? out : err; // Note: the guard against comments (starting with ;) is for Z3
        } else {
            if (out.endsWith(endMarker)) out = out.substring(0,out.length()-endMarker.length());
            return out;
        }
	}

	/** Returns true if the process is still running; this relies on exceptions
	 * for control flow and may be a bit expensive.
	 */
	public boolean isRunning(boolean expectStopped) {
		if (process == null) return false;
		try {
			process.exitValue();
			if (!expectStopped) {
				if (log != null) {
					try {
						log.write("Solver has unexpectedly terminated"); log.write(eol); log.flush();
					} catch (IOException e) {
						// ignore
					}
				}
			}
			return false;
		} catch (IllegalThreadStateException e) {
			return true;
		}
	}

	/** Removes the shutdown hook registered in start(), if it is still registered -- called once
	 * the process has actually terminated (see the onExit() registration in start()), whether
	 * that is because of our own destroyForcibly() call below or the process dying on its own.
	 * This is done rather than leaving the hook registered until the JVM actually exits so it
	 * doesn't keep this SolverProcess -- and the 'process' it closes over -- pinned in memory for
	 * the rest of the JVM's lifetime; the JVM's shutdown-hook registry holds a strong reference to
	 * every registered hook until it is explicitly removed. */
	private void unregisterShutdownHook() {
		if (shutdownThread != null) {
			Runtime.getRuntime().removeShutdownHook(shutdownThread);
			shutdownThread = null;
		}
	}

	/** Aborts the process; returns immediately if already stopped */
	public void exit() {
		if (process == null) return;
		process.destroyForcibly();
		process = null;
		toProcess = null;
		// destroyForcibly() closes the process's pipes, which drives each gobbler's read()
		// loop to EOF on its own; joining here just makes shutdown deterministic so repeated
		// start()/exit() cycles (e.g. across many tests) don't accumulate live threads.
		joinQuietly(standardOut);
		joinQuietly(errorOut);
		standardOut = null;
		errorOut = null;
		if (log != null) {
			try {
				log.write(";;Exiting solver");
				log.write(eol);
				log.flush();
				log.close();
			} catch (IOException e) {
				// Ignore
			}
		}
	}

	private static void joinQuietly(Thread t) {
		if (t == null) return;
		try {
			t.join(500);
		} catch (InterruptedException e) {
			Thread.currentThread().interrupt();
		}
	}

	/** Sends all the given text arguments, then (if listen is true) listens for the designated end marker text */
	public /*@Nullable*/ String send(boolean listen, String ... args) throws IOException {
		if (toProcess == null) throw new ProverException("The solver has not been started");
		// Check liveness *before* writing, rather than relying on the write/read to fail on
		// its own. Writes to an already-exited process's pipe are not reliably synchronous
		// with the process's death: the OS may buffer several KB before a write actually
		// fails, and a subsequent listen() can then race between the process being reported
		// dead and the stderr StreamGobbler thread finishing its last read -- observed as
		// intermittent, non-deterministic gaps in cascaded post-death error output (some
        // commands got a clean deterministic error, others silently got an empty response
        // that wasn't recognized as an error at all). Failing fast here, uniformly, once
        // death is known, removes that race for every command after the first.
		if (process != null && !process.isAlive()) {
			throw new IOException("Solver process has already exited");
		}
		for (String arg: args) {
			if (log != null) log.write(arg);
			toProcess.write(arg);
		}
		if (log != null) log.flush();
		toProcess.flush();
		if (listen) return listen();
		return null;
	}

	/** Sends all the given text arguments, then listens for the designated end marker text */
	public /*@Nullable*/ String sendAndListen(String ... args) throws IOException {
		return send(true,args);
	}

	/** Sends all the given text arguments, but does not wait for a response */
	public void sendNoListen(String ... args) throws IOException {
		send(false,args);
	}

// TODO - combine listen and noListen versions of send?

	/** Continuously drains one of the process's output streams (stdout or stderr) on a
	 *  dedicated thread, so that a solver writing a large amount of text to one stream
	 *  can never be blocked by the other stream's OS pipe buffer filling up while this
	 *  process is busy reading elsewhere -- reading stdout and stderr sequentially in a
	 *  single thread cannot make that guarantee.
	 *
	 *  Complete chunks of text are handed off to the consumer through a BlockingQueue,
	 *  which is what supplies the actual thread-safety here: only this thread ever touches
	 *  the in-progress StringBuilder, and only complete, immutable Strings cross to another
	 *  thread, via a queue implementation that already provides the necessary locking and
	 *  visibility guarantees. No manual synchronized/wait/notify is needed.
	 */
	public static class StreamGobbler extends Thread {

	    /** One handoff from the gobbler thread to a consumer: either a complete chunk of text
	     * (an end-marker match, or a raw read for streams with no end marker), a signal that
	     * the stream reached EOF (with any trailing unmatched text), or the IOException that
	     * ended the read loop. */
	    private static final class Chunk {
	        final String text;
	        final boolean eof;
	        final IOException error;
	        private Chunk(String text, boolean eof, IOException error) {
	            this.text = text; this.eof = eof; this.error = error;
	        }
	        static Chunk text(String s) { return new Chunk(s, false, null); }
	        static Chunk eof(String s) { return new Chunk(s, true, null); }
	        static Chunk error(IOException e) { return new Chunk("", true, e); }
	    }

	    /*@ non_null */ InputStream is;
	    /*@ nullable */ Function<StringBuilder,Boolean> endRecognizer;
	    /*@ non_null */ Charset charset;
	    /*@ nullable */ Writer log;

	    private final BlockingQueue<Chunk> queue = new LinkedBlockingQueue<Chunk>();

	    public StreamGobbler(/*@ non_null */InputStream is,
	                            /*@ nullable */ Function<StringBuilder,Boolean> endRecognizer,
	                            /*@ non_null */ Charset charset) {
	        this.is = is;
	        this.endRecognizer = endRecognizer;
	        this.charset = charset;
	        setDaemon(true);
	    }

	    public void run()
	    {
	        char[] buf = new char[10000];
	        StringBuilder local = new StringBuilder(); // thread-confined: only this thread ever touches it
	        try (
	            InputStreamReader isr = new InputStreamReader(is, charset);
	            BufferedReader br = new BufferedReader(isr); ){
	            int n;
	            while ((n = br.read(buf)) != -1) {
	                local.append(buf,0,n);
	                if (endRecognizer == null || endRecognizer.apply(local)) {
	                    offer(Chunk.text(local.toString()));
	                    local.setLength(0);
	                }
	            }
	            // end of stream reached -- fall through to report EOF with any trailing text
	        } catch (IOException ioe) {
	            offer(Chunk.error(ioe));
	            return;
	        }
	        offer(Chunk.eof(local.toString()));
	    }

	    private void offer(Chunk c) {
	        try {
	            queue.put(c);
	        } catch (InterruptedException e) {
	            Thread.currentThread().interrupt();
	        }
	    }

	    /** Blocks until a complete chunk is available: an end-marker match, or -- if the
	     * process dies first without ever producing one -- whatever trailing text (possibly
	     * empty) had already arrived. Never blocks forever: EOF always produces a chunk. */
	    String take() throws IOException {
	        try {
	            Chunk c = queue.take();
	            if (c.error != null) throw c.error;
	            return c.text;
	        } catch (InterruptedException e) {
	            Thread.currentThread().interrupt();
	            throw new IOException("Interrupted while waiting for solver output", e);
	        }
	    }

	    /** Drains whatever text has arrived, waiting up to settleMillis for the *first* chunk
	     * before concluding there is none, and (once at least one chunk has arrived) up to
	     * settleMillis again for further stragglers before giving up. Always returns -- never
	     * blocks indefinitely -- once the stream reaches EOF or a settle window elapses.
	     *
	     * The first wait matters as much as the straggler one: this thread only just unblocked
	     * from standardOut.take(), which guarantees the solver has finished writing this
	     * response's stdout, but says nothing about whether our own stderr-gobbler thread --
	     * scheduled completely independently -- has finished reading and queuing whatever
	     * error text the solver wrote alongside it. A non-blocking first check can catch that
	     * gobbler thread simply not having caught up yet, even though the solver did write
	     * error text for this command, and concludes "no error" -- observed as an entire
	     * command's error-and-echo block silently missing from a script's output, not merely
	     * truncated at a boundary, while later commands in the same run are unaffected. */
	    String drain(long settleMillis) throws IOException {
	        StringBuilder out = new StringBuilder();
	        try {
	            Chunk c = queue.poll(settleMillis, TimeUnit.MILLISECONDS); // brief grace period, first chunk
	            while (c != null) {
	                if (c.error != null) throw c.error;
	                out.append(c.text);
	                if (c.eof) break;
	                c = queue.poll(settleMillis, TimeUnit.MILLISECONDS); // brief grace period for stragglers
	            }
	        } catch (InterruptedException e) {
	            Thread.currentThread().interrupt();
	            throw new IOException("Interrupted while draining solver error output", e);
	        }
	        return out.toString();
	    }
	}

	public static void main(String ... args) {
        java.util.Scanner in = new java.util.Scanner(System.in);
	    SolverProcess sp = new SolverProcess(args, "\n", null);
	    sp.start(false);
	    while (true) {
            String s = in.nextLine();
            System.out.println("READ " + s);
            try {
                System.out.println("WRITING " + s);
                String out = sp.sendAndListen(s + "\n");
                System.out.println("HEARD: " + out);
            } catch (java.io.IOException e) {
                System.out.println("FAILED TO WRITE INPUT " + e);
            }
            try { Thread.sleep(100); } catch (Exception e) {}
	    }
	}
}
