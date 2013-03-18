/*
 * This file is part of the SMT plugin project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.plugin;

/** All log messages from the plug-in are sent to this class. */
public class Log {

	/** An interface for objects that want to receive any plug-in log messages  */
	public static interface IListener {
		/** Called when a log message is recorded in the log (listener should NOT add line separator). */
		public void log(String msg);

		/** Called when a log message is recorded in the log (listener should add line separator). */
		public void logln(String msg);

		/** Called when an error message is recorded in the log (listener should add line separator). */
		public void errorlog(String msg, /*@Nullable*/ Throwable e);
	}

	/**
	 * Called to record an ordinary message; notifies any listeners;
	 * if no listeners, simply writes to System.out (no line separator added)
	 */
	public void log(String s) {
		if (listener != null)
			listener.log(s);
		else
			System.out.print(s);
	}
	
	/**
	 * Called to record an ordinary message; notifies any listeners;
	 * if no listeners, simply writes to System.out (line separator added)
	 */
	public void logln(String s) {
		if (listener != null) {
			listener.logln(s);
		} else
			System.out.println(s);
	}

	/**
	 * Called to record an error message; notifies any listeners;
	 * if no listeners, simply writes to System.out; adds line separator
	 */
	public void errorlog(String s, Throwable e) {
		if (listener != null)
			listener.errorlog(s,e);
		else
			System.out.println(s);
	}

	/** The (at most) one listener */
	/*@Nullable */
	public IListener listener = null;

	/** Adds a listener to the log - only one listener is allowed */
	public void setListener(IListener l) {
		listener = l;
	}

}
