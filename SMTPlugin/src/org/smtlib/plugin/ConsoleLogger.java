/*
 * This file is part of the SMT plugin project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.plugin;

import java.io.IOException;
import java.io.PrintStream;

import org.eclipse.core.runtime.ILog;
import org.eclipse.core.runtime.Plugin;
import org.eclipse.core.runtime.Status;
import org.eclipse.swt.graphics.Color;
import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IConsoleManager;
import org.eclipse.ui.console.MessageConsole;
import org.eclipse.ui.console.MessageConsoleStream;
import org.smtlib.IResponse;

/** This class provides Log.IListener implementation that listens
 * to messages written through methods in the plug-in Log and sends them to the Eclipse console;
 * also listens to messages written through the application log.
 */
public class ConsoleLogger implements org.smtlib.plugin.Log.IListener, org.smtlib.Log.IListener {

	/** Creates a new ConsoleLogger utility object
	 * 
	 * @param consoleName The name of the console to be logged to
	 */
	//@ requires consoleName != null;
	//@ requires Activator.plugin != null;
	//@ modifies \nothing;
	//@ ensures \result.consoleName == consoleName;
	public ConsoleLogger(/*@NonNull*/ String consoleName) {
		this.consoleName = consoleName;
		Plugin plugin = Activator.getDefault();
		this.pluginLog = plugin.getLog();
		this.pluginID = plugin.getBundle().getSymbolicName();
	}

	// This model variable models the content of the material
	// sent to the log.
	//@ model public String content;

	/** The name of the console that this plugin writes to. */
	//@ constraint \not_modified(consoleName);
	//@ spec_public
	//@ non_null
	/*@NonNull*/
	final private String consoleName;

	/** The ILog of the plugin that this ConsoleLogger object connects to */
	//@ constraint \not_modified(pluginLog);
	//@ invariant pluginLog != null;
	//@ spec_public
	final private ILog pluginLog;

	/** The id of the plugin using this log */
	//@ constraint \not_modified(pluginID);
	//@ invariant pluginID != null;
	//@ spec_public
	/*@NonNull*/
	final private String pluginID;

	/** Cached value of the stream to use to write to the console */
	/*@Nullable*/
	private MessageConsoleStream stream = null;
	//@ private constraint \old(stream) != null ==> \not_modified(stream);

	/** The associated PrintStream, lazily initialized */
	/*@Nullable*/
	private PrintStream printStream = null;

	/** Creates, if necessary, and returns an instance of
	 *  the stream to use to write to the console
	 * @return The stream value to use
	 */
	//@ modifies stream;
	//@ ensures \result != null;
	//@ ensures \result == stream;
	public MessageConsoleStream getConsoleStream() {
		if (stream == null) {
			/*@Mutable*/ MessageConsole console = null;
			IConsoleManager consoleManager = ConsolePlugin.getDefault().getConsoleManager();
			/*@Mutable*/ IConsole[] existing = consoleManager.getConsoles();
			for (int i=0; i<existing.length; ++i) {
				if (existing[i].getName().equals(consoleName)) {
					console = (/*@Mutable*/ MessageConsole)existing[i];
					break;
				}
			}
			if (console == null) {
				console = new MessageConsole(consoleName,null);
				consoleManager.addConsoles(new IConsole[]{console});
			}
			stream = console.newMessageStream();
		}
		return stream;
	}

	/** Color to use for error messages */
	// TODO - should get this color from the system preferences
	static final private Color errorColor = new Color(null,255,0,0);
	static final private Color diagColor = new Color(null,0,0,255);

	/**
	 * Records an informational message
	 * @param msg The message to log
	 */
	//@ requires msg != null;
	//@ modifies content, stream;
	@Override
	public void log(String msg) {
		getConsoleStream().print(msg);
	}

	/**
	 * Records an informational message, adding a newline
	 * @param msg The message to log
	 */
	//@ requires msg != null;
	//@ modifies content, stream;
	@Override
	public void logln(String msg) {
		getConsoleStream().println(msg);
	}

	/**
	 * Records an error message, writing it to the console and the plug-in error log;
	 * adds line separator
	 * @param msg The message to log
	 * @param e An associated exception (may be null)
	 */
	// TODO - must this be called from the UI thread (because it sets the color)?
	//@ modifies content;
	@Override
	public void errorlog(/*@NonNull*/String msg, /*@Nullable*/ Throwable e) {
		// Always put errors in the plug-in Error log
		pluginLog.log(
				new Status(Status.ERROR, 
						pluginID,
						Status.OK, msg, e));
		MessageConsoleStream cs = getConsoleStream();
		Color c = cs.getColor();
		cs.setColor(errorColor);
		cs.println(msg);
		if (e != null) e.printStackTrace(this.stream());
		cs.setColor(c);
	}

	/** Flushes the associated console stream */
	public void flush() throws IOException {
		getConsoleStream().flush();
	}


	/**
	 * Creates a PrintStream that, when written to, writes to the Eclipse Console
	 * of the current log object
	 * 
	 * @return a PrintStream connected to the Eclipse Console
	 */
	//@ modifies printStream, stream;
	//@ ensures \result != null;
	//@ ensures \result == printStream;
	public PrintStream stream() {
		if (printStream == null) printStream = new PrintStream(getConsoleStream());
		return printStream;
	}


	/** This listens to and echos to the console regular log messages from the SMT application;
	 *  no additional line separators added. */
	@Override
	public void logOut(String msg) {
		log(msg);
	}

	/** This listens to and echos to the console regular log messages from the SMT application;
	 *  adds a line separator */
	@Override
	public void logOut(IResponse response) {
		logln(Activator.smtConfiguration.defaultPrinter.toString(response));
	}

	@Override
	public void indent(String prompt) {
	}


	/** This listens to messages from the SMT application - errors are caught by the Problem listener,
	 * so they are not logged here, unless verbose is requested.  Also SMT-LIB errors are not turned into
	 * Error log entries either. */
	@Override
	public void logError(IResponse.IError response) {
		logError(Activator.smtConfiguration.defaultPrinter.toString(response));
	}

	@Override
	public void logError(String msg) {
		if (Activator.verbose) {
			MessageConsoleStream cs = getConsoleStream();
//			Color c = cs.getColor();
//			cs.setColor(errorColor);
			cs.println(msg);
//			cs.setColor(c); // FIXME - causes "Invalid Thread access" errors when logging errors from a computational thread
		}
	}


	/** This listens to and echos to the console diagnostic messages from the SMT application.
	 *  Adds a line separator */
	@Override
	public void logDiag(String msg) {
		MessageConsoleStream cs = getConsoleStream();
//		Color c = cs.getColor();
//		cs.setColor(diagColor);
		cs.println(msg);
//		cs.setColor(c); // FIXME - causes "Invalid Thread access" errors when logging errors from a computational thread
	}
}

