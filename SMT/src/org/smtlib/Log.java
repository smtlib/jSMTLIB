/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

import java.util.LinkedList;
import java.util.List;

import org.smtlib.IPos.ISource;


/** This class is used as a collection point for all output.  The SMTLIB defines two output
 * streams - regular output and diagnostic output, normally assigned to standard out and stderr.
 * 
 * @author David Cok
 *
 */
public class Log {
	
	/** Number of errors logged since last clear */
	public int numErrors = 0;
	
	/** Keeps a reference to smtConfig for this instance of the SMT tool*/
	/*@NonNull*/ private SMT.Configuration smtConfig;
	
	/** Constructs a Log based on the given configuration */
	public Log(SMT.Configuration smtConfig) {
		this.smtConfig = smtConfig;
		addListener(new StandardListener());
	}
	
	/** This is an interface to be implemented by any Object that wants to hear log
	 * messages; the Object must register itself by calling Log.addListener.
	 */
	public static interface IListener {
		/** Logs the given msg to the SMT-LIB normal output (with no additional line termination) */
		public void logOut(String msg);
		/** Logs the given response to the SMT-LIB normal output, with a line termination */
		public void logOut(/*@ReadOnly*/ IResponse result);
		/** Logs the given msg to the SMT-LIB normal output as an error message (with line termination added) */
		public void logError(String msg);
		/** Logs an error response to the SMT-LIB normal output, with error position information, and line termination */
		public void logError(/*@ReadOnly*/ IResponse.IError result);
		/** Logs the given message to the SMT-LIB diagnostic output (with line termination) */
		public void logDiag(String msg);
		/** Amount of offset in the input line */
		public void indent(String chars);
	}
	
	/** This class logs to the standard PrintStreams out and diag.  The class is not static so that it
	 * can see out and diag in the containing class; it needs to do this so that changes to out and diag 
	 * are reflected here as well.
	 */
	public class StandardListener implements IListener {
		String prompt = null;
		
		@Override
		public void indent(String chars) {
			prompt = chars;
		}
		
		/** Writes the message to the 'out' PrintStream */
		@Override
		public void logOut(String msg) {
			out.print(msg);
		}
		
		/** Writes the given response to the out stream */
		@Override
		public void logOut(/*@ReadOnly*/ IResponse response) {
			out.println(smtConfig.defaultPrinter.toString(response));
		}

		/** Writes the message to the 'out' PrintStream */
		@Override
		public void logError(String msg) {
			out.println(msg);
		}
		
		/** Writes the offending text line, column location in that line, and the error message
		 * to the 'out' stream.
		 */
		@Override
		public void logError(/*@ReadOnly*/IResponse.IError result) {
			IPos pos = result.pos();
			if (pos != null && pos.source() != null && !smtConfig.noshow) {
				out.println(locationIndication(pos,prompt,smtConfig));
			}
			// Print the actual response
			out.println(smtConfig.defaultPrinter.toString(result));
		}
		

		/** Writes the message to the diag stream */
		@Override
		public void logDiag(String msg) {
			diag.println(msg);
		}
		
	}
	
	/** The list of listeners to send log messages to */
	private List<IListener> listeners = new LinkedList<IListener>();
	
	/** The stream used for regular output and error information */
	public /*@NonNull*/ java.io.PrintStream out = System.out;
	
	/** The stream used for diagnostic log information */
	public /*@NonNull*/ java.io.PrintStream diag = System.err;

	/** Prints the argument on the regular output stream and to any listeners */
	public void logOut(/*@NonNull*/ IResponse r) {
		for (IListener listener: listeners) {
			listener.logOut(r);
		}
	}
	
	/** Prints the argument on the regular output stream and to any listeners*/
	public void logOut(/*@NonNull*/ String message) {
		for (IListener listener: listeners) {
			listener.logOut(message);
		}
	}
	
	/** Prints the argument on the regular output stream with no newline, and to any listeners. */
	public void logOutNoln(/*@NonNull*/ String message) {
		for (IListener listener: listeners) {
			listener.logOut(message);
		}
	}

	/** Reports the error to any listeners. */
	public void logError(/*@NonNull*//*@ReadOnly*/ IResponse.IError r) {
		numErrors++;
		for (IListener listener: listeners) {
			listener.logError(r);
		}
	}
	
	/** Reports the error to any listeners. */
	public void logError(/*@NonNull*/String r) {
		numErrors++;
		for (IListener listener: listeners) {
			listener.logError(r);
		}
	}
	
	/** Prints the argument to any listeners. */
	public void logDiag(/*@NonNull*/ IResponse r) {
		logDiag(smtConfig.defaultPrinter.toString(r));
	}

	/** Prints the argument to any listeners (adds a line terminator). */
	public void logDiag(/*@NonNull*/ String message) {
		for (IListener listener: listeners) {
			listener.logDiag(message);
		}
	}
	
	/** Sends the call to any listeners. */
	public void indent(/*@NonNull*/ String prompt) {
		for (IListener listener: listeners) {
			listener.indent(prompt);
		}
	}
	
	/** Adds a listener */
	public void addListener(IListener listener) {
		listeners.add(listener);
	}
	
	/** Clears all listeners */
	public void clearListeners() {
		listeners.clear();
	}
	
	/** Removes a listener (found by using object equality ==)
	 * @param listener the listener to add
	 * @return true if the argument was in the list
	 */
	public boolean removeListener(IListener listener) {
		return listeners.remove(listener);
	}

	// Result does not have a final line-termination
	static public String locationIndication(IPos pos, String prompt, SMT.Configuration smtConfig) {
		int s = pos.charStart();
		int e = pos.charEnd();
		ISource source = pos.source();
		int b;
		StringBuilder sb = new StringBuilder();
		b = source.lineBeginning(s);
		// Print the text line
		if (!smtConfig.interactive) {
			String input = source.textLine(s);
			// input will have a line terminator
			sb.append(input);
		}
		// Show the location in the text line
		if (smtConfig.interactive && prompt != null) {
			int bb = 0;
			while (bb < prompt.length()) {
				char c = prompt.charAt(bb);
				sb.append(c == '\t' ? '\t' : ' ');
				bb++;
			}
		}
		while (b < s) {
			char c = source.charAt(b);
			sb.append(c == '\t' ? '\t' : ' ');
			b++;
		}
		while (b++ < e) {
			sb.append('^');
		}
		return sb.toString();
	}

}