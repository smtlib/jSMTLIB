/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.impl;

import java.io.*;

import org.smtlib.*;

/** Represents a range of characters in a source - used to indicate the location of errors */
public class Pos implements IPos {

	/** The starting character, beginning from 0 */
	protected int charStart;
	/** One past the last character of the range, beginning from 0 */
	protected int charEnd;

	/** The source of text */
	protected /*@Nullable*/ISource source;
	
	/** Constructor for a Pos object
	 * @param cs the start position of the character range, 0-based
	 * @param ce one past the end position of the character range, 0- based
	 * @param s the source of text to which the character positions refer
	 */
	public Pos(int cs, int ce, /*@Nullable*/ISource s) {
		this.charStart = cs;
		this.charEnd = ce;
		this.source = s;
	}
	
	/** The starting character, beginning from 0 */
	@Override
	public int charStart() { return charStart; }
	/** One past the last character of the range, beginning from 0 */
	@Override
	public int charEnd() { return charEnd; }
	/** The source of text */
	@Override
	public /*@Nullable*/ISource source() { return source; }

	/** An implementation of IPosable, holding an instance of Pos,
	 *  that can be used as a base class if necessary */
	public static class Posable implements IPosable {
		protected /*@Nullable*/ IPos pos;
		@Override
		public IPos pos() { return pos; }
		@Override
		public void setPos(IPos pos) { this.pos = pos; }

		// Defined here (rather than on INode) because Java forbids interface default methods from overriding
		// Object methods. Identity semantics is the correct default for AST nodes: 
		// internal maps always key on the same parsed object instance. Classes requiring structural equality
		// (Numeral, Symbol, Keyword, etc.) override these explicitly.
		@Override
		public boolean equals(Object o) { return this == o; }
		@Override
		public int hashCode() { return System.identityHashCode(this); }
	}

	/** A Posable that also implements INode, with toString() delegating to Printer.
	 *  This toString() exists purely for debugger/IDE display convenience - it must
	 *  never be relied on for program logic or real output. Production code that needs
	 *  to render a node must go through IPrinter/Printer explicitly (e.g.
	 *  smtConfig.defaultPrinter.toString(...)), not this method. */
	public static abstract class Printable extends Posable implements INode {
		@Override
		public String toString() {
			return org.smtlib.sexpr.Printer.write(this);
		}
	}

	/** A Printable that also implements IExpr, additionally holding the sort computed for
	 *  the expression by the type checker (null if not yet, or never, computed). */
	public static abstract class AbstractExpr extends Printable implements IExpr {
		protected /*@Nullable*/ ISort sort;
		@Override
		public /*@Nullable*/ ISort sort() { return sort; }
		@Override
		public void setSort(/*@Nullable*/ ISort sort) { this.sort = sort; }
	}


	/** An implementation of the ISource interface */
	public static class Source implements ISource {
		private Reader rdr = null;
		
		/** The sequence of characters */
		private CharSequence chars;
		/** The sequence of characters */
		@Override
		public CharSequence chars() { return chars; }
		
		/** The identifier for the location */
		private /*@Nullable*/ Object location;
		/** The identifier for the location */
		@Override
		public /*@Nullable*/ Object location() { return location; }

		/** Creates a Source from a character sequence
		 * @param cs the sequence to use as a source of characters
		 * @param location a designator of the location of the source, used for identification only
		 */
		public Source(CharSequence cs, /*@Nullable*/ Object location) {
			this.chars = cs;
			this.location = location;
		}

		/** Creates a Source from a File; for these objects, the location is the file path (a String)
		 * @param smtConfig the SMT Configuration object
		 * @param f the File object from which to read characters
		 * @throws java.io.FileNotFoundException if a problem occurred opening or reading the file
		 */
		public Source(SMT.Configuration smtConfig, java.io.File f) throws java.io.FileNotFoundException {
			rdr = new FileReader(f);
			// The numbers in the next call are not magic - they just double the buffer by a factor of 2 if it is not large enough
			CharSequenceReader csr = new CharSequenceReader(rdr,smtConfig.initialInputBufferSize,0,2);
			csr.prompter = new SMT.Prompter(smtConfig);
			chars = csr;
			this.location = f.getPath();
		}
		
		/** Creates a Source from a File
		 * @param smtConfig the SMT Configuration object
		 * @param f the InputStream object from which to read characters
		 * @param location object describing the location of the source
		 */
		public Source(SMT.Configuration smtConfig, InputStream f, Object location) {
			rdr = new InputStreamReader(f);
			// The numbers in the next call are not magic - they just double the buffer by a factor of 2 if it is not large enough
			CharSequenceReader csr = new CharSequenceReader(rdr,smtConfig.initialInputBufferSize,0,2);
			csr.prompter = new SMT.Prompter(smtConfig);
			chars = csr;
			this.location = location;
		}
		
		@Override
		public void close() {
			try {
				rdr.close();
			} catch (IOException e) {}
		}
		
		@Override
		public char charAt(int pos) {
			return this.chars.charAt(pos);
		}
		
		// FIXME - what about empty lines
		@Override
		public int lineBeginning(int pos) {
			int p = pos;
			if (p >= chars().length()) p = chars().length()-1; // If the length is indeterminate, length() should be INT_MAX
			if (p > 0 && charAt(p) == '\n' && charAt(p-1) == '\r') --p;
			char c;
			while (p >= 0 && (c=charAt(p)) != '\n' && c != '\r') --p;
			return p+1;
		}
		
		private final static String eol = System.getProperty("line.separator");
		
		@Override
		public String textLine(int pos) {
			int b = lineBeginning(pos);
			int e = nextLineTermination(pos);
			String s = chars.subSequence(b,e+1).toString();
			char c = s.length() == 0 ? ' ' : s.charAt(s.length()-1);
			if (c != '\n' && c != '\r') s = s + eol;
			return s;
		}

		/** The (last character of) the next line termination sequence after the given character position */
		//@ requires pos >= 0;
		//@ ensures \result >= pos;
		protected int nextLineTermination(int pos) {
			char c;
			if (pos >= chars().length()) return chars().length()-1; // If the length is indeterminate, length() should be INT_MAX
			while ((c=charAt(pos)) != '\n' && c != '\r' && c != CharSequenceInfinite.endChar) ++pos;
			if (c == '\r' && charAt(pos+1) == '\n') ++pos;
			else if (c == CharSequenceInfinite.endChar) --pos;
			return pos;
		}
		
		// Note: this counts lines from the beginning of the character sequence, calling charAt at each
		// character position; this is not very efficient; the presumption is that this method is called
		// just for the occasional error message.
		@Override
		public int lineNumber(int pos) {
			int line = 1;
			char c;
			for (int i=0; i<pos; i++) {
				c = charAt(i);
				if (c == '\n') line++;
				else if (c == '\r') {
					line++;
					if (charAt(i+1) == '\n') i++;
				}
			}
			return line;
		}
	}
}
