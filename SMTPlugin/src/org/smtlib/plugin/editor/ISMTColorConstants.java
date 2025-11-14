/**
 * This class is part of the SMT Plugin
 * @author David R. Cok
 * September 2010
 */
package org.smtlib.plugin.editor;

import org.eclipse.swt.graphics.RGB;

/** This class defines color constants to be used for syntax coloring. */
// FIXME - should allow setting these from the preferences
public interface ISMTColorConstants {
	RGB DEFAULT = new RGB(0, 0, 0); // default text color is black
	RGB SMT_COMMENT = new RGB(128, 128, 128); // gray for comments
	RGB SMT_KEYWORD = new RGB(0, 0, 255);
	RGB SMT_NUMERAL = new RGB(0, 0, 255);
	RGB SMT_DECIMAL = new RGB(0, 128, 255);
	RGB SMT_STRING = new RGB(0, 0, 255);
	RGB SMT_SYMBOL = new RGB(0, 128, 0);
	RGB SMT_QSYMBOL = new RGB(0, 255, 0);
	RGB SMT_PAREN = new RGB(255, 0, 255);
	RGB SMT_COMMAND = new RGB(128, 128, 255);
	RGB SMT_HEX = new RGB(0, 0, 255);
	RGB SMT_BINARY = new RGB(0, 0, 255);
	RGB SMT_INVALID = new RGB(255, 0, 0);
	RGB SMT_RESERVED_WORD = new RGB(0, 0, 128);
}
