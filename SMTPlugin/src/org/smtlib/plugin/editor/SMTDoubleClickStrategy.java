/**
 * This class is part of the SMT Plugin
 * @author David R. Cok
 * September 2010
 */
package org.smtlib.plugin.editor;

import org.eclipse.jface.text.*;

/** This class implements the action that happens when a double-click happens on text - for example
 * selecting the whole word or token.
 * @author David R. Cok
 *
 */

// FIXME - the double-click strategy is not implemented for SMT
public class SMTDoubleClickStrategy implements ITextDoubleClickStrategy {
	protected ITextViewer fText;

	@Override
	public void doubleClicked(ITextViewer part) {
		int pos = part.getSelectedRange().x;

		if (pos < 0)
			return;

		fText = part;

		//if (!selectComment(pos)) {
			selectWord(pos);
		//}
	}
	
	// FIXME - this selects a Java comment - don't need this here - change it??
	protected boolean selectComment(int caretPos) {
		IDocument doc = fText.getDocument();
		int startPos, endPos;

		try {
			int pos = caretPos;
			char c = ' ';

			while (pos >= 0) {
				c = doc.getChar(pos);
				if (c == '\\') {
					pos -= 2;
					continue;
				}
				if (c == Character.LINE_SEPARATOR || c == '\"')
					break;
				--pos;
			}

			if (c != '\"')
				return false;

			startPos = pos;

			pos = caretPos;
			int length = doc.getLength();
			c = ' ';

			while (pos < length) {
				c = doc.getChar(pos);
				if (c == Character.LINE_SEPARATOR || c == '\"')
					break;
				++pos;
			}
			if (c != '\"')
				return false;

			endPos = pos;

			int offset = startPos + 1;
			int len = endPos - offset;
			fText.setSelectedRange(offset, len);
			return true;
		} catch (BadLocationException x) {
		}

		return false;
	}
	
	// FIXME - this selects a Java word
	protected boolean selectWord(int caretPos) {
		

		IDocument doc = fText.getDocument();
		int startPos, endPos;

		try {
//			ITypedRegion region = doc.getPartition(caretPos);
//			startPos = region.getOffset();
//			endPos = startPos + region.getLength();

			int pos = caretPos;
			char c;

			while (pos >= 0) {
				c = doc.getChar(pos);
				if (c == '(' || c == ')' || c <= ' ') break;
				--pos;
			}

			startPos = pos;

			pos = caretPos;
			int length = doc.getLength();

			while (pos < length) {
				c = doc.getChar(pos);
				if (c == '(' || c == ')' || c <= ' ') break;
				++pos;
			}

			endPos = pos;
			selectRange(startPos, endPos);
			return true;

		} catch (BadLocationException x) {
		}

		return false;
	}

	private void selectRange(int startPos, int stopPos) {
		int offset = startPos + 1;
		int length = stopPos - offset;
		fText.setSelectedRange(offset, length);
	}
}