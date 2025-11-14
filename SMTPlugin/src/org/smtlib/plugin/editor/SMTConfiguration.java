/**
 * This class is part of the SMT Plugin
 * @author David R. Cok
 * September 2010
 */
package org.smtlib.plugin.editor;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextDoubleClickStrategy;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.presentation.PresentationReconciler;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.ui.editors.text.TextSourceViewerConfiguration;

/** This file extends its super class in order to add customized syntax coloring
 * Using TextSourceViewerConfiguration instead of SourceViewerConfiguration
 * gives hover information on problem icons.  It can also provide double-click
 * and quick-assist functionality, but these are not yet implemented.
 * @author David R. Cok
 *
 */
// FIXME - document
// FIXME - implement double click and quick assist
public class SMTConfiguration extends TextSourceViewerConfiguration {
	private SMTDoubleClickStrategy doubleClickStrategy;
	private RuleBasedScanner scanner;

	public SMTConfiguration() {
	}
	
	@Override
	public String[] getConfiguredContentTypes(ISourceViewer sourceViewer) {
		return SMTPartitionScanner.tokenNamesWithDefault; // Must include the default
	}
	
	@Override
	public ITextDoubleClickStrategy getDoubleClickStrategy(
		ISourceViewer sourceViewer,
		String contentType) {
		if (doubleClickStrategy == null)
			doubleClickStrategy = new SMTDoubleClickStrategy();
		return doubleClickStrategy;
	}

	protected RuleBasedScanner getScanner() {
		if (scanner == null) {
			scanner = new SMTPartitionScanner();
			scanner.setDefaultReturnToken(
				SMTPartitionScanner.smtDefault);
		}
		return scanner;
	}

	final static public RGB[] colors = {
		ISMTColorConstants.SMT_COMMENT, ISMTColorConstants.SMT_NUMERAL, ISMTColorConstants.SMT_DECIMAL, 
		ISMTColorConstants.SMT_SYMBOL, ISMTColorConstants.SMT_QSYMBOL, ISMTColorConstants.SMT_RESERVED_WORD,
		ISMTColorConstants.SMT_KEYWORD, ISMTColorConstants.SMT_COMMAND,
		ISMTColorConstants.SMT_HEX, ISMTColorConstants.SMT_BINARY, ISMTColorConstants.SMT_STRING,
		ISMTColorConstants.SMT_PAREN, ISMTColorConstants.SMT_INVALID,
	};
	
	final static public String[] tokens = {
		SMTPartitionScanner.SMT_COMMENT, SMTPartitionScanner.SMT_NUMERAL, SMTPartitionScanner.SMT_DECIMAL, 
		SMTPartitionScanner.SMT_SYMBOL, SMTPartitionScanner.SMT_QSYMBOL, SMTPartitionScanner.SMT_RESERVED_WORD,
		SMTPartitionScanner.SMT_KEYWORD, SMTPartitionScanner.SMT_COMMAND,
		SMTPartitionScanner.SMT_HEX, SMTPartitionScanner.SMT_BINARY, SMTPartitionScanner.SMT_STRING,
		SMTPartitionScanner.SMT_PAREN, SMTPartitionScanner.SMT_INVALID,
	};
	
	@Override
	public IPresentationReconciler getPresentationReconciler(ISourceViewer sourceViewer) {
		PresentationReconciler reconciler = new PresentationReconciler();

		DefaultDamagerRepairer dr;

		dr = new DefaultDamagerRepairer(getScanner());
		
		reconciler.setDamager(dr, IDocument.DEFAULT_CONTENT_TYPE);
		reconciler.setRepairer(dr, IDocument.DEFAULT_CONTENT_TYPE);

		return reconciler;
	}

}