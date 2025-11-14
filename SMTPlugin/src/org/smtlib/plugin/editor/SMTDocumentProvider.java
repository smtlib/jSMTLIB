/**
 * This class is part of the SMT Plugin
 * @author David R. Cok
 * September 2010
 */
package org.smtlib.plugin.editor;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.rules.FastPartitioner;
import org.eclipse.ui.editors.text.FileDocumentProvider;

/** This class is a DocumentProvider, connecting a document partitioner with 
 * the argument to createDocument*/
public class SMTDocumentProvider extends FileDocumentProvider {

	@Override
	protected IDocument createDocument(Object element) throws CoreException {
		IDocument document = super.createDocument(element);
		if (document != null) {
			IDocumentPartitioner partitioner =
				new FastPartitioner(
					new SMTPartitionScanner(),
					SMTPartitionScanner.tokenNames); // No default listed here
			partitioner.connect(document);
			document.setDocumentPartitioner(partitioner);
		}
		return document;
	}
}