/**
 * This class is part of the SMT Plugin
 * @author David R. Cok
 * September 2010
 */
package org.smtlib.plugin.editor;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentListener;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.editors.text.TextEditor;
import org.smtlib.plugin.Activator;


/** This class defines a custom text editor, adding syntax coloring 
 * and automatic type checking when a file is edited. */
public class SMTEditor extends TextEditor {

	public SMTEditor() {
		super();
		setSourceViewerConfiguration(new SMTConfiguration());
		setDocumentProvider(new SMTDocumentProvider());
	}
	
	@Override
	protected void doSetInput(final IEditorInput input) throws CoreException {
		super.doSetInput(input);
		IDocument d = getDocumentProvider().getDocument(input);
		d.addDocumentListener(new IDocumentListener() {
			
			@Override
			public void documentAboutToBeChanged(DocumentEvent event) {
			}

			@Override
			public void documentChanged(DocumentEvent event) {
				IFile f = (IFile)input.getAdapter(IFile.class);
				Activator.utils.runCheck(f,event.getDocument().get());
				// FIXME _ create a class so we can move these dependencies out of this file?
				// FIXME - do the rechecking in a background thread?
				// FIXME - condition the checking on an option - on edit? on save? manual only? in the background?

			}
		});
		
	}
	
	@Override
	public void dispose() {
		super.dispose();
	}

}
