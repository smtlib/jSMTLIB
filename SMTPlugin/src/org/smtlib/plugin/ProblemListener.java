/*
 * This file is part of the SMT plugin project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.plugin;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.smtlib.IPos;

/** This class listens to log messages from the org.smtlib.Log message logger; 
 * it converts any error messages it hears into Eclipse problem markers.
 * @author David Cok
 *
 */
public class ProblemListener implements org.smtlib.Log.IListener {

	@Override
	public void indent(String prompt) {
	}

	/** Hears error messages from the parent interface */
	@Override
	public void logError(org.smtlib.IResponse.IError r) {
		notify(r);
	}

	/** Hears error messages from the parent interface */
	@Override
	public void logError(String msg) {
		// Positionless error messages are shown in a dialog box
		Activator.utils.showMessageInUI(null,"SMT Error", msg);
	}

	/** Hears regular messages from the parent interface */
	@Override
	public void logOut(String message) { // Don't capture these
	}
	
	/** Hears regular messages from the parent interface */
	@Override
	public void logOut(org.smtlib.IResponse r) { // Don't capture these
	}
	
	/** Hears diagnostic messages from the parent interface */
	@Override
	public void logDiag(String message) { // Don't capture these
	}
	
	/** Does the actual work of creating a marker for the given CommandResult */
	public void notify(org.smtlib.IResponse.IError result) {
		try {
			IResource f = null;
			String msg = Activator.smtConfiguration.defaultPrinter.toString(result);
			if (!(result instanceof IPos.IPosable)) {
				Activator.utils.showMessageInUI(null,"SMT Error", msg);
				return;
			}
			IPos pos = ((IPos.IPosable)result).pos();
			if (pos == null) {
				Activator.utils.showMessageInUI(null,"SMT Error", msg);
				return;
			}
			if (pos.source() == null) {
				Activator.utils.showMessageInUI(null,"SMT Error", msg);
				return;
			}
			Object location = pos.source().location();
			if (location == null) {
				Activator.utils.showMessageInUI(null,"SMT Error", msg);
				return;
			}
			
			String filename = location.toString(); // Note: locations are not necessarily paths,
											// but if it is not, I presume we'll just not find it
											// in the workspace further on
			IWorkspace w = ResourcesPlugin.getWorkspace();
			IWorkspaceRoot root = w.getRoot();
			//Activator.log.log("LOC " + root.getLocation() + " " + filename);
			f = root.findMember(filename);
			if (f == null) {
				Path path = new Path(filename);
				f = root.getFileForLocation(path);
				filename = filename.substring(root.getLocation().toString().length());
			}
			if (f == null) {
				Activator.log.logln("Could not find resource " + filename); // FIXME - errorlog?
				f = root;
			}
			// Use the following if you want problems printed to the console
			// as well as producing markers and annotations

			final IResource r = f;
			final int finalOffset = pos.charStart();
			final int finalEnd = pos.charEnd();
			final int finalLineNumber = pos.source().lineNumber(finalOffset);
			final String finalErrorMessage = result.errorMsg();
			final int finalSeverity = IMarker.SEVERITY_ERROR ; // All SMT problems are errors, not warnings

			// Eclipse recommends that things that modify the resources
			// in a workspace be performed in a IWorkspaceRunnable
			IWorkspaceRunnable runnable = new IWorkspaceRunnable() {
				//JAVA16 @Override
				public void run(IProgressMonitor monitor) throws CoreException {
					IMarker marker = r.createMarker(Utils.SMT_MARKER_ID);
					marker.setAttribute(IMarker.LINE_NUMBER, 
							finalLineNumber >= 1? finalLineNumber : 0);
					marker.setAttribute(IMarker.CHAR_START, finalOffset); 
					marker.setAttribute(IMarker.CHAR_END, finalEnd);

					// Note - it appears that CHAR_START is measured from the beginning of the
					// file and overrides the line number
					// However, the LINE_NUMBER attribute is used for the 'Location' column
					// of the Problems view

					marker.setAttribute(IMarker.SEVERITY,finalSeverity);
					marker.setAttribute(IMarker.MESSAGE, finalErrorMessage);
				}
			};
			r.getWorkspace().run(runnable, null); // FIXME - should we use a specified ISchedulingRule?
		} catch (Exception e) {
			Activator.log.errorlog("Failed to make a marker " + e,e);
		}
	}
}
