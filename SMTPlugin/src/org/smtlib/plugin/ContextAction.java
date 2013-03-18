/*
 * This file is part of the SMT plugin project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.plugin;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IActionDelegate;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;

/** This class is an abstract base class for implementing popup menu item actions.
 * @author David R. Cok
 */
abstract public class ContextAction implements IObjectActionDelegate {
    /** A cached value of the most recent selection */
	/*@Nullable*/ protected ISelection selection;

    /** A cached value of the shell that holds the most recent editor (actually IWorkbenchPart) */
    /*@Nullable*/ protected Shell shell;
	
	/**
	 * Constructor, with no initialization
	 */
	public ContextAction() {
		super();
	}

	/**
	 * @see IObjectActionDelegate#setActivePart(IAction, IWorkbenchPart)
	 */
	//@ ensures this.shell != null;
    @Override
	public void setActivePart(IAction action, IWorkbenchPart targetPart) {
		shell = targetPart.getSite().getShell();
	}

	/**
	 * @see IActionDelegate#run(IAction)
	 */
    @Override
	abstract public void run(IAction action);

	/**
	 * @see IActionDelegate#selectionChanged(IAction, ISelection)
	 */
	//@ ensures this.selection != null;
    @Override
	public void selectionChanged(IAction action, ISelection selection) {
        this.selection = selection;
	}

	/** Runs the default solver on the selected files */
	static public class RunSolver extends ContextAction {
		/**
		 * @see IActionDelegate#run(IAction)
		 */
	    @Override
		public void run(IAction action) {
    		try {
    			final List<String> solvers = Activator.utils.getSolvers(action.getId());
    			List<IFile> files = Activator.utils.getSelectedFiles(selection,null,shell);
    			Activator.utils.text = null; // TODO - setting 'text' through side-effects is a bad design
        		if (files.isEmpty()) files = Activator.utils.resources(selection,null,shell); // sets Activator.utils.text also
        		if (files.isEmpty()) {
        			Activator.utils.showMessageInUI(shell,"SMT Run Solver",
        					"Failed to find a resource on which to run a solver (select one or more files or an editor)");
        			return;
        		}
    			Activator.utils.runJobs(solvers,files);
    		} catch (Exception e) {
    			Activator.utils.topLevelException(shell,"ContextAction.RunSolver",e);
    		}
        }
	}
	
	
	/** Deletes SMT markers on selected resources */
	static public class DeleteMarkers extends ContextAction {
		/**
		 * @see IActionDelegate#run(IAction)
		 */
	    @Override
		public void run(IAction action) {
            try {
                Activator.utils.deleteMarkersInSelection(selection,null,shell);
            } catch (Exception e) {
                Activator.utils.topLevelException(shell,"ContextAction.DeleteMarkers",e);
            }
		}
	}

// Not included because the ViewLogic command uses selected text; it does not make sense
// to run it on a file.
//	/** Shows the content of the SMT logic or theory whose name is selected */
//	static public class ViewLogic extends ContextAction {
//		/**
//		 * @see IActionDelegate#run(IAction)
//		 */
//		public void run(IAction action) {
//        	Activator.utils.viewLogic(shell,selection);
//		}
//	}

}

