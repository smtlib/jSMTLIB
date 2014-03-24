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
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;

/**
 * This class holds the implementations of the utils in response to
 * menu items in the menubar and toolbar
 */
abstract public class MenuActions implements IWorkbenchWindowActionDelegate {

    // IWorkbenchWindowActionDelegate is the interface for actions that
    // are contributed as menubar or toolbar items

    /** Caches the value of the window, when informed of it. */
    /*@Nullable*/ protected IWorkbenchWindow window;

    /** Caches the value of the shell in which the window exists. */
    /*@Nullable*/ protected Shell shell = null;

    /** The current selection. */
    /*@Nullable*/ protected ISelection selection;

    /* (non-Javadoc)
     * @see org.eclipse.ui.IActionDelegate#selectionChanged(org.eclipse.jface.action.IAction, org.eclipse.jface.viewers.ISelection)
     */
    //@ ensures this.selection != null;
    //JAVA16 @Override
    public final void selectionChanged(final IAction action, final ISelection selection) {
        this.selection = selection;
    }

    /**
     * We can use this method to dispose of any system
     * resources we previously allocated.
     * @see IWorkbenchWindowActionDelegate#dispose
     */
    //JAVA16 @Override
    public void dispose() {
    }

    /**
     * We will cache window object in order to
     * be able to provide a parent shell for the message dialog.
     * @param window The parent window
     * @see IWorkbenchWindowActionDelegate#init
     */
    //JAVA16 @Override
    public void init(IWorkbenchWindow window) {
        this.window = window;
        this.shell = window.getShell();
    }

    /** Called by the system in response to a menu selection (or other command).
     * This should be overridden for individual menu items.
     */
    //JAVA16 @Override
    abstract public void run(final IAction action);

    /**
     * This class implements the action for checking
     * JML in the selected objects (which may be working sets, folders,
     * or java files).  Applying the operation
     * to a container applies it to all its contents recursively.
     * The checks are done in a non-UI thread.
     * 
     * @author David R. Cok
     */
    public static class RunSolver extends MenuActions {

    	@Override
    	public final void run(final IAction action) {
    		try {
    			final List<String> solvers = Activator.utils.getSolvers(action.getId());
    			List<IFile> files = Activator.utils.getSelectedFiles(selection,window,shell);
    			Activator.utils.text = null; // TODO - setting 'text' through side-effects is a bad design
        		if (files.isEmpty()) files = Activator.utils.resources(selection,window,shell); // sets Activator.utils.text also
        		if (files.isEmpty()) {
        			Activator.utils.showMessageInUI(shell,"SMT Run Solver",
        					"Failed to find a resource on which to run a solver (select one or more files or an editor)");
        			return;
        		}
    			Activator.utils.runJobs(solvers,files);
    		} catch (Exception e) {
    			Activator.utils.topLevelException(shell,"MenuActions.RunSolver",e);
    		}

    	}
    }

    /**
     * This class implements the action that clears
     * SMT markers.  It is performed entirely in the UI thread, with no
     * progress reporting.  Its ought to be fast.
     * 
     * @author David R. Cok
     */
    public static class DeleteMarkers extends MenuActions {
        @Override
        public final void run(final IAction action) {
            try {
                Activator.utils.deleteMarkersInSelection(selection,window,shell);
            } catch (Exception e) {
                Activator.utils.topLevelException(shell,"MenuActions.DeleteMarkers",e);
            }
        }
    }

    /** Shows the content of the SMT logic or theory whose name is selected */
    public static class ViewLogic extends MenuActions {
        @Override
        public final void run(final IAction action) {
        	Activator.utils.viewLogic(shell,selection);
        }
    }

    /** Does a get-value command on the selected text */
    public static class GetValue extends MenuActions {
        @Override
        public final void run(final IAction action) {
        	Activator.utils.getValue(shell,selection);
        }
    }

}
