/*
 * This file is part of the SMT plugin project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.plugin;

// FIXME - still needs review
// FIXME - need to be sure that the showMessage... methods are called in the UI context when they need to be

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;
import java.io.StringBufferInputStream;
import java.util.Date;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IStorage;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPersistableElement;
import org.eclipse.ui.IStorageEditorInput;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkingSet;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.texteditor.IDocumentProvider;
import org.eclipse.ui.texteditor.ITextEditor;
import org.smtlib.IResponse;
import org.smtlib.SMT;

/** This class holds utility values and methods to support the Eclipse plugin.
 * 
 * @author David Cok
 *
 */
public class Utils {
	
	final static String windowHeader = "SMT Plugin";

    /** This class is used to wrap arbitrary exceptions coming from the plug-in */
    public static class PluginException extends RuntimeException {
        /** Default serial version Symbol */
        private static final long serialVersionUID = 1L;

        /** Used to signal some unexpected error situation during plug-in processing. */
        public PluginException(String error) {
            super(error);
        }
        /** Used to signal some unexpected error situation during plug-in processing. */
        public PluginException(String error, /*@NonNull*/ java.lang.Exception e) {
            super(error,e);
        }
    }

    /** The Symbol of the marker, which must match that in the plugin file. */
    final public static  String SMT_MARKER_ID = Activator.PLUGIN_ID + ".SMTProblem";

    
    /** Run a specific solver on the given text, belonging to the given file (unsaved edits), in a computational job. 
     * If solver is null, then use the default from the options.  Call the method from the UI thread.
     */
    public void runSolver(String solver, IFile file, String text) {
    	if (solver == null) solver = Preferences.poptions.defaultSolver.getStringValue();
    	String exec = "";
    	// FIXME - there is a lot of code in common with the previous method
    	if (!solver.equals(org.smtlib.Utils.TEST_SOLVER)) try {// FIXME - make "test" a symbolic constant
    		exec = Preferences.getExec(solver);
    		if (exec == null) {
    			Activator.log.errorlog("SMT: INTERNAL ERROR: Could not find an executable option for " + solver,null);
    			return;
    		}
    		File execFile = new File(exec);
    		if (!execFile.exists()) {
    			Activator.utils.showMessageInUI(null,windowHeader,"The executable path for this solver does not appear to exist: " + solver + " \"" + exec + "\"");
    			return;
    		}
    		if (!execFile.canExecute()) {
    			Activator.utils.showMessageInUI(null,windowHeader,"The executable path for this solver does not appear to be executable: " + solver + " " + exec);
    			return;
    		}
    	} catch (java.lang.Exception e) {
			Activator.log.errorlog("SMT: Could not find the executable for the solver " + solver,e);
			return;
    	}
    	if (Activator.verbose) Activator.log.logln("ISolver = " + solver);
    	try {
			SMT smt = new SMT();
			smt.smtConfig = Activator.smtConfiguration.clone();
			smt.smtConfig.files = null;
			String[] cmd = text == null ? new String[]{ "-s", solver, "--exec", exec, file.getLocation().toString() }
										: new String[]{ "-s", solver, "--exec", exec, "--text", text, file.getLocation().toString() };
			deleteMarkers(file,null);
			boolean batch = false;
			if (batch) { // FIXME - get rid of launchJob now?
				launchJob(file.getLocation().toString(),smt,cmd,null);
			} else {
				interactiveJob(file.getLocation().toString(),smt,cmd,null);
			}
    	} catch (java.lang.Exception e) {
    		Activator.log.errorlog("SMT - Internal exception",e);
    	}
    }
    
    SMT saved_smt = null;
    
    /** Executes the given command (cmd) by the smt instance as a computational (non-UI) Job
     *
     * @param name name of the Job
     * @param smt the SMT instance in which to execute the commands
     * @param cmd the command to execute
     * @param shell the shell in which to display any UI messages
     */
    public void launchJob(String name, final SMT smt, final String[] cmd, /*@Nullable*/ final Shell shell) {
    	Job j = new Job("SMT Solver: " + name) {
    		@Override
    		public IStatus run(IProgressMonitor monitor) {
    			boolean c = false;
    			try {
    				smt.smtConfig.log.numErrors = 0;
    				int exitCode = smt.exec(cmd);
    				String timestring = "[" + new Date().toString() + "] ";
    				Activator.log.logln(timestring + "Completed " + cmd[1]
    						+ (exitCode == 0 ? "" : " (exitcode=" + exitCode +")")
    						+ (smt.smtConfig.log.numErrors == 0? "" : (" : " + smt.smtConfig.log.numErrors + " errors")) 
    						+ (smt.checkSatStatus == null ? "(no result)" : (" " + smt.smtConfig.defaultPrinter.toString(smt.checkSatStatus)))
    						);
    			} catch (PluginException e) {
    				showMessageInUI(shell,"SMT PluginException",e.getClass() + " - " + e.getMessage());
    				c = true;
    			}
    			return c ? Status.CANCEL_STATUS : Status.OK_STATUS;
    		}
    	};
    	j.setUser(true); // true = initiated by an end-user
    	j.schedule();
    }

    /** Executes the given command within the given SMT object,
     *  reporting results on the console and to the given shell;
     *  'name' is an informational name giving the file being working on;
     *  this method must be called in a computational thread.
     */
    public void interactiveJob(String name, SMT smt, String[] cmd, /*@Nullable*/ final Shell shell) {
    			try {
    				smt.smtConfig.log.numErrors = 0;
    				int exitCode = smt.exec(cmd);
    				String timestring = "[" + new Date().toString() + "] ";
    				Activator.log.logln(timestring + "Completed " + cmd[1] + " on " + name + " :"
    						+ (exitCode == 0 ? "" : " (exitcode=" + exitCode +")")
    						+ (smt.smtConfig.log.numErrors == 0? "" : (" : " + smt.smtConfig.log.numErrors + " errors")) 
    						+ (smt.checkSatStatus == null ? "(no result)" : (" " + smt.smtConfig.defaultPrinter.toString(smt.checkSatStatus)))
    						);
    			} catch (PluginException e) {
    				showMessageInUI(shell,"SMT PluginException",e.getClass() + " - " + e.getMessage());
    			}
				saved_smt = smt;
    }

    /** This runs a type-check only on the given text, in the UI thread. */
    public void runCheck(IFile file, String text) {
    	if (text.length() > 1000000) return; // FIXME - disable for large text
    	try {
			SMT smt = new SMT();
			// FIXME - would rather not clone the configuration and allocate
			// a new log and ProblemListener on each edit, but we might want
			// to have any configuration parameters in force as they change
			smt.smtConfig = Activator.smtConfiguration.clone();
			smt.smtConfig.log = new org.smtlib.Log(smt.smtConfig);
			smt.smtConfig.log.clearListeners(); // This removes the standard listener that would otherwise send log information to the console
		    smt.smtConfig.log.addListener(new ProblemListener());

			smt.smtConfig.files = null;
    		String[] cmd = new String[]{ "-s", org.smtlib.Utils.TEST_SOLVER, "--text", text, file.getFullPath().toString() };
    		deleteMarkers(file,null);
    		smt.exec(cmd);
    		//launchJob("interactive",smt,cmd,null);
    	} catch (java.lang.Exception e) {
    		Activator.log.errorlog("SMT - Internal exception",e);
    	}
    }


    /** Returns the ITextSelection corresponding to a selection, if there is one (null otherwise). */
    /*@Nullable*/
    static public ITextSelection getSelectedText(ISelection selection) {
        if (!selection.isEmpty() && selection instanceof ITextSelection) {
            return (ITextSelection)selection;
        } else {
            return null;
        }
    }
    

    /**
     * This method interprets the selection returning a List of IResources, and
     * ignoring things it does not know how to handle.  The selection is ignored
     * if it is not an IStructuredSelection (e.g. ITextSelections are ignored).
     * If the selection is empty and 'window'
     * is non-null, then the routine attempts to find a resource that corresponds
     * to the currently active editor.  The method expects to be called in the UI thread,
     * <UL>
     * <LI>IResource - added directly to list, whether a file or a container
     * <LI>working set - adds the elements of the working set if they can be
     *          converted (through IAdaptor) to an IResource
     * <LI>IJavaElement - adds the IResource that contains the element
     * <LI>otherwise - ignored
     * </UL>
     * 
     * @param selection  The selection to inspect
     * @param window  The window in which a selected editor exists
     * @param shell the shell to use in displaying information dialogs
     * @return A List of IResources found in the selection
     */
    public List<IResource> getSelectedResources(ISelection selection, 
            /*@Nullable*/ IWorkbenchWindow window, /*@Nullable*/ Shell shell) {
        List<IResource> list = new LinkedList<IResource>();
        if (!selection.isEmpty() && selection instanceof IStructuredSelection) {
            IStructuredSelection structuredSelection = (IStructuredSelection) selection;
            for (Iterator<?> iter = structuredSelection.iterator(); iter.hasNext(); ) {
                Object element = iter.next();
                if (element instanceof IResource) {
                    list.add((IResource)element);
                } else if (element instanceof IWorkingSet) {
                    for (IAdaptable a: ((IWorkingSet)element).getElements()) {
                        IResource r = (IResource) a.getAdapter(IResource.class);
                        if (r != null) list.add(r);
                    }
                    continue;
                } else if (element instanceof IAdaptable) {
                    IResource r = (IResource) ((IAdaptable)element).getAdapter(IResource.class);
                    if (r != null) list.add(r);
                }	
            }
        } else {
            // We had nothing selected
            // Look for the active editor instead
            try {
                IEditorPart p = window.getActivePage().getActiveEditor();
                IEditorInput e = p==null? null : p.getEditorInput();
                IResource o = e==null ? null : (IFile)e.getAdapter(IFile.class);
                if (o != null) {
                    list.add(o);  // This is an IFile
                } 
            } catch (PluginException ee) {
            	// These methods expect to be called in the UI thread.
                Activator.log.errorlog("PluginException when finding selected targets: " + ee,ee);
                showMessage(shell,"JML Plugin PluginException","PluginException occurred when finding selected targets: " + ee);
            }
        }
        return list;
    }

    /** Creates a list of all the selected files, or files that are in selected containers. */
    public List<IFile> getSelectedFiles(ISelection selection, 
            /*@Nullable*/ IWorkbenchWindow window, /*@Nullable*/ Shell shell) throws CoreException {
        List<IFile> list = new LinkedList<IFile>();
        if (!selection.isEmpty() && selection instanceof IStructuredSelection) {
            IStructuredSelection structuredSelection = (IStructuredSelection) selection;
            for (Iterator<?> iter = structuredSelection.iterator(); iter.hasNext(); ) {
                Object element = iter.next();
                if (element instanceof IResource) {
                	addFiles((IResource)element,list);
                } else if (element instanceof IWorkingSet) {
                    for (IAdaptable a: ((IWorkingSet)element).getElements()) {
                        IResource r = (IResource) a.getAdapter(IResource.class);
                        if (r != null) addFiles(r,list);
                    }
                } else if (element instanceof IAdaptable) {
                    IResource r = (IResource) ((IAdaptable)element).getAdapter(IResource.class);
                    if (r != null) addFiles(r,list);
                }
            }
        }
        return list;
    }
    
    // TODO - duplicated with Preferences.solverNames, and should be made configurable
	final String[] solverList = new String[]{ "simplify", "yices", "cvc", "z3_2_11", "z3_4_3"};
    
	/** Interprets the input string (the action id, as in action.getId()) to
	 * determine which solvers to run, returning their names in a list.
	 */
    public List<String> getSolvers(String id) {
    	List<String> solvers = new LinkedList<String>();
		int i = id.lastIndexOf('.');
		String name = id.substring(i+1);
    	if ("All".equals(name)) {
    		for (String s: solverList) solvers.add(s);
    	} else if ("default".equals(name)) {
        	name = Preferences.poptions.defaultSolver.getStringValue();
        	solvers.add(name);
    	} else {
    		solvers.add(name);
    	}
    	return solvers;
    }
    
    public void runJobs(final List<String> solvers, final List<IFile> files) {
		Job j = new Job("SMT Solving") {
			@Override
			public IStatus run(IProgressMonitor monitor) {
				IStatus status = Status.OK_STATUS;
				if (monitor != null) {
					monitor.beginTask("SMT solving", solvers.size() * (files.isEmpty() ? 1 : files.size()));
				}
        		for (IFile file: files) {
        			for (String solver: solvers) {
        				try {
        					if (monitor != null) monitor.subTask(solver + " on " + file.getName().substring(file.getName().lastIndexOf('/')+1));
        					runSolver(solver,file,text);
        				} catch (Exception e) {
        					Activator.log.errorlog("Exception while executing " + solver + " on " + file.getName() + ": " + e,e);
        				}
        				if (monitor != null) {
        					monitor.worked(1);
        					if (monitor.isCanceled()) {
        						status = Status.CANCEL_STATUS;
        						break;
        					}
        				}
        			}
        		}
				if (monitor != null) {
					monitor.done();
				}
				return status;
			}
		};
		j.setUser(true); // true = initiated by an end-user
		j.schedule();
    }
    
    /** Finds the selected editor; if it is a TextEditor, then if the editor is
     * dirty, runs the solver on the text; if the editor is not dirty, runs the
     * solver on the file. Returns true if successfully found file or text on which
     * to run; returns false otherwise.
     * 
     * This must be called in the UI thread; executes the check in a computational Job.
     * */
    public boolean runSolverOnSelectedEditor(String solver, List<IFile> files) throws CoreException {
		for (IFile r: files) runSolver(solver,r,text);
        return true;
    }
    
    String text;
    
    // FIXME - document
    public List<IFile> resources(ISelection selection, 
            /*@Nullable*/ IWorkbenchWindow window, /*@Nullable*/ Shell shell) throws CoreException {
    	IFile file = null;
		List<IFile> list = new LinkedList<IFile>();
		text = null;
    	try {
    		IWorkbenchPage page = window == null ? null : window.getActivePage();
    		IEditorPart p = page == null ? null : window.getActivePage().getActiveEditor();
    		IEditorInput e = p==null? null : p.getEditorInput();
    		file = e==null ? null : (IFile)e.getAdapter(IFile.class);
    		if (file == null) return null;
			if (p instanceof ITextEditor) {
				list.add(file);
				if (p.isDirty()) {
					IDocumentProvider doc = ((ITextEditor)p).getDocumentProvider();
					if (doc == null) return null;
					IDocument d = doc.getDocument(e);
					if (d == null) return null;
					text = d.get();
				}
			}
    	} catch (PluginException ee) {
    		// These calls expect to be in the UI thread
    		Activator.log.errorlog("PluginException when finding selected targets: " + ee,ee);
    		showMessage(shell,"JML Plugin PluginException","PluginException occurred when finding selected targets: " + ee);
    	}
    	return list;
    }
    
    /** This adds files in the given resource to the list; if the resource is a container, it 
     * adds the files that are in the container.
     */
    private void addFiles(IResource resource, List<IFile> list) throws CoreException {
    	if (resource instanceof IFile) {
    		if (resource.getName().toString().endsWith(org.smtlib.Utils.SUFFIX)) {
        		//Activator.log.log("ADDING " + resource.getLocation().toString());
    			list.add((IFile)resource);
    		}
    		return;
    	} else if (resource instanceof IContainer) {
    		for (IResource r: ((IContainer)resource).members()) {
    			addFiles(r,list);
    		}
    	}
    }


    // FIXME - should resource things be happening in another thread?
    /** Deletes all JML markers from the items selected, right within the UI thread,
     * without a progress dialog.  The resources for which markers are deleted are
     * those returned by Utils.getSelectedResources.   This should be called from
     * the UI thread.
     * @param selection the IStructuredSelection whose markers are to be deleted
     * @param window the current workbench window, or null (used in getSelectedResources)
     * @param shell the current Shell, or null for the default shell (for message dialogs)
     */
    public void deleteMarkersInSelection(ISelection selection, IWorkbenchWindow window, Shell shell) {
        List<IResource> list = getSelectedResources(selection,window,shell);
        //list.add(ResourcesPlugin.getWorkspace().getRoot()); // FIXME - temporarily here to clear out unrooted markers
        if (list.isEmpty()) {
            showMessage(shell,windowHeader,"Nothing appropriate to delete markers of");
            return;
        }
        deleteMarkers(list,shell);
        return;
    }


    /** This class is an implementation of the interfaces needed to provide input
     * to and launch editors in the workspace.
     * @author David R. Cok
     */
    public static class StringStorage implements IStorage, IStorageEditorInput {
        /** The initial content of the editor */
        private String content;
        /** The name of storage unit (e.g. the file name) */
        private String name;
        
        /** A constructor for a new storage unit */
        //@ assignable this.*;
        public StringStorage(String content, String name) { 
            this.content = content; 
            this.name = name; 
        }
        
        /** Interface method that returns the contents of the storage unit */
        //JAVA16 @Override
        public InputStream getContents() throws CoreException {
            return new StringBufferInputStream(content);
        }

        /** Returns the path to the underlying resource
         * @return null (not needed for readonly Strings)
         */
        //JAVA16 @Override
        public IPath getFullPath() {
            return null;
        }

        /** Returns the name of the storage object 
         * @return the name of the storage unit
         */
        //JAVA16 @Override
        public String getName() { return name; }

        /** Returns whether the storage object is read only
         * @return always true
         */
        //JAVA16 @Override
        public boolean isReadOnly() { return true; }

        /** Returns the object adapted to the given class.  It appears we can
         * ignore this and always return null.
         * @return null
         */
        //JAVA16 @Override
        public /*@Nullable*/ Object getAdapter(Class arg0) { return null; }

        /** Returns self
         * @return this object
         */
        //@ ensures \return == this;
        //JAVA16 @Override
        public IStorage getStorage() throws CoreException {
            return (IStorage)this;
        }
        
        /** Returns whether the underlying storage object exists
         * @return always true
         */
        //JAVA16 @Override
        public boolean exists() {
            return true;
        }
        
        /** Returns an ImageDescriptor, here ignored
         * @return always null
         */
        //JAVA16 @Override
        public /*@Nullable*/ ImageDescriptor getImageDescriptor() {
            return null;
        }
        
        /** Returns a corresponding Persistable object, here ignored
         * @return always null
         */
        //JAVA16 @Override
        public /*@Nullable*/ IPersistableElement getPersistable() {
            return null;
        }
        
        /** Return the text desired in a tool tip, here the name of the
         * storage unit
         */
        //@NonNull
        //JAVA16 @Override
        public String getToolTipText() {
            return name;
        }

    }

    /** Launches a read-only text editor with the given content and name
     * @param content the content of the editor
     * @param name the name (as in the title) of the editor
     */
    public void launchEditor(String content,String name) {
        try {
            IEditorInput editorInput = new StringStorage(content,name);
            IWorkbenchWindow window = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
            if (window == null) {
                showMessageInUI(null,"SMT PluginException","No window found for editor named " + name);
            	return;
            }
            IWorkbenchPage page = window.getActivePage();
            if (page == null) {
                showMessageInUI(null,"SMT PluginException","No active page found for editor named " + name);
            	return;
            }

            //            IEditorPart[] parts = page.getEditors();
            //            for (IEditorPart e: parts) Log.log("EDITOR " + e.getEditorSite().getId());
            page.openEditor(editorInput, "org.eclipse.ui.DefaultTextEditor");
        } catch (java.lang.Exception e) {
            showMessageInUI(null,"SMT PluginException",e.getMessage());
		}
    }

    /** Deletes the SMT_MARKER_ID markers in any of the objects in the List that are 
     * IResource objects; if the object is a container, markers are deleted for
     * any resources in the container; other kinds of objects are ignored.
     * Expects to be called from the UI thread.
     * @param <T> just the type of the list
     * @param list a list of objects whose markers are to be deleted
     * @param shell the current shell for dialogs (or null for default)
     */
    public <T extends IResource> void deleteMarkers(List<T> list, /*@Nullable*/ Shell shell) {
    	StringBuilder sb = new StringBuilder();
        for (T t: list) {
            IResource resource = (IResource)t;
            String s = deleteMarkers(resource,shell);
            if (s != null) { sb.append(s); sb.append("\n"); }
        }
        String ss = sb.toString();
        if (!ss.isEmpty()) Activator.utils.showMessage(shell,windowHeader,ss);
    }
    
    /** Deletes any SMT_MARKER_ID markers on the given resource, returns an error message, if any (else null);
     * expects to be called from the UI thread. */
    public /*@Nullable*/ String deleteMarkers(IResource resource, /*@Nullable*/ Shell shell) {
		try {
			try {
				if (Activator.verbose) Activator.log.logln("Deleting markers in " + resource.getName());
				resource.deleteMarkers(SMT_MARKER_ID, false,
						IResource.DEPTH_INFINITE);
			} catch (CoreException e) {
				String msg = "Failed to delete markers on "
						+ resource.getProject();
				Activator.log.errorlog(msg, e);
			}
		} catch (PluginException e) {
			Activator.log.errorlog("PluginException while deleting markers: " + e, e);
			return "PluginException while deleting markers "
							+ (resource != null ? "on " + resource.getName()
									: "");
		}
		return null;
	}
 
    /**
     * Displays a message in a dialog in the UI thread - this may
     * be called from other threads.
     * @param sh  The shell to use to display the dialog, or 
     *      a top-level shell if the parameter is null
     * @param title  The title of the dialog window
     * @param msg  The message to display in the dialog
     */
    public void showMessageInUI(/*@Nullable*/ Shell sh, 
            final String title, final String msg) {
        final Shell shell = sh;
        Display d = shell == null ? Display.getDefault() : shell.getDisplay();
        d.asyncExec(new Runnable() {
            public void run() {
                MessageDialog.openInformation(
                        shell,
                        title,
                        msg);
            }
        });
    }

    /**
     * Displays a message in a non-modal dialog in the UI thread - this may
     * be called from other threads.
     * @param sh  The shell to use to display the dialog, or 
     *      a top-level shell if the parameter is null
     * @param title  The title of the dialog window
     * @param msg  The message to display in the dialog
     */
    public void showMessageInUINM(/*@Nullable*/ Shell sh, 
            final String title, final String msg) {
        final Shell shell = sh;
        Display d = shell == null ? Display.getDefault() : shell.getDisplay();
        d.asyncExec(new Runnable() {
            public void run() {
                Dialog d = new NonModalDialog(
                        shell,
                        title,
                        msg);
                d.open();
            }
        });
    }

    // FIXME this does not seem to be working
    static public class NonModalDialog extends MessageDialog {
        final static String[] buttons = { "OK" };
        public NonModalDialog(Shell shell, String title, String message) {
            super(new Shell(),title,null,message,INFORMATION,buttons,0);
            setShellStyle(getShellStyle()|SWT.MODELESS);
            setBlockOnOpen(false);
        }
    }
    

    /**
     * Displays a message in a information dialog; must be called from the UI thread.
     * @param shell  Either the parent shell
     * @param title  A title for the dialog window
     * @param msg   The message to display in the dialog window
     */
    //@ requires msg != null;
    public void showMessage(/*@Nullable*/Shell shell, /*@Nullable*/String title, String msg) {
        MessageDialog.openInformation(
                shell,
                title,
                msg);
    }
    
    /** Shows an error dialog box for an exception; must be called from the UI thread */
    public void topLevelException(/*@Nullable*/Shell shell, String title, java.lang.Exception e) {
        //e.printStackTrace(sw); // TODO
        showMessage(shell,"SMT Top-level PluginException: " + title,
                e.toString());
    }
    
    /** Shows the logic or theory file of the selected text; error dialogs if can't find an appropriate file to show. */
    public void viewLogic(Shell shell, ISelection selection) {
    	String name = "";
    	String path = "";
		Reader r = null;
		InputStream stream = null;
    	try {
    		ITextSelection tsel = Utils.getSelectedText(selection);
    		if (tsel == null) {
    			Activator.utils.showMessage(shell,windowHeader,"Select the name of a logic or theory to show");
    			return;
    		}
    		name = tsel.getText();
    		if (name == null || name.length() == 0) {
    			Activator.utils.showMessage(shell,windowHeader,"Select the name of a logic or theory to show");
    			return;
    		}
    		String dir = Preferences.poptions.logics.getValue();
    		if (dir != null) dir = dir.trim();
    		
			if (dir == null || dir.isEmpty()) {
	    		try {
	    			stream = SMT.logicFinder.find(null,name,null);
	    			if (stream == null) {
	    				return;
	    			}
		    		r = new InputStreamReader(stream);
	    		} catch (IOException e) {
					showMessage(shell,"SMT View Logic","Could not read the definition file for " + name
							+ "\n" + e.getMessage());
					return;
	    		} catch (org.smtlib.Utils.SMTLIBException e) {
					showMessage(shell,"SMT View Logic","Could not read the definition file for " + name
							+ "\n" + e.errorResponse);
					return;
	    		}
			} else {
				String fname = dir + File.separator + name + org.smtlib.Utils.SUFFIX;
				if (Activator.verbose) Activator.log.logln("Trying to read logic file " + fname);
				File f = new File(fname);
				if (f.isFile()) r = new FileReader(f);
			}
			if (r == null) {
				showMessage(shell,"SMT View Logic","Could not find a definition file for " + name
						+ "\nTry setting the directory for logic definitions in the SMT preferences");
				return;
			}

    		char[] buf = new char[10000];
    		int p = 0;
    		int n = 0;
    		try {
    			while (p < buf.length) {
    				n = r.read(buf,p,buf.length-p);
    				if (n == -1) break; 
    				p += n;
    			}
    			Activator.utils.launchEditor(new String(buf,0,p),name);
    		} catch (IOException e) {
    			Activator.utils.showMessage(shell,windowHeader,"Failed to read logic file for " + name);
    			Activator.log.errorlog("Failed to read logic file for " + name,e);
    		}
    	} catch (FileNotFoundException e) {
    		Activator.utils.showMessage(shell,windowHeader,"Could not find logic or theory named " + name + "\n(" + path + ")");

    	} catch (PluginException e) {
    		Activator.utils.topLevelException(shell,windowHeader,e);
    	} finally {
    		try {
    			if (r != null) r.close();
    			if (stream != null) stream.close();
    		} catch (IOException e) {
    			Activator.log.errorlog("Failed to close reader for the logic file",e);
    		}
    	}
    }
    
    /** Performs a get-value command on the selected text. */
    public void getValue(Shell shell, ISelection selection) {
    	String text = "";
    	try {
    		ITextSelection tsel = Utils.getSelectedText(selection);
    		if (tsel == null) {
    			Activator.utils.showMessage(shell,windowHeader,"Select an expression whose value is wanted");
    			return;
    		}
    		text = tsel.getText();
    		if (text == null || text.length() == 0) {
    			Activator.utils.showMessage(shell,windowHeader,"Select an expression whose value is wanted");
    			return;
    		}
    		if (saved_smt == null) {
    			Activator.utils.showMessage(shell,windowHeader,"There is no current model");
    			return;
    		}
    		
    		int e = saved_smt.execCommand("(get-value (" + text + "))");
    		if (e != 0) {
    			Activator.utils.showMessage(shell,windowHeader,"The selected text is not a valid expression:\n" + text);
    		} else {
    			IResponse response = saved_smt.lastResponse;
    			Activator.utils.showMessage(shell,windowHeader,"Value: " + saved_smt.smtConfig.defaultPrinter.toString(response));
    		}
    	} catch (PluginException e) {
    		Activator.utils.topLevelException(shell,windowHeader,e);
    	}
    }

}
