/*
 * This file is part of the SMT plugin project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.plugin;

import org.eclipse.core.runtime.Platform;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;
import org.smtlib.SMT;

import java.io.*;
import java.net.URL;

import org.smtlib.IPos;
/**
 * The activator class controls the plug-in life cycle
 */
public class Activator extends AbstractUIPlugin {

	/** The plug-in Symbol - must match what is in plugin.xml */
	public static final String PLUGIN_ID = "org.smtlib.plugin.SMTPlugin"; //$NON-NLS-1$

	/** The shared (singleton) instance of the plugin, initialized on construction */
	/*@NonNull*/
	private static Activator plugin;
	
	/** The shared instance of the plug-in utils methods */
	/*@NonNull*/
	public static Utils utils;
	
	/** The shared instance of a plug-in Log for the whole plug-in */
	/*@NonNull*/
	public static Log log;
	
	/** A shared instance of the SMT configuration */
	public static org.smtlib.SMT.Configuration smtConfiguration = null;//new org.smtlib.SMT.Configuration();
	
	/** The option to print out verbose diagnostic information for the plug-in*/
	public static boolean verbose = false;
	
	/**
	 * The constructor
	 */
	public Activator() {
		plugin = this;
	    utils = new Utils();
	    log = new Log();
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
	 */
	@Override
	public void start(BundleContext context) throws Exception {
		super.start(context);
		// Initialize the configuration
	    smtConfiguration = Preferences.extractOptions(null);
		// Creates a new console and sets it to hear plugin log messages
	    ConsoleLogger console = new ConsoleLogger("SMT Console");
	    Activator.log.setListener(console);
	    // Set the console to hear all the SMT application messages as well
	    smtConfiguration.log.clearListeners(); // This removes the standard listener that would otherwise send log information to the console
	    smtConfiguration.log.addListener(console);
	    // Sets a problem listener to hear application error log messages, so they can become problem markers
	    smtConfiguration.log.addListener(new ProblemListener());

	    // Listens for Preference page changes and updates the SMT Configuration accordingly
	    AbstractPreference.addListener(new AbstractPreference.Listener() { 
	    	@Override
	    	public void run() { 
	    		// The following line also extracts and sets Activator.verbose
	    		smtConfiguration = Preferences.extractOptions(smtConfiguration); 
	    	}
	    });
	    
	    /** The logic file finder for the plug-in looks for a logic file with the given name:
	     * (a) if no logic directory path is set, then it looks within the SMT plugin itself for any built-in files
	     * (b) if a logic directory path is set, it looks there.
	     * <P>
	     * I would have thought that the non-plugin functionality of (a) exporting
	     * logics directory and (b) finding the logic files on the classpath
	     * would work - but I have not been able to make that function. Thus
	     * we need one mechanism for finding resources inside a plug-in (this 
	     * one - with reference to the plug-in bundle) and another mechanism
	     * (looking on the classpath) when one is not inside a plug-in.
	     */
	    SMT.logicFinder = new SMT.ILogicFinder() {
	    	@Override
	    	public InputStream find(SMT.Configuration smtConfig, String name, IPos pos) throws java.io.IOException {
	    		if (smtConfig == null || smtConfig.logicPath == null || smtConfig.logicPath.trim().length() ==0) {
	    			// Note that the following logic depends on the fact that the 
	    			// logic definition files (e.g., QF_UF.smt2) reside at the
	    			// root of the plugin that holds the SMT application (not
	    			// this plugin which is for the UI). They get there because
	    			// they are copied into the bin directory as part of the
	    			// build. The application depends on them being on the
	    			// classpath.
	    			URL url = Platform.getBundle(org.smtlib.Utils.PLUGIN_ID).getResource(name + org.smtlib.Utils.SUFFIX);
	    			if (Activator.verbose) Activator.log.logln("Finding logic file " + name + " " + url);
	    			if (url != null) {
	    				InputStream stream =  url.openStream();
	    				if (stream != null) return stream;
	    				if (smtConfig==null) Activator.utils.showMessageInUI(null,"SMT: ViewLogic",
	    						"No logic file found for " + name + " as " + url);
	    				else smtConfig.log.logError(smtConfig.responseFactory.error("No logic file found for " + name + " as " + url, pos));
	    			} else {
	    				if (smtConfig==null) Activator.utils.showMessageInUI(null,"SMT: ViewLogic",
	    						"No logic file found for " + name);
	    				else smtConfig.log.logError(smtConfig.responseFactory.error("No logic file found for " + name, pos));
	    			}
	    			return null;
	    		} else {
	    			String fname = smtConfig.logicPath + File.separator + name + org.smtlib.Utils.SUFFIX;
	    			File f = new File(fname);
	    			if (Activator.verbose) Activator.log.logln("Finding logic file " + name + " " + fname);
	    			if (!f.isFile()) {
	    				smtConfig.log.logError(smtConfig.responseFactory.error("No logic file found for " + name + " as " + f.getPath(), pos));
	    				return null;
	    			}
	    			return new FileInputStream(f);
	    		}
	    	}
	    };
	    
	    if (verbose) Activator.log.logln("SMT UI plugin started");
	    
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
	 */
	@Override
	public void stop(BundleContext context) throws Exception {
		super.stop(context);
	}

	/**
	 * Returns the shared instance
	 *
	 * @return the shared instance
	 */
	/*@NonNull*//*@Pure*/
	public static Activator getDefault() {
		return plugin;
	}

}
