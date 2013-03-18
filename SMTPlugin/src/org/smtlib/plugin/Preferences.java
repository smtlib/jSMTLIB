/*
 * This file is part of the SMT plug-in project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.plugin;

// FIXME implement logic, out, diag, port, relax -- check all options

import java.io.File;
import java.util.Enumeration;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CTabFolder;
import org.eclipse.swt.custom.CTabItem;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.osgi.framework.Bundle;
import org.smtlib.SMT.Configuration;

/**
 * @author David Cok
 * 
 * This class implements the preference page for the plugin.
 * To add a new Preference:
 *  - add a String to POptions -- this is the key used in the preference database
 *  - add an AbstractPreference for that key to POptions - this specifies the kind of preference (Boolean, String, Choice, ...)
 *  - add a PreferenceWidget linked to the AbstractPreference to one of the PreferenceWidget arrays (e.g. options, pluginOptions)
 *  - if you create a new array, alter createContents, performOK, performDefaults
 */
public class Preferences extends org.eclipse.jface.preference.PreferencePage 
implements IWorkbenchPreferencePage {

	/* (non-Javadoc)
	 * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
	 */
	// FIXME _ what might go in here?
	public void init(IWorkbench workbench) {
	}

	/** This class defines all the items that have a persistent
	 * presence in the Preferences store. */
	static public class POptions {
		/** The prefix to be put on each key. */
		final static public String prefix = "org.smtlib.plugin.";

		/** The preference store key for the verbose option. */
		final static public String verbosePluginKey = prefix + "verbosePlugin";

		/** The preference store key for the verbose SMT app option. */
		final static public String verboseKey = prefix + "verbose";

		/** The preference store key for the verbose SMT solver option. */
		final static public String solverVerbosityKey = prefix + "solverVerbosity";

		/** The preference store key for the print-success option. */
		final static public String printSuccessKey = prefix + "printSuccess";

		/** The preference store key for the abort-on-error option. */
		final static public String abortKey = prefix + "abort";

		/** The preference store key for the print-success option. */
		final static public String relaxKey = prefix + "relax";

		/** The preference store key for the print-success option. */
		final static public String echoKey = prefix + "echo";

		/** The preference store key for the logic option. */
		final static public String logicKey = prefix + "logic";

		/** The preference store key for the logics option. */
		final static public String logicsKey = prefix + "logics";

		/** The preference store key for the default solver choice option. */
		final static public String defaultSolverKey = prefix + "defaultSolver";

		/** The preference store key for option storing the path to the given solver's executable. */
		final static public String execKey(String solver) {
			return prefix + "execKey_" + solver;
		}
		// The various option objects
		
		public AbstractPreference.BooleanOption verbosePlugin = 
			new AbstractPreference.BooleanOption(verbosePluginKey, false, "verbose plug-in?", "If true, progress and debugging information from the plug-in is printed.");

		public AbstractPreference.BooleanOption verbose = 
			new AbstractPreference.BooleanOption(verboseKey, false, "verbose SMT app?", "If true, diagnostic information from the SMT app is printed.");

		public AbstractPreference.IntOption solverVerbosity = 
			new AbstractPreference.IntOption(solverVerbosityKey, 0, "SMT solver verbosity", "Verbosity level of the SMT solver, 0 for quiet");

		public AbstractPreference.BooleanOption printSuccess = 
			new AbstractPreference.BooleanOption(printSuccessKey, true, "print success?", "If true, all command results are printed; if false, all except success are printed.");

		public AbstractPreference.BooleanOption abort = 
			new AbstractPreference.BooleanOption(abortKey, false, "abort on error?", "If true, an error aborts further processing.");

		public AbstractPreference.BooleanOption echo = 
			new AbstractPreference.BooleanOption(echoKey, false, "echo batch commands?", "If true, batch commands are echoed to the output as they are executed");
		public AbstractPreference.BooleanOption relax = 
			new AbstractPreference.BooleanOption(relaxKey, false, "relax conformity?", "If true, some not-strictlyu-SMT-LIB enahancements are allowed; if false, SMT-LIB is strictly enforced.");

		public AbstractPreference.StringOption logics = 
			new AbstractPreference.StringOption(logicsKey,"","Directory containing logic files (if empty, built-in logic files are used)","Directory that contains the files defining SMT-LIB logics and theories");

		public String[] logicNames = new String[]{};
		{
			String logicsDir = logics.getValue();
			List<String> logicList = new LinkedList<String>();
			if (logicsDir.trim().length() != 0) {
				File dir = new File(logicsDir);
				logicList.add("");
				if (dir.isDirectory()) {
					for (String f : dir.list()) {
						if (f.endsWith(org.smtlib.Utils.SUFFIX)) {
							f = f.substring(0,f.length() - org.smtlib.Utils.SUFFIX.length());
							if (f.charAt(1) <= 'Z') {
								logicList.add(f);
							}
						}
					}
				}
			} else { // FIXME - unify this with findLogic in Activator
				Bundle b = Platform.getBundle(org.smtlib.Utils.PLUGIN_ID);
				@SuppressWarnings("unchecked")
				Enumeration<String> e = (Enumeration<String>)b.getEntryPaths("logics/");
				while (e.hasMoreElements()) {
					String p = e.nextElement();
					int n = 1 + p.indexOf('/');
					int nn = p.indexOf('.');
					if (nn != -1) logicList.add(p.substring(n,nn));
				}
			}
			logicNames = logicList.toArray(logicNames);
		}
		
		// FIXME - This gets set dynamically when the plugin first starts; changes in the logic path are not
		// changed until the plug-in restarts
		
		public AbstractPreference.ChoiceOption logic = dynamicLogicList(logicKey, logics.getValue());

		/** Names of defaultSolver to include; test must be first */
		public static final String[] solverNames = new String[]{org.smtlib.Utils.TEST_SOLVER,"simplify","yices","cvc","z3_2_11","z3_4_3"};
		
		public AbstractPreference.ChoiceOption defaultSolver = 
			new AbstractPreference.ChoiceOption(defaultSolverKey,
					solverNames,
					0,
					"Default solver to use",
			"The default solver to use in response to menu commands");

		public List<AbstractPreference.StringOption> execOptions = new LinkedList<AbstractPreference.StringOption>();
		
		public POptions() {
			// Skip solverNames[0] ("test")
			for (int i = 1; i<solverNames.length; ++i) {
				String name = solverNames[i];
				execOptions.add(new AbstractPreference.StringOption(execKey(name),"",name + " executable","File system path to the executable for the "+name+" solver"));
			}
		}

	}
	
	public static AbstractPreference.ChoiceOption dynamicLogicList(String logicKey, String logicsDir) {
		String[] logicNames = new String[]{};
		File dir = new File(logicsDir);
		List<String> logicList = new LinkedList<String>();
		logicList.add("");
		if (dir.isDirectory()) {
			for (String f : dir.list()) {
				if (f.endsWith(org.smtlib.Utils.SUFFIX)) {
					f = f.substring(0,f.length() - org.smtlib.Utils.SUFFIX.length());
					if (f.charAt(1) <= 'Z') {
						logicList.add(f);
					}
				}
			}
		}
		logicNames = logicList.toArray(logicNames);
		
		return
			new AbstractPreference.ChoiceOption(logicKey, logicNames, 0, "implicit logic:", "If set, the logic to set implicitly for each SMT execution.");

	}
	
	/** An instance of the object that holds all of the preference store items being used. */
	static POptions poptions = new POptions();

	/** This method fills in a Configuration structure whose values are set from
	 * the current preference store settings (which should match those in the UI).
	 * We use the preference store instead of the UI widgets so that this method
	 * works even if the preference page has not yet been generated.  If the 
	 * argument is null, a new Configuration structure is allocated; otherwise the
	 * fields of the argument are filled in.  The argument or newly allocated 
	 * object is returned.
	 * @param options if not null, the structure to fill in
	 * @return An Configuration structure initialized to the current preference store settings.
	 */
	static public Configuration extractOptions(Configuration smtConfig) {
		if (smtConfig == null) {
			smtConfig = new Configuration();
		}
		Activator.verbose = poptions.verbosePlugin.getValue();
		smtConfig.verbose = poptions.verbose.getValue() ? 1 : 0;
		smtConfig.solverVerbosity = poptions.solverVerbosity.getValue();
		smtConfig.nosuccess = !poptions.printSuccess.getValue();
		smtConfig.abort = poptions.abort.getValue();
		smtConfig.echo = poptions.echo.getValue();
		smtConfig.relax = poptions.relax.getValue();
		
		smtConfig.logic = null;
//		if (poptions.logic.getIndexValue() == 0) options.logic = null; // FIXME - implement implicit logic?
//		else options.logic = poptions.logic.getStringValue();
		
		smtConfig.solvername = poptions.defaultSolver.getStringValue();
		smtConfig.logicPath = poptions.logics.getValue();
		if (smtConfig.logicPath.trim().isEmpty()) smtConfig.logicPath = null;
		if (Activator.verbose) Activator.log.logln("Extracted options");
		return smtConfig;
	}


	static PreferenceWidget.ChoiceWidget logicChoiceWidget;
	static PreferenceWidget.DirectoryWidget logicPathWidget;
	/**
	 * An array of the SMT option widgets.
	 */
	static private PreferenceWidget[] options = {
		new PreferenceWidget.BooleanWidget(poptions.verbose),
		new PreferenceWidget.IntWidget(poptions.solverVerbosity, new String[]{"0","1","2","3","4","5","6","7","8","9"}),
		new PreferenceWidget.BooleanWidget(poptions.printSuccess),
		new PreferenceWidget.BooleanWidget(poptions.abort),
		new PreferenceWidget.BooleanWidget(poptions.echo),
		new PreferenceWidget.BooleanWidget(poptions.relax),
		new PreferenceWidget.ChoiceWidget(poptions.defaultSolver),
		logicChoiceWidget=new PreferenceWidget.ChoiceWidget(poptions.logic),
		logicPathWidget=new PreferenceWidget.DirectoryWidget(poptions.logics),
	};
	
	static private PreferenceWidget[] solverConfig = new PreferenceWidget[poptions.execOptions.size()];

	
	static {
		List<PreferenceWidget> list = new LinkedList<PreferenceWidget>();
		for (AbstractPreference.StringOption s: poptions.execOptions) {
			list.add(new PreferenceWidget.FileWidget(s));
		}
		solverConfig = list.toArray(solverConfig);
		// FIXME _ have not been able to get this to work
//		logicPathWidget.addModifyListener( new ModifyListener() {
//			public void modifyText(ModifyEvent e) {
//				if (logicPathWidget != null && logicChoiceWidget != null && poptions != null && poptions.logic != null) {
//				poptions.logic = dynamicLogicList(POptions.logicKey,logicPathWidget.value());
//				logicChoiceWidget.setChoices(poptions.logic.choices());
//				}
//			}
//		});
	}
	
	static final public String getExec(String solver) throws java.lang.Exception {
		String key = POptions.execKey(solver);
		for (AbstractPreference.StringOption p: poptions.execOptions) {
			if (p.key().equals(key)) return p.getValue();
		}
		return null;
	}

	/**
	 * An array of widgets for plugin options.
	 */
	static final private PreferenceWidget[] pluginOptions = {
		new PreferenceWidget.BooleanWidget(poptions.verbosePlugin),
	};
	
//	static final private PreferenceWidget[] execOptions = new PreferenceWidget[poptions.execOptions.size()];
//	{
//		int i = 0;;
//		for (AbstractPreference.StringOption p: poptions.execOptions) {
//			execOptions[i++] = new PreferenceWidget.StringWidget(p);
//		}
//	}

	/**
	 * Creates the property page controls and initializes them.
	 * 
	 * @param parent The UI object into which to insert the controls
	 * @return The new control that is added to 'parent'
	 */
	protected Control createContents(Composite parent) {

		// Creates the contents of the property page view.

		CTabFolder tf = new CTabFolder(parent, SWT.TOP|SWT.MULTI|SWT.FLAT);
		CTabItem mainTab = new CTabItem(tf,SWT.NONE,0);
		mainTab.setText("General");
		CTabItem solverTab = new CTabItem(tf,SWT.NONE,1);
		solverTab.setText("Solvers");
		Composite generalComposite = new Widgets.VComposite(tf);
		mainTab.setControl(generalComposite);
		Composite solverComposite = new Widgets.VComposite(tf);
		solverTab.setControl(solverComposite);
		addWidgets(solverConfig,solverComposite);

		Composite composite0 = generalComposite;
		new Label(composite0, SWT.CENTER).setText("SMT version: " + org.smtlib.Version.VERSION_ID);
		new Label(composite0, SWT.CENTER)
		.setText("These choices are workspace options that apply to every SMT-LIB project.");

		new Widgets.LabeledSeparator(composite0, "Configuration relating to the plugin");
		addWidgets(pluginOptions, composite0);
		new Widgets.LabeledSeparator(composite0, "Configuration relating to SMT");
		addWidgets(options, composite0);

		tf.showItem(mainTab);
		tf.setSelection(mainTab);
		return composite0;

	}

//	/**
//	 * Constructs the view of the property page by adding different features like
//	 * labels, and setting the layout. Just a helper to <code>createContents()
//	 * </code>.
//	 * 
//	 * @param parent The parent composite to which the controls are added
//	 * @return The resulting control that defined the looking of the property page
//	 */
//	private Control addControl(Composite parent) {
//		Composite composite0 = new Widgets.VComposite(parent);
//
//		new Label(composite0, SWT.CENTER).setText("SMT version: " + org.smtlib.Utils.SW_VERSION);
//		new Label(composite0, SWT.CENTER)
//		.setText("These options are workspace options that apply to every SMT-LIB project.");
//		//  Composite composite0 = new Widgets.HComposite(composite0a, 2);
//		//  Composite composite1 = new Widgets.VComposite(composite0);
//		//  Composite composite2a = new Widgets.VComposite(composite0);
//		//  Composite composite2 = new Widgets.HComposite(composite2a, 2);
//		//  Composite composite3 = new Widgets.VComposite(composite2);
//		//  Composite composite4 = new Widgets.VComposite(composite2);
//
//		//    new Widgets.LabeledSeparator(composite0, "Configuration relating to Eclipse");
//		//    addWidgets(eclipseOptions, composite0);
//		//    new Widgets.LabeledSeparator(composite0, "Configuration relating to Java");
//		//    addWidgets(javaOptions, composite0);
//		new Widgets.LabeledSeparator(composite0, "Configuration relating to the plugin");
//		addWidgets(pluginOptions, composite0);
//		new Widgets.LabeledSeparator(composite0, "Configuration relating to SMT");
//		addWidgets(options, composite0);
//		//    new Widgets.LabeledSeparator(composite0, "Configuration for debugging");
//		//    addWidgets(debugOptions, composite0);
//
//		return composite0;
//	}

	/**
	 * @see org.eclipse.jface.preference.IPreferencePage#performOk()
	 */
	public boolean performOk() {
		// When OK is pressed, set all the options selected.
		setOptionValue(pluginOptions);
		setOptionValue(options);
		setOptionValue(solverConfig);

		if (false) {
			// FIXME _ hard coded array positions is fragile
			poptions.logic = dynamicLogicList(POptions.logicKey,logicPathWidget.value());
			logicChoiceWidget.setChoices(poptions.logic.choices());
		}
		AbstractPreference.notifyListeners();
		return true;
	}

	public void performDefaults() {
		// When OK is pressed, set all the options selected.    
		setDefaults(pluginOptions);
		setDefaults(options);
		setDefaults(solverConfig);
	}

	/** Calls setDefault for each widget in the list
	 * 
	 * @param ws an array of widgets to be processed
	 */
	//@ requires ws != null;
	//@ requires \nonnullelements(ws);
	public void setDefaults(PreferenceWidget[] ws) {
		for (int i = 0; i<ws.length; ++i) {
			ws[i].setDefault();
		}
	}

	/**
	 * Calls 'setOptionValue' on all the items in the array,
	 * so that the stored options are set from the UI
	 * @param ws An array of PreferenceWidget items 
	 */
	//@ requires ws != null;
	//@ requires \nonnullelements(ws);
	public void setOptionValue(PreferenceWidget[] ws) {
		for (int i=0; i<ws.length; ++i) {
			ws[i].setOptionValue();
		}
	}

	// Inherited method
	protected IPreferenceStore doGetPreferenceStore() {
		return Activator.getDefault().getPreferenceStore();
	}

	// Default implementation does a performOk()
	//public void performApply();

	// Default implementation does nothing and returns true
	//public boolean performCancel();

	/* (non-Javadoc)
	 * @see org.eclipse.jface.dialogs.IDialogPage#performHelp()
	 */
	public void performHelp() {}

	/**
	 * Calls 'addWidget' on all the items in the list of PreferenceWidgets, in
	 * order to add them to the given composite.
	 * @param ws    The list of widgets to be added
	 * @param composite The composite to add them to
	 */
	//@ requires ws != null && composite != null;
	//@ requires \nonnullelements(ws);
	public void addWidgets(PreferenceWidget[] ws, Composite composite) {
		addWidgets(ws,0,ws.length,composite);
	}

	/**
	 * Calls 'addWidget' on some of the items in the list of PreferenceWidgets, in
	 * order to add them to the given composite.
	 * @param ws    The list of widgets to be added
	 * @param offset The index in the array at which to begin
	 * @param num The number of widgets to add
	 * @param composite The composite to add them to
	 */
	//@ requires ws != null && composite != null;
	//@ requires offset >= 0 && offset < ws.length;
	//@ requires num >= 0 && offset + num < ws.length;
	//@ requires \nonnullelements(ws);
	public void addWidgets(PreferenceWidget[] ws, int offset, int num, Composite composite) {
		for (int i=0; i<num; ++i) {
			ws[offset+i].addWidget(composite);
		}
	}
}
