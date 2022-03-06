package org.smtlib.plugin;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.DirectoryFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

/**
 * This class creates a Code Sonar Preferences page in Eclipse
 * This page hold data needed for CodeSonar and Eclipse interaction
 * 
 * @author sjohnson
 *
 */
public class SettingsPage extends FieldEditorPreferencePage implements
IWorkbenchPreferencePage {

    @Override
    public void init(IWorkbench workbench) {
        setPreferenceStore(Activator.getDefault().getPreferenceStore());
    }

    @Override
    protected void createFieldEditors() {
//        addField(new DirectoryFieldEditor("CODESONARPATH" ,
//                "&Code Sonar Path",
//                getFieldEditorParent()));
//        addField(new StringFieldEditor("HUB", "&Code Sonar Hub", 
//                getFieldEditorParent()));
//        addField(new StringFieldEditor("USERNAME", "&Code Sonar Username",
//                getFieldEditorParent()));
//        Composite fieldEditorParent = getFieldEditorParent();
//        password = new StringFieldEditor("PASSWORD", "&Code Sonar Password",
//                fieldEditorParent);
//        password.getTextControl(fieldEditorParent).setEchoChar('*');
//        addField(password);
//        addField(new BooleanFieldEditor("NO_SERVICES", "&No Services",
//                getFieldEditorParent()));
    }
}
