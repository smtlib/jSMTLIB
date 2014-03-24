package org.smtlib;

import java.util.MissingResourceException;
import java.util.ResourceBundle;


public class Version {
	public static final String VERSION_ID = "jSMTLIB version " + version();
	
    private static final String versionRBName = "org.smtlib.resources.version";
    private static ResourceBundle versionRB;

    public static String version() throws RuntimeException {
    	String key = "release";
        if (versionRB == null) {
            //try {
                versionRB = ResourceBundle.getBundle(versionRBName);
//            } catch (MissingResourceException e) {
//                return Log.getLocalizedString("version.not.available");
//            }
        }
//        try {
            return versionRB.getString(key);
//        }
//        catch (MissingResourceException e) {
//            return Log.getLocalizedString("version.not.available");
//        }
    }

}
