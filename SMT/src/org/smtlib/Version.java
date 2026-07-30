package org.smtlib;

import java.util.ResourceBundle;

/** Provides the release version string for jSMTLIB, read from the {@code org.smtlib.resources.version}
 *  resource bundle.
 */
public class Version {
    private static final String versionRBName = "org.smtlib.resources.version";
    private static ResourceBundle versionRB;

    /** Returns the release version string for this build of jSMTLIB. */
    public static String version() throws RuntimeException {
    	String key = "release";
    	if (versionRB == null) {
    		versionRB = ResourceBundle.getBundle(versionRBName);
    	}
    	return versionRB.getString(key);
    }

}
