package org.smtlib.test.bugs;

import java.io.File;
import java.util.concurrent.TimeUnit;
import java.util.jar.JarFile;
import java.util.jar.Manifest;

import org.junit.Assert;
import org.junit.Assume;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;

/**
 * Regression guard for <a href="https://github.com/smtlib/jSMTLIB/issues/14">issue #14</a>
 * ("No main manifest attribute in jSMTLIB.jar" -- a user reported that
 * {@code java -jar jSMTLIB-0.9.10.1.jar} failed with exactly that JVM launch error, unable
 * to run the tool as documented in the tutorial).
 * <p>
 * Not reproducible against the current build: {@code SMT/buildRelease} already writes
 * {@code Main-Class: org.smtlib.SMT} into the jar's manifest (and has since at least version
 * 0.5, well before the 0.9.10.1 the report was filed against), and {@code java -jar
 * SMT/jSMTLIB.jar --help} was confirmed by hand to run correctly rather than failing with
 * the reported error. This test exists purely as a regression guard against the manifest
 * generation ever breaking again, checking the built jar directly rather than spawning a
 * {@code java -jar} subprocess.
 * <p>
 * Skips (rather than failing) if the jar hasn't been built yet at the expected path --
 * this test verifies packaging, not compilation, and shouldn't block a normal source-only
 * test run.
 */
public class JarMainClassManifestTest {

    @Rule public Timeout timeout = new Timeout(1, TimeUnit.MINUTES);

    @Test
    public void builtJarDeclaresAMainClass() throws Exception {
        String path = System.getenv("SMT_JAR");
        File jar = path != null ? new File(path) : new File("../SMT/jSMTLIB.jar");
        Assume.assumeTrue("built jar not found at " + jar.getAbsolutePath() + " -- run buildRelease first",
                jar.isFile());

        try (JarFile jarFile = new JarFile(jar)) {
            Manifest manifest = jarFile.getManifest();
            Assert.assertNotNull("jar has no manifest at all: " + jar.getAbsolutePath(), manifest);
            String mainClass = manifest.getMainAttributes().getValue("Main-Class");
            Assert.assertEquals("org.smtlib.SMT", mainClass);
        }
    }
}
