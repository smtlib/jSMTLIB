package org.smtlib.test;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.Assume;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.junit.runner.RunWith;
import org.junit.runners.ParameterizedWithNames;
import org.junit.runners.Parameterized.Parameters;

@RunWith(ParameterizedWithNames.class)
public class ScriptTests {

    @Rule public Timeout timeout = new Timeout(2, TimeUnit.MINUTES);

    private static final String PLATFORM;
    private static final String PLATFORM_ARCH;

    static {
        String os = System.getProperty("os.name").toLowerCase();
        String platform;
        if (os.contains("win"))      platform = "windows";
        else if (os.contains("mac")) platform = "macos";
        else                         platform = "linux";
        PLATFORM = platform;

        String arch = System.getProperty("os.arch").toLowerCase();
        String archTag = (arch.contains("aarch64") || arch.contains("arm64")) ? "arm64" : "x64";
        PLATFORM_ARCH = platform + "-" + archTag;
    }

    @Parameters
    public static Collection<String[]> datax() {
        Collection<String[]> data = new ArrayList<>();
        File scriptsDir = findScriptsFolder();
        File[] scrFiles = scriptsDir.listFiles(f -> f.getName().endsWith(".scr"));
        if (scrFiles != null) {
            Arrays.sort(scrFiles);
            for (File f : scrFiles) {
                String name = f.getName().replaceAll("\\.scr$", "");
                data.add(new String[]{name, f.getAbsolutePath()});
            }
        }
        return data;
    }

    private static File findScriptsFolder() {
        try {
            String resource = ScriptTests.class.getClassLoader().getResource("err_array.tst").getPath();
            return new File(new File(resource).getParentFile().getParentFile(), "scripts");
        } catch (Exception e) {
            return new File("scripts");
        }
    }

    private final File scrFile;

    public ScriptTests(String name, String scrFilePath) {
        this.scrFile = new File(scrFilePath);
    }

    @Test
    public void checkScript() throws Exception {
        checkSkip();

        File smtTestsDir = scrFile.getParentFile().getParentFile();
        ProcessBuilder pb = new ProcessBuilder("bash", "runscript", scrFile.getAbsolutePath());
        pb.directory(smtTestsDir);
        pb.redirectErrorStream(true);
        Process proc = pb.start();
        String output = new String(proc.getInputStream().readAllBytes());
        boolean finished = proc.waitFor(2, TimeUnit.MINUTES);

        if (!finished) {
            proc.destroyForcibly();
            Assert.fail("Script test timed out: " + scrFile.getName());
        }

        int exitCode = proc.exitValue();
        if (exitCode == 77) {
            String reason = findLine(output, "SKIP:");
            Assume.assumeTrue(reason != null ? reason : "Skipped", false);
        }
        if (exitCode != 0) {
            Assert.fail("Script FAILED: " + scrFile.getName() + "\n" + output);
        }
    }

    private void checkSkip() {
        String base = scrFile.getAbsolutePath();
        for (String suffix : new String[]{
                ".skip." + PLATFORM_ARCH, ".skip." + PLATFORM, ".skip"}) {
            File skip = new File(base + suffix);
            if (skip.exists()) {
                Assume.assumeTrue("Skip: " + readFirstLine(skip), false);
            }
        }
    }

    private String findLine(String text, String prefix) {
        for (String line : text.split("\n")) {
            if (line.startsWith(prefix)) return line;
        }
        return null;
    }

    private static String readFirstLine(File f) {
        try (BufferedReader r = new BufferedReader(new FileReader(f))) {
            String line = r.readLine();
            return line != null ? line : "";
        } catch (IOException e) {
            return f.getName();
        }
    }
}
