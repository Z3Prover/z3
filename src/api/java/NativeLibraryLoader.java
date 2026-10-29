/**
 * Copyright (c) 2026 Microsoft Corporation
 * Licensed under the MIT license.
 */
package com.microsoft.z3;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Locale;

/** Loading policy shared by source builds and release packages. */
final class NativeLibraryLoader {
    private NativeLibraryLoader() { }

    // Called only from Native's class initializer, which the JVM serializes.
    static void load() {
        if (Boolean.parseBoolean(System.getProperty("z3.skipLibraryLoad"))) {
            return;
        }
        UnsatisfiedLinkError first;
        try {
            System.loadLibrary("z3java");
            return;
        } catch (UnsatisfiedLinkError ex) {
            first = ex;
        }
        UnsatisfiedLinkError second;
        try {
            System.loadLibrary("libz3java");
            return;
        } catch (UnsatisfiedLinkError ex) {
            second = ex;
        }

        String platform = platform();
        String stage = "finding bundled resources for " + platform;
        try {
            String core = libraryName(platform, "z3");
            String bridge = libraryName(platform, "z3java");
            // Check both before creating a directory or loading either library.
            try (InputStream coreInput = resource(platform, core);
                 InputStream bridgeInput = resource(platform, bridge)) {
                Path directory = Files.createTempDirectory("z3-native-");
                directory.toFile().deleteOnExit();
                stage = "extracting bundled resources for " + platform + " to " + directory;
                Path corePath = extract(directory, core, coreInput);
                Path bridgePath = extract(directory, bridge, bridgeInput);
                stage = "loading " + corePath;
                System.load(corePath.toAbsolutePath().toString());
                stage = "loading " + bridgePath;
                System.load(bridgePath.toAbsolutePath().toString());
            }
        } catch (IOException | UnsatisfiedLinkError | SecurityException ex) {
            UnsatisfiedLinkError error = new UnsatisfiedLinkError(
                "Failed to load Z3 native libraries for " + platform + " while " + stage
                + ". System attempts: z3java: " + first.getMessage()
                + "; libz3java: " + second.getMessage()
                + ". Bundled attempt: " + ex.getMessage()
                + ". Check the platform classifier, native runtime dependencies and writable java.io.tmpdir.");
            error.initCause(ex);
            error.addSuppressed(first);
            error.addSuppressed(second);
            throw error;
        }
    }

    private static InputStream resource(String platform, String name) throws IOException {
        String path = "/com/microsoft/z3/native/" + platform + "/" + name;
        InputStream input = NativeLibraryLoader.class.getResourceAsStream(path);
        if (input == null) {
            throw new FileNotFoundException("Missing bundled native resource " + path);
        }
        return input;
    }

    private static Path extract(Path directory, String name, InputStream input) throws IOException {
        Path target = directory.resolve(name);
        // The directory is unique; do not overwrite or use a shared extraction cache.
        target.toFile().deleteOnExit();
        Files.copy(input, target);
        return target;
    }

    private static String libraryName(String platform, String name) {
        if (platform.startsWith("win-")) {
            return name.equals("z3") ? "libz3.dll" : "z3java.dll";
        }
        return "lib" + name + (platform.startsWith("osx-") ? ".dylib" : ".so");
    }

    static String platform() {
        String os = System.getProperty("os.name", "").toLowerCase(Locale.ROOT);
        String arch = System.getProperty("os.arch", "").toLowerCase(Locale.ROOT);
        String osPart;
        if (os.startsWith("windows")) {
            osPart = "win";
        } else if (os.startsWith("mac") || os.equals("darwin")) {
            osPart = "osx";
        } else if (os.equals("linux")) {
            osPart = "linux";
        } else {
            osPart = "unsupported-os";
        }
        String archPart;
        if (arch.equals("amd64") || arch.equals("x86_64")) {
            archPart = "x64";
        } else if (arch.equals("aarch64") || arch.equals("arm64")) {
            archPart = "arm64";
        } else if (arch.equals("x86") || arch.matches("i[3-6]86")) {
            archPart = "x86";
        } else {
            archPart = "unsupported-arch";
        }
        return osPart + "-" + archPart;
    }
}
