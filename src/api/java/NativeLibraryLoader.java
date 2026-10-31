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
import java.nio.file.Paths;
import java.nio.file.LinkOption;
import java.nio.file.DirectoryStream;
import java.nio.file.StandardCopyOption;
import java.nio.file.StandardOpenOption;
import java.nio.file.attribute.PosixFilePermissions;
import java.nio.file.attribute.PosixFilePermission;
import java.nio.channels.FileChannel;
import java.nio.channels.FileLock;
import java.nio.channels.OverlappingFileLockException;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.Locale;
import java.util.Set;
import java.util.TreeMap;

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
        Throwable cacheFailure = null;
        try {
            String core = libraryName(platform, "z3");
            String bridge = libraryName(platform, "z3java");
            try {
                if (!"false".equalsIgnoreCase(System.getProperty("z3.nativeCache"))) {
                    loadCached(platform, core, bridge);
                    return;
                }
            } catch (IOException | UnsatisfiedLinkError | SecurityException
                     | OverlappingFileLockException | java.nio.file.InvalidPathException
                     | UnsupportedOperationException ex) {
                // Restricted properties/filesystems and other ClassLoaders keep the private path.
                cacheFailure = ex;
            }
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
                + (cacheFailure == null ? "" : ". Cache attempt: " + cacheFailure)
                + ". Bundled attempt: " + ex.getMessage()
                + ". Check the platform classifier, native runtime dependencies and writable java.io.tmpdir.");
            error.initCause(ex);
            error.addSuppressed(first);
            error.addSuppressed(second);
            if (cacheFailure != null) {
                ex.addSuppressed(cacheFailure);
            }
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
        // Private fallback for disabled/unavailable caching or another ClassLoader.
        target.toFile().deleteOnExit();
        Files.copy(input, target);
        return target;
    }

    private static MessageDigest digest() {
        try {
            return MessageDigest.getInstance("SHA-256");
        } catch (NoSuchAlgorithmException ex) {
            throw new AssertionError("SHA-256 is required by Java", ex);
        }
    }

    private static String hash(InputStream input) throws IOException {
        MessageDigest digest = digest();
        byte[] buffer = new byte[65536];
        int count;
        while ((count = input.read(buffer)) != -1) {
            digest.update(buffer, 0, count);
        }
        StringBuilder text = new StringBuilder(64);
        for (byte value : digest.digest()) {
            text.append(Character.forDigit((value & 255) >>> 4, 16));
            text.append(Character.forDigit(value & 15, 16));
        }
        return text.toString();
    }

    private static boolean matches(Path path, String expected) throws IOException {
        if (!Files.isRegularFile(path, LinkOption.NOFOLLOW_LINKS)) {
            return false;
        }
        try (InputStream input = Files.newInputStream(path, LinkOption.NOFOLLOW_LINKS)) {
            return expected.equals(hash(input));
        }
    }

    private static void checkPath(Path path) throws IOException {
        for (Path part = path; part != null; part = part.getParent()) {
            if (Files.isSymbolicLink(part)) {
                throw new IOException("Symbolic link in native cache path: " + part);
            }
        }
    }

    private static Path cacheRoot() throws IOException {
        String configured = System.getProperty("z3.nativeCacheDir");
        String profile = System.getProperty("user.home");
        if (profile == null || profile.isEmpty()) {
            throw new IOException("No user.home for the native cache");
        }
        Path root = (configured == null
            ? Paths.get(profile, ".z3", "native")
            : Paths.get(configured)).toAbsolutePath().normalize();
        checkPath(root);
        if (root.getFileSystem().supportedFileAttributeViews().contains("posix")) {
            Files.createDirectories(root, PosixFilePermissions.asFileAttribute(
                PosixFilePermissions.fromString("rwx------")));
            Set<PosixFilePermission> permissions = Files.getPosixFilePermissions(root);
            if (permissions.contains(PosixFilePermission.GROUP_WRITE)
                    || permissions.contains(PosixFilePermission.OTHERS_WRITE)) {
                throw new IOException("Native cache is writable by other users: " + root);
            }
        } else {
            // On Windows inherit the user's profile ACL, including for .z3/native.
            Files.createDirectories(root);
        }
        checkPath(root);
        if (!Files.getOwner(root).equals(Files.getOwner(Paths.get(System.getProperty("user.home"))))) {
            throw new IOException("Native cache is not owned by the profile owner: " + root);
        }
        return root;
    }

    private static void loadCached(String platform, String core, String bridge) throws IOException {
        // Interned strings are shared across ClassLoaders. Keep one cache channel open
        // per JVM: on some systems closing another channel releases this JVM's locks.
        synchronized ("com.microsoft.z3.NativeLibraryLoader.cache") {
            loadCachedLocked(platform, core, bridge);
        }
    }

    private static void loadCachedLocked(String platform, String core, String bridge) throws IOException {
        String coreHash;
        String bridgeHash;
        // Derive identity from the actual bundled bytes, not the version or a mutable manifest.
        try (InputStream input = resource(platform, core)) {
            coreHash = hash(input);
        }
        try (InputStream input = resource(platform, bridge)) {
            bridgeHash = hash(input);
        }
        String identity;
        try (InputStream input = new java.io.ByteArrayInputStream(
                (coreHash + bridgeHash).getBytes(java.nio.charset.StandardCharsets.US_ASCII))) {
            identity = hash(input);
        }
        Path root = cacheRoot();
        // One process lock covers verification, publication, loading and eviction.
        // File locks overlap across ClassLoaders in one JVM; that case uses private copies.
        try (FileChannel channel = FileChannel.open(root.resolve(".lock"),
                StandardOpenOption.CREATE, StandardOpenOption.WRITE, LinkOption.NOFOLLOW_LINKS);
             FileLock lock = channel.lock()) {
            Path directory = root.resolve(platform + "-" + identity);
            checkPath(directory);
            if (!matches(directory.resolve(core), coreHash) || !matches(directory.resolve(bridge), bridgeHash)) {
                if (Files.exists(directory, LinkOption.NOFOLLOW_LINKS)) {
                    removeEntry(directory, core, bridge);
                }
                Path staging = Files.createTempDirectory(root, ".extract-");
                try {
                    try (InputStream input = resource(platform, core)) {
                        Files.copy(input, staging.resolve(core));
                    }
                    try (InputStream input = resource(platform, bridge)) {
                        Files.copy(input, staging.resolve(bridge));
                    }
                    if (!matches(staging.resolve(core), coreHash) || !matches(staging.resolve(bridge), bridgeHash)) {
                        throw new IOException("Bundled native resources changed during extraction");
                    }
                    // Publish only complete, verified pairs. If atomic moves are unavailable,
                    // preserve the old private-extraction behavior instead of a partial cache.
                    Files.move(staging, directory, StandardCopyOption.ATOMIC_MOVE);
                } finally {
                    if (Files.exists(staging, LinkOption.NOFOLLOW_LINKS)) {
                        removeEntry(staging, core, bridge);
                    }
                }
            }
            Files.setLastModifiedTime(directory, java.nio.file.attribute.FileTime.fromMillis(System.currentTimeMillis()));
            System.load(directory.resolve(core).toString());
            System.load(directory.resolve(bridge).toString());
            prune(root, directory, platform, core, bridge);
        }
    }

    // Never recursively remove a directory, follow links, or touch unknown files.
    private static void checkEntry(Path directory, String core, String bridge) throws IOException {
        if (!Files.isDirectory(directory, LinkOption.NOFOLLOW_LINKS)) {
            throw new IOException("Not a native cache directory: " + directory);
        }
        try (DirectoryStream<Path> files = Files.newDirectoryStream(directory)) {
            for (Path file : files) {
                String name = file.getFileName().toString();
                if ((!name.equals(core) && !name.equals(bridge))
                        || !Files.isRegularFile(file, LinkOption.NOFOLLOW_LINKS)) {
                    throw new IOException("Unexpected native cache entry: " + file);
                }
            }
        }
    }

    private static void removeEntry(Path directory, String core, String bridge) throws IOException {
        checkEntry(directory, core, bridge);
        Files.deleteIfExists(directory.resolve(core));
        Files.deleteIfExists(directory.resolve(bridge));
        Files.delete(directory);
    }

    private static void prune(Path root, Path current, String platform, String core, String bridge) {
        try {
            TreeMap<String, Path> previous = new TreeMap<String, Path>();
            long stale = System.currentTimeMillis() - 30L * 24 * 60 * 60 * 1000;
            try (DirectoryStream<Path> entries = Files.newDirectoryStream(root)) {
                for (Path entry : entries) {
                    String name = entry.getFileName().toString();
                    if (entry.equals(current) || !Files.isDirectory(entry, LinkOption.NOFOLLOW_LINKS)) {
                        continue;
                    }
                    long modified = Files.getLastModifiedTime(entry, LinkOption.NOFOLLOW_LINKS).toMillis();
                    if (name.matches(platform + "-[0-9a-f]{64}")) {
                        try { checkEntry(entry, core, bridge); } catch (IOException ignored) { continue; }
                        previous.put(String.format(Locale.ROOT, "%020d-%s", modified, name), entry);
                    } else if (name.startsWith(".extract-") && modified < stale) {
                        try { removeEntry(entry, core, bridge); } catch (IOException ignored) { }
                    }
                }
            }
            // Keep this pair and the two most recently used pairs for this platform.
            while (previous.size() > 2) {
                Path entry = previous.pollFirstEntry().getValue();
                try { removeEntry(entry, core, bridge); } catch (IOException ignored) { }
            }
        } catch (IOException | SecurityException ignored) {
            // A loaded DLL may remain locked on Windows. Cleanup cannot break a working load.
        }
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
