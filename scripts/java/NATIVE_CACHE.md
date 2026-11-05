# Bundled native library cache

`NativeLibraryLoader` still tries the installed JNI library first. When that
fails, platform and `all` JARs use a cache at `${user.home}/.z3/native` by default.
The API-only JAR still requires an external native installation.

- `-Dz3.nativeCacheDir=/absolute/user-owned/path` selects another cache root.
- `-Dz3.nativeCache=false` keeps the original private `java.io.tmpdir` extraction.
- `z3.skipLibraryLoad` keeps its existing behavior and does not access the cache.

The cache contains `.lock` and `<platform>-<content-sha256>` directories, each
with the Z3 library and JNI bridge. The identity hashes both bundled libraries;
it does not depend on version names, Maven coordinates or a new resource format.
Every JVM hashes the bundled bytes and verifies the cached files before loading.
This deliberately saves repeated writes and disk space, without promising
faster startup: reading/decompressing the selected platform's resources remains
necessary. Other platforms in an `all` JAR are not extracted or hashed.

## Publication, reuse and fallback

One file lock coordinates JVM processes. A shared JVM monitor also serializes
cache operations across ClassLoaders, so closing another loader's channel cannot
invalidate the first loader's OS lock. See Java 8's
[FileLock platform dependencies](https://docs.oracle.com/javase/8/docs/api/java/nio/channels/FileLock.html).
A miss is extracted into a staging directory, checked again, then published
with an [atomic directory move](https://docs.oracle.com/javase/8/docs/api/java/nio/file/Files.html#move-java.nio.file.Path-java.nio.file.Path-java.nio.file.CopyOption...-).
The core library is loaded before the JNI bridge.

The cache requires a user-owned directory, rejects symbolic links, and rejects
group/other-writable POSIX cache roots. Newly created POSIX directories use
owner-only permissions; Windows uses inherited profile ACLs. A custom root must
also have trusted parent directories and ACLs. This does not isolate mutually
untrusted programs running as the same OS user.

An unavailable cache, unsupported locking/atomic moves, damaged files that cannot
be replaced, or a library already associated with another ClassLoader falls
back to private extraction. Both conventional-load errors and the cache failure
remain available when that fallback also fails. A Java 8 SecurityManager may
restrict profile access; applications can disable caching explicitly.

The loader keeps the current pair and two recent pairs for the current platform.
Cleanup checks names and file types, never follows links or recursively deletes
directories, and preserves unknown files. Abandoned staging directories older
than 30 days are eligible for the same conservative cleanup. Loaded DLLs can
remain locked on Windows; such directories are skipped, so three pairs is a
retention target rather than a hard disk quota. The lock file is retained.

Private fallback retains the previous `deleteOnExit` policy. In particular,
multiple retained ClassLoaders still need separate copies and can leave DLLs
behind on Windows. Users can remove old private extraction directories after
the relevant JVMs exit. The cache does not promise safe coexistence of unrelated
Z3 ABI versions in one JVM.

## Validation

`smoke.py` runs both the platform and exact same `all` JAR through:

- Default cache selection in an isolated profile and three JVM restarts without
  rewriting the cached files or creating private temporary directories.
- Four JVMs using an initially empty cache, with Context/version/SAT/UNSAT checks.
- Corrupt-file repair and unavailable-cache fallback.
- Two retained isolated ClassLoaders, sequentially and concurrently, and an
  overlapping JVM file lock.
- Retention, abandoned staging cleanup, preservation of unknown files and
  symbolic-link rejection.
- Existing system-load, skip, missing-resource, unsupported-architecture and
  opt-out private-extraction/failure cases.

These cache modes are required by both the release and Maven rehearsal receipt
gates. They use current-branch generated classes with pinned JNI inputs in fast
CI, and same-run source-built inputs in Full Flow. No new native compilation,
dependencies, publication credentials or Maven coordinates are introduced.

On 2026-11-01, local Windows x64 checks passed with JDK 25.0.3 and pinned 5.3.2
native/API inputs: 66 regression tests, both single-platform packaging forms
through all 18 required smoke modes, the source/API class and signature check,
real Maven source/Javadoc generation, actionlint 1.7.12 for the three Java
packaging workflows, and `git diff --check`. Three restarts kept the cached
library hashes and modification times unchanged and the temporary directories
empty. Other-platform hosted results and current-source Full Flow remain
pending at this checkpoint. Packaging success alone is not native compatibility
evidence.
