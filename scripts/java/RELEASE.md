# Standalone Java packaging validation

The release and nightly workflows do not run the shared Java/Maven packaging
stage or publish its standalone JAR attachments. Java bindings remain included
in the native distribution ZIPs. Dedicated Java CI remains enabled.

Java Full Flow builds native distributions and passes them to the shared
`java-package-artifacts.yml` validation workflow.
Each producer records source commit,
source/runtime version, platform, workflow run ID, run attempt and ZIP SHA-256
in its existing artifact. Artifact names and ZIP layout remain compatible with
the existing NuGet and Python consumers. The four Java-producing jobs use
Temurin 17; API class bytes must agree across their distributions.

The standalone validation workflow:

1. Download only the selected artifacts from the caller's workflow run.
2. Reject mixed source/version/run/attempt, missing inputs or incorrect hashes.
3. Assemble the unmodified source-built API and original native libraries.
   This job neither downloads release binaries nor compiles native code.
4. Test each platform JAR and the same universal JAR on native Linux x64/arm64,
   Windows x64 and macOS arm64 runners using Java 17. Tests cover Context,
   version, SAT/UNSAT, concurrent initialization, conventional loading and
   loading failures. Java 8 coverage remains in the fast Packaging Test CI.
5. Require all native receipts, matching source/loader/generator identity,
   final JAR hashes and every required smoke mode before producing the
   `java-release-packages` Actions artifact. Include the receipts in a validation report.

These artifacts are for inspection and validation, not automatic publication
to GitHub Releases or Maven Central. The reusable Maven publisher remains
disconnected from Release Build; see [MAVEN.md](MAVEN.md).

## Nightly downloads

Nightly Build records the same source/run/attempt receipts in its four existing
native artifacts and uses Temurin 17 for those producers. Download the native
distribution ZIP for the desired platform to obtain its Java bindings.
The `Nightly` release/tag and its download contents are replaced by later runs.
Standalone API-only, platform and universal JARs are no longer attached by the
nightly or release publishers. Native runtime requirements still follow the
native build platform; removing the packaging stage does not lower them.

## Files and versions

Standalone validation produces these files for source version `X.Y.Z.0`:

- `z3-X.Y.Z.jar`: API only; use with an external native installation.
- `z3-X.Y.Z-linux-x64.jar`, `z3-X.Y.Z-linux-arm64.jar`, `z3-X.Y.Z-win-x64.jar`,
  `z3-X.Y.Z-osx-arm64.jar`: API and the indicated platform's Z3/JNI pair.
- `z3-X.Y.Z-all.jar`: one API copy and all four selected platforms.
- `z3-X.Y.Z-java-provenance.json`: source, workflow and native input identity.
- `z3-X.Y.Z-java-validation.json`: native results and tested JAR hashes.
- `z3-X.Y.Z-java-SHA256SUMS`: checksums of every Java attachment above.

Use one API-containing JAR on the classpath. `all` covers the explicitly listed
platforms; other ZIP architectures are not implicitly included or claimed as
verified. These files do not include a Maven POM or claim Maven coordinates.
Namespace ownership and Maven deployment require maintainer configuration;
[MAVEN.md](MAVEN.md) describes companion preparation, consumer checks, signing
and the disabled-by-default Central workflow. In `--release` mode, the packer requires the exact source
version, workflow inputs and matching API class bytes, and refuses `--group-id`.
Fast tests retain their explicit prototype coordinates, suffixed version and
prototype provenance, so mixed test inputs cannot enter the release gate.

External system prerequisites still apply: supported glibc/libstdc++ on Linux,
macOS 13.3 or newer for these upstream builds, and the supported Microsoft
Visual C++ runtime on Windows. The JAR embeds only Z3 and its JNI bridge.
Hosted-runner success does not establish compatibility with a clean Windows
installation lacking that runtime. No native binaries are rewritten.
Bundled JARs reuse verified per-user native files when possible; see
[NATIVE_CACHE.md](NATIVE_CACHE.md) for configuration, cleanup and private fallback.

## Validation without publishing

Run the fast regression suite:

```text
python -m unittest discover -s scripts/tests -p "test_java*.py" -v
```

Dispatch **Java Full Flow** against the desired source commit to exercise the
same assembly, native tests and final verification gate without publishing anything.
It builds the four required native distributions. It never invokes
Release Build or accesses publishing credentials.

Use the resulting verified Actions artifact for inspection. Rerun **all jobs** when
retrying: successful native artifacts from a previous attempt are intentionally
rejected rather than mixed with the new attempt. A real release remains a
maintainer-controlled operation; Java Full Flow artifacts alone are not an
announcement of a released version.
