# Java release attachments

The release and nightly workflows reuse `UbuntuBuild`, `WindowsBuild-x64` and `MacArm64`
from its existing native producers. Each producer records source commit,
source/runtime version, platform, workflow run ID, run attempt and ZIP SHA-256
in its existing artifact. Artifact names and ZIP layout remain compatible with
the existing NuGet and Python consumers. The three Java-producing jobs use
Temurin 17; API class bytes must agree across their distributions.

`java-package-artifacts.yml` is shared by Release Build, Nightly Build and Java Full Flow:

1. Download only the selected artifacts from the caller's workflow run.
2. Reject mixed source/version/run/attempt, missing inputs or incorrect hashes.
3. Assemble the unmodified source-built API and original native libraries.
   This job neither downloads release binaries nor compiles native code.
4. Test each platform JAR and the same universal JAR on native Linux x64,
   Windows x64 and macOS arm64 runners using Java 17. Tests cover Context,
   version, SAT/UNSAT, concurrent initialization, conventional loading and
   loading failures. Java 8 coverage remains in the fast Packaging Test CI.
5. Require all native receipts, matching source/loader/generator identity,
   final JAR hashes and every required smoke mode before producing the
   `java-release-packages` artifact. Include the receipts in a validation report.

The GitHub publisher depends on this entire gate. It selects Java files only
from `java-release-packages`, never the intermediate assembly. The existing
`publish_github` switch and draft/prerelease behavior are preserved; there is
no additional Java attachment publisher. Optional Maven deployment is separate
and disabled by default; see [MAVEN.md](MAVEN.md).

## Nightly downloads

Nightly Build records the same source/run/attempt receipts in its three existing
native artifacts and uses Temurin 17 for those producers. Its Java package job
uses only those same-run artifacts; it does not rebuild native code or download
binaries from the moving `Nightly` release. The existing Nightly publisher waits
for the shared Java gate and attaches only `java-release-packages`, excluding
Maven rehearsal ZIPs and intermediate Java assemblies.

The Nightly release provides the same API-only, platform and universal JAR
forms listed below. Names retain the checked-out source version, while the
provenance and validation attachments identify the exact source commit and
workflow run. The `Nightly` release/tag and its download contents are replaced
by later runs: keep the provenance and checksum files when pinning a build.
These downloads do not publish a Maven version or establish snapshot coordinates.

## Files and versions

For source version `X.Y.Z.0` and matching workflow `RELEASE_VERSION=X.Y.Z`:

- `z3-X.Y.Z.jar`: API only; use with an external native installation.
- `z3-X.Y.Z-linux-x64.jar`, `z3-X.Y.Z-win-x64.jar`,
  `z3-X.Y.Z-osx-arm64.jar`: API and the indicated platform's Z3/JNI pair.
- `z3-X.Y.Z-all.jar`: one API copy and all three selected platforms.
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

## Validation without publishing

Run the fast regression suite:

```text
python -m unittest discover -s scripts/tests -p "test_java*.py" -v
```

Dispatch **Java Full Flow** against the desired source commit to exercise the
same assembly, native tests and final release gate without publishing anything.
It builds only the three required native distributions. It never invokes
Release Build or accesses publishing credentials.

For an explicitly authorized rehearsal of the entire existing Release Build,
set `publish_github`, `publish_nuget`, and `publish_pypi` to false, and set
`maven_publish=disabled`. In particular, `publish_github` defaults to true;
the Maven override disables any configured repository publication mode.
Use the resulting verified artifact for inspection. Rerun **all jobs** when
retrying: successful native artifacts from a previous attempt are intentionally
rejected rather than mixed with the new attempt. A real release remains a
maintainer-controlled operation; Java Full Flow artifacts alone are not an
announcement of a released version.
