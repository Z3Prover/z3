# Maven artifact preparation (unpublished)

PR #11441 was merged on 2026-10-29. The official `z3-5.3.3` GitHub Release
contains the API JAR, `linux-x64`, `win-x64`, `osx-arm64` and `all` JARs,
with provenance, validation and SHA-256 attachments. This follow-up prepares
Maven companions and tests consumers; it does not publish to a Maven registry.

## Artifact family

The preparation flow deliberately fixes the test group to
`invalid.z3.prototype`. This is not a proposed official namespace. It produces:

- A POM with project, MIT license, contributor and commit-specific SCM metadata.
- The original API, platform and universal JARs, copied without changing bytes.
- Genuine `sources` and generated `javadoc` JARs for the shared Java API.
- Identical companion bytes under `<platform>-sources`, `<platform>-javadoc`,
  `all-sources` and `all-javadoc` classifiers for classified dependencies.
- `maven-preparation.json` with source hashes, API source commit, generator/loader
  checkout commit, class/signature validation and each JAR hash, plus SHA256SUMS.

Select one API-containing dependency, using `all` or a single platform
classifier. The unclassified artifact remains API-only. Do not combine these
forms on one classpath. Native-only companion dependencies are outside this change.

## Source and documentation integrity

Fast CI keeps the pinned 5.3.2 native inputs; it does not resolve `latest`.
`release.json` now also pins each handwritten Java source by commit and SHA-256.
Preparation combines those files with the current generated `Native.java` and
loader, and generates enumerations using the pinned headers. The actual API
JAR determines which handwritten files were shipped: the official CMake source
list currently excludes some Java files present in the repository.

Full Flow uses the current checkout's Java sources and official header list.
Only Java files are generated or compiled in packaging jobs. Native ZIPs still
come from the existing producers in the same workflow run and attempt.

Before creating companions, `sources.py` compiles the entire source set with
`javac --release 8` and compares the exact class set and every JVM member
signature against the API JAR. Comparison tolerates compiler member ordering,
including synthetic accessors, without dropping members or descriptors.
This is a compatibility check, not a proof that arbitrary source bodies and
bytecode are equivalent. Version/commit pinning and tracked generators establish
the source origin; provenance distinguishes mixed fast-test inputs.

Standard Maven Source Plugin 3.4.0 and Javadoc Plugin 3.12.0 create attachments.
The Java source entry hashes and required API/enum documentation pages are then
checked. Existing documentation is built with doclint disabled and errors remain
fatal. No remote documentation links are fetched. Fixed archive timestamps and
disabled Javadoc timestamps permit a repeated fast-CI build comparison under
the same JDK/Maven toolchain; cross-JDK byte identity is not promised.

## Consumer checks without remote publication

`maven_consumer.py` accepts a fresh local work directory. Deploy Plugin 3.2.0
places already-built files into a repository whose `file:` URL is derived from
that directory. The script has no remote repository upload option. It uses
isolated Maven settings and artifact cache, keeping credentials out of this test.
Maven plugins can still be downloaded from Central.

Independent Maven and Gradle projects resolve both the runner's platform and
`all` dependencies, plus their source/documentation classifiers. The test checks
resolved hashes and runs the existing smoke program with an empty JNI search
path. It requires exactly two extracted libraries and successful version,
Context, SAT/UNSAT and concurrent initialization checks. CI runs on Linux x64,
Windows x64 and macOS arm64 using Java 17. Existing Java 8/17/21 loader coverage
remains in the ordinary packaging smoke jobs. No additional native build occurs.

Example after `prepare.py --with-sources` and ordinary JAR assembly:

```text
python scripts/java/maven_artifacts.py --packages build/java-packages --sources build/java-test/sources --out-dir build/java-maven-packages --work-dir build/java-maven-work
python scripts/java/maven_consumer.py --packages build/java-maven-packages --platform win-x64 --work-dir build/java-consumer --gradle
```

Maven and Gradle must be installed to run both consumer tools. Omit `--gradle`
for a Maven-only local check; its receipt then contains Maven results only.
All output/work directories must be fresh to exclude stale artifacts.

The separate `java-maven-test-packages` artifact is never selected by the GitHub
Release attachment publisher. Existing final release verification also waits for
the new consumer jobs. There is no publication credential, signature or Maven
upload job in these workflows.

## Publication decisions reserved for maintainers

Maintainers must approve the official group/artifact coordinates, namespace
ownership, release responsibility and signing/token custody before publication.
The Java package name `com.microsoft.z3` does not establish Maven namespace rights.
The generic contributor metadata describes the code's contributors; it does not
assign a publishing owner.

GitHub Packages can provide a preview channel using the standard Deploy Plugin,
but even public Maven packages require consumer authentication under the
[GitHub Maven registry rules](https://docs.github.com/en/packages/working-with-a-github-packages-registry/working-with-the-apache-maven-registry).
For a default, public consumer experience, prefer Maven Central after namespace
approval. Central additionally requires signatures/checksums and accurate
[publication metadata and attachments](https://central.sonatype.org/publish/requirements/).
Its [Portal Maven integration](https://central.sonatype.org/publish/publish-portal-maven/)
is a separate, explicitly controlled follow-up. `deploy-file` is not itself a
complete Central Portal publishing workflow.

Both channels should receive the exact JAR bytes that passed native validation.
Sign and upload after that gate. A packaging fix needs a new version; do not
overwrite a published Central release. Clean Windows CRT availability, additional
architectures and minimum OS/runtime compatibility remain the existing explicit
boundaries in RELEASE.md.
