# Maven artifact preparation (unpublished)

PR #11441 was merged on 2026-10-29. The official `z3-5.3.3` GitHub Release
contains the API JAR, `linux-x64`, `win-x64`, `osx-arm64` and `all` JARs,
with provenance, validation and SHA-256 attachments. PR #11454 added Maven
companions and consumer tests. Repository rehearsals extend those tests without
publishing to a Maven registry.

## Artifact family

The preparation flow defaults to the test group `invalid.z3.prototype`.
This is not a proposed official namespace. An explicit `--group-id` selects a
maintainer-configured group before repository and consumer validation. It produces:

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
Packaging jobs regenerate the bindings and compile Java. Native ZIPs come from
the existing producers in the same workflow run and attempt.

Before creating companions, `sources.py` compiles the entire source set with
`javac --release 8` and compares the exact class set and every JVM member
signature against the API JAR. Comparison tolerates compiler member ordering,
including synthetic accessors, without dropping members or descriptors.
Loader source bytes and, for fast preparation, generated Native source bytes
must also match the hashes captured when preparing the binary API.
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

`maven_consumer.py` accepts a fresh local work directory. With `--repository`,
it checks and consumes the already assembled Maven directory. Without this
option, the existing repository assembler places already-built files and the
selector POM into a fresh local repository.
Both modes construct a `file:` URL from a local path and have no remote upload option. They use
isolated Maven settings and artifact cache, keeping credentials out of this test.
Maven plugins can still be downloaded from Central.

Independent Maven and Gradle projects resolve both the runner's platform and
`all` dependencies, plus their source/documentation classifiers. The test checks
resolved hashes and runs the existing smoke program with an empty JNI search
path. It requires exactly two extracted libraries and successful version,
Context, SAT/UNSAT and concurrent initialization checks. CI runs on Linux x64,
Windows x64 and macOS arm64 using Java 17. Existing Java 8/17/21 loader coverage
remains in the ordinary packaging smoke jobs. No additional native build occurs.

The Maven consumer also declares the POM-only automatic selector without a
classifier, consumer-side OS profiles or platform-detection extensions. Its
classpath must contain exactly the expected platform JAR, and it runs the same
native smoke. An offline negative metadata fixture with no matching platform
profiles must fail resolution of the default unavailable classifier. This fixture
does not represent execution on an unsupported native host. The final bundle requires this additional
receipt and binds it to the selector POM's SHA-256 as well as the runtime JAR.

Example after `prepare.py --with-sources` and ordinary JAR assembly:

```text
python scripts/java/maven_artifacts.py --packages build/java-packages --sources build/java-test/sources --out-dir build/java-maven-packages --work-dir build/java-maven-work
python scripts/java/maven_bundle.py prepare --packages build/java-maven-packages --out-dir build/java-maven-repository
python scripts/java/maven_consumer.py --packages build/java-maven-packages --repository build/java-maven-repository --platform win-x64 --work-dir build/java-consumer --gradle
```

Maven and Gradle must be installed to run both consumer tools. Omit `--gradle`
for a Maven-only local check; its receipt then contains Maven results only.
All output/work directories must be fresh to exclude stale artifacts.

The separate `java-maven-test-packages` artifact is never selected by the GitHub
Release attachment publisher. Existing final release verification also waits for
the new consumer jobs. PR and Full-Flow validation jobs have no publication
credentials and perform no Maven uploads.

## Offline repository bundle

`maven_bundle.py prepare` validates the exact family, its SHA-256 manifest,
POM coordinates and SCM commit, source hashes, required Javadoc pages, and
embedded native manifests. It copies the existing POM/JAR bytes to the standard
`group/path/artifact/version/` directory and writes MD5, SHA-1, SHA-256 and SHA-512
sidecars. MD5/SHA-1 serve repository compatibility; SHA-256 binds the test evidence.
It does not generate snapshot timestamp metadata or expose an HTTP repository.
The fixed test snapshot is consumed directly from the local file repository.

Maven and Gradle consumers record a hash of this exact directory as well as
the preparation report and resolved JARs. A final job in fast and Full-Flow CI
downloads the repository, family and receipts from that same workflow run.
`maven_bundle.py verify` requires all declared platforms, both consumer tools,
both platform/universal JARs and all seven native smoke modes. It rejects stale
source identities, changed files, missing companions and incomplete receipts.
Full-Flow native provenance must also match repository, run ID and attempt.
Fast CI retains its explicitly mixed, pinned-release/current-loader provenance.

The repository also includes an unpublished `<artifactId>-auto` POM generated
from the validated platform list. Its identity, SCM commit and checksum sidecars
are covered by the same repository digest. No Java classes or new native builds
are needed for this additional artifact. The original runtime POM remains free
of platform-selection dependencies, since that POM is shared by API-only,
platform and `all` dependencies.

Only after these checks does it produce `maven-rehearsal.zip`, `rehearsal.json`
and `SHA256SUMS`. The ZIP contains the Maven directory only; the report preserves
provenance and test receipts separately. ZIP timestamps and ordering are fixed,
so identical inputs produce identical ZIP bytes. The report always states
`publishable: false` and `signed: false`. No signatures, production coordinates,
remote uploads or registry acceptance are implied. Central signatures and
Portal-side validation remain a later, maintainer-controlled step.

The `java-maven-test-repository` and `java-maven-rehearsal-bundle` artifacts are
also excluded from the GitHub Release attachment publisher. Packaging jobs
reuse the tested JARs and never rebuild native code for this rehearsal.

## Dependency examples for a local rehearsal

These examples use the deliberately unpublished test coordinates and a local
repository from fast CI. They are not dependencies available on Central.
Replace the local repository URL with the absolute `file:` URL for your directory.

```xml
<repositories>
  <repository>
    <id>z3-local-rehearsal</id>
    <url>file:///absolute/path/to/java-maven-repository</url>
  </repository>
</repositories>
<dependencies>
  <dependency>
    <groupId>invalid.z3.prototype</groupId>
    <artifactId>z3</artifactId>
    <version>5.3.2-packaging-SNAPSHOT</version>
    <classifier>all</classifier>
  </dependency>
</dependencies>
```

```groovy
repositories { maven { url = uri('/absolute/path/to/java-maven-repository') } }
dependencies { implementation 'invalid.z3.prototype:z3:5.3.2-packaging-SNAPSHOT:all' }
```

Use `all` for the supported platform union, or replace it with `linux-x64`,
`win-x64` or `osx-arm64` for a platform JAR. Omit the classifier for the API-only
JAR, supplying matching system native libraries through the existing loader
mechanism. Select a single form per classpath. Platform/universal JARs extract
only the current platform's libraries and still require OS runtime dependencies
described in RELEASE.md. A successful rehearsal on these three platforms does
not establish compatibility with additional OS/CPU combinations.

## Optional Maven automatic platform selection (unpublished)

With the same local rehearsal repository, Maven users can instead declare:

```xml
<dependency>
  <groupId>invalid.z3.prototype</groupId>
  <artifactId>z3-auto</artifactId>
  <version>5.3.2-packaging-SNAPSHOT</version>
  <type>pom</type>
</dependency>
```

The published selector POM activates OS/architecture profiles and depends on
exactly one of the existing self-contained platform JARs. The consuming project
does not need a classifier, its own profiles or a detection plugin. The `pom`
dependency type avoids an empty selector JAR and extra source/Javadoc artifacts.
The API source/Javadoc companions remain attached to the selected runtime JAR.
`z3-auto` is a provisional test artifactId, not an approved official coordinate.

Detection follows the JVM running Maven, including its architecture. Supported
profiles are generated only for platforms present in the prepared repository.
Unknown platforms resolve an intentionally unavailable
`unsupported-platform-use-explicit-classifier` classifier and fail instead of selecting
another architecture. For a different deployment target, use the ordinary `z3`
dependency with an explicit platform classifier, or select `all` for one
cross-platform application artifact. These forms do not pull in an additional
platform JAR. Overriding the selector with CLI or consumer POM properties is not
supported: dependency profile activation differs between Maven versions.

This entry point is Maven-specific. Gradle consumers should continue selecting
a platform classifier or `all`; Maven profile activation does not establish
automatic selection in Gradle. The selector adds no new native platform support.
Cross-platform CI results, rather than successful POM generation, establish its
tested coverage.

The published OS profiles use the same general approach as the
[OpenJFX 21.0.2 parent POM](https://repo.maven.apache.org/maven2/org/openjfx/javafx/21.0.2/javafx-21.0.2.pom).
Only OS/architecture activation is used. Maven 3.10 isolates dependency profile
activation from consumer CLI properties and also considers properties declared
in the dependency POM; a self-referencing custom-override profile can therefore
activate unexpectedly. See the
[Maven 3.10 profile activation context](https://maven.apache.org/ref/3.10.0/apidocs/org/apache/maven/model/profile/ProfileActivationContext.html).
The selector avoids that property-activation dependency. Consumer tests exercise
the actual resolved POM rather than only inspecting its XML, and record the
installed Maven version in their receipts.

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
is explicitly controlled as described below. `deploy-file` alone is not a
complete Central Portal publishing workflow.

Both channels should receive the exact JAR bytes that passed native validation.
Sign and upload after that gate. A packaging fix needs a new version; do not
overwrite a published Central release. Clean Windows CRT availability, additional
architectures and minimum OS/runtime compatibility remain the existing explicit
boundaries in RELEASE.md.

## Central publication configuration (disabled by default)

The shared Java validation workflow stages already tested JARs and POMs through
the standard Maven Deploy Plugin without credentials or upload. Source-built
stable Full Flow then runs Sonatype's `central-publishing-maven-plugin` 0.12.0
with `skipUpload=true`, using the unchanged POM-only selector as its project.
Fast CI retains its pinned SNAPSHOT identity and assembles a local rehearsal ZIP
instead, since Central's plugin sends snapshots through a different mechanism.
The `java-maven-central-rehearsal` Actions artifact contains the bundle and exact
file hashes; its receipt identifies which tool ran. Local repository metadata is
excluded. Deployment runs on Linux; local Windows rehearsals check the plugin's
native ZIP separator variants against the exact inventory but cannot upload.
Native code is never rebuilt by these steps.

Release Build has a `maven_publish` input:

- `configured` (default): use `JAVA_MAVEN_CENTRAL_MODE`, falling back to `disabled`.
- `disabled`: always skip deployment, even when credentials exist.
- `validate`: sign and upload for Central validation, leaving public release to
  the maintainer through the Portal.
- `publish`: sign, upload, and wait for validated artifacts to be published.

Adding credentials alone does not enable deployment. When deployment is enabled,
missing configuration is an error, not a successful skip. Repository preparation
still uses test coordinates when no group is configured.

After approving the coordinates and obtaining namespace rights, an upstream
maintainer configures repository variables:

- `JAVA_MAVEN_GROUP_ID`: the approved namespace. The preparation, selector,
  three-platform consumer tests and final bundle all use it before publishing.
- `JAVA_MAVEN_ARTIFACT_ID`: the artifactId already used by the source-built and
  tested family (currently `z3`). This is an approval check, not a rename step.
- `JAVA_MAVEN_CENTRAL_MODE`: initially `disabled`; use `validate` for the first
  controlled deployment and `publish` only after reviewing it.

Configure a `maven-central` GitHub environment with release-tag restrictions and
the required approvals, then add `CENTRAL_USERNAME`, `CENTRAL_PASSWORD`,
`MAVEN_GPG_KEY` and `MAVEN_GPG_PASSPHRASE`. Use Portal user-token
credentials and an exported, passphrase-protected PGP signing key whose public
key is available as required by Central. The Maven GPG Plugin 3.2.8 BC signer
reads key material and passphrase from environment variables; neither is placed
on the command line, in generated POMs, or in uploaded build artifacts.

Deployment requires an upstream `workflow_dispatch` run from the matching
`refs/tags/z3-X.Y.Z` tag, a numeric stable version, current-source native inputs
from that exact run/attempt, and the complete native/Maven/Gradle receipt gate.
The publisher rechecks the verified repository bytes and receipts, signs the
same JAR bytes, rehearses the signed bundle locally, and then calls the Central
plugin. Existing stable coordinates and errors checking remote state fail
instead of silently overwriting or skipping publication. This workflow is not
called by PR, fast packaging or Nightly runs; fork deployment is rejected.

After the first controlled deployment, setting the repository mode to `publish`
allows later tagged Release Build runs to publish without per-version source
edits. The explicit `disabled` input remains available for rehearsals. Upload,
validation and published states are distinct in the publication receipt. A
failed/partial Portal deployment needs inspection before retrying; Central
release versions must not be overwritten.

GitHub Packages and Maven SNAPSHOT publication are separate optional channels.
This change neither configures them nor assigns an official publishing owner.
The actual namespace, environment approvals and credentials remain maintainer
decisions tracked in [issue #11471](https://github.com/Z3Prover/z3/issues/11471).
