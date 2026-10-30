# Java release packaging prototype

The loader and layered CI were merged in
[PR #11434](https://github.com/Z3Prover/z3/pull/11434).
For the subsequent source-matched release attachment flow, see
[RELEASE.md](RELEASE.md). The investigation below records the earlier baseline;
it is not a statement of the current published release or Maven availability.
For the subsequent unpublished Maven source/Javadoc and consumer tests, see
[MAVEN.md](MAVEN.md).

Investigation date: 2026-10-29. Source baseline:
`c95b61cb03b22e258dfbc5941262c9273e6650bd` (upstream master).
This is a contribution prototype, not an official Maven distribution.

## Verified upstream state

- [Z3 latest stable release](https://github.com/Z3Prover/z3/releases/tag/z3-5.3.2)
  is `z3-5.3.2`, published 2026-10-25, targeting
  `b411c90217766c924e6ea3d0b51f452a89fd8fc2`. The development version is
  `5.3.3.0`. Tests must pin the release, commit, asset names and SHA-256 values;
  they must not resolve `latest` on each run.
- [PR #10529](https://github.com/Z3Prover/z3/pull/10529) was closed on
  2026-08-15 without merging. Its four changed files proposed Python packaging,
  base and classifier JARs, generated-loader fallback, fixture tests and an
  optional GitHub Packages upload. Public issue comments, PR reviews and inline
  review comments are empty. Its closure event has no explanatory body.
  The historical head has 38 check runs (36 success and two failed instances
  of the legacy Python-MT build). No public evidence links those failures to
  the closure. Its new tests were ZIP fixtures; the proposed release job was
  manual, so passing unrelated build checks would not prove bundled loading.
- The final [maintainer comment on #182](https://github.com/Z3Prover/z3/issues/182#issuecomment-5303682704)
  invites a new PR along those lines if there is user demand. This supports
  another upstream contribution; it does not establish why #10529 was closed.
  Earlier comments emphasize continuing maintenance, clear package ownership,
  accurate naming and an automated registry workflow.
- Current `scripts/update_api.py:mk_java` generates `Native.java` and JNI
  `Native.cpp` from the C API headers. `mk_consts_files.py` generates enums.
  `src/api/java/CMakeLists.txt` compiles the API for Java 8, builds the JNI bridge,
  and installs the JAR separately from the native libraries. The generated
  initializer tries `z3java`, then `libz3java`, and honors `z3.skipLibraryLoad`.
  It has no embedded-resource fallback.
- CMake already sets JNI Linux RPATH to `$ORIGIN` and macOS RPATH to
  `@loader_path`. This makes a no-rewriting experiment reasonable, but does not
  itself prove dynamic linking works for all release binaries.
- Release scripts now use CMake; the old `mk_make.py`/`mk_util.py` workflow was
  removed after #10529. `mk_unix_dist.py` and `mk_win_dist.py` install the API JAR
  under `java/` and flatten the JNI library into `bin/`. Do not reuse #10529's
  assumption that the API JAR is under `bin/`.
- `.github/workflows/release.yml` is manually dispatched. macOS x64/arm64,
  Windows x86/x64/arm64 and Linux x64/arm64 jobs upload ZIP artifacts. NuGet and
  Python packaging jobs depend on these producers and download artifacts from
  the same run. Publishing is separate. Current master contains no Java Maven
  packaging or Maven registry job.

Release ZIP coverage is Windows x86/x64/arm64, Linux x64 (glibc 2.39), Linux
arm64 (glibc 2.38), and macOS x64/arm64 (13.3). Python wheels additionally cover
Linux RISC-V; a wheel alone is not evidence of a corresponding Java JNI release.
Assets also include NuGet packages, Python sdist and documentation. Exact Java
test inputs and download URLs are recorded in `release.json`.

## Turnkey assessment

Inspected [tudo-aqua/z3-turnkey](https://github.com/tudo-aqua/z3-turnkey) at
`fe384a0f7de3d4a4de7e2f3ed6482546e74970f9`. It is not archived. Its latest
release is 4.14.1 (2025-06-30); [PR #155](https://github.com/tudo-aqua/z3-turnkey/pull/155)
is open and unmerged. That PR's statement about runner architectures is a
proposal author's explanation, not an independently established platform rule.

| Mechanism | Disposition for upstream | Evidence / remaining validation |
| --- | --- | --- |
| Gradle Kotlin/buildSrc orchestration, download and Python plugins | Replace with standard-library Python scripts | Upstream already owns generation and CMake; avoid another build system. |
| Regenerate every Java API class from downloaded source | Use official release API JAR for fast tests | Regenerate and compile the entire `Native` class family with pinned release headers and the current generator; compare JVM signatures before replacement. Full builds use all current sources. |
| JavaParser AST rewrite of `Native` initializer | Delete in upstream | Modify the generator at its source and add one package-private loader compiled by existing CMake. No turnkey code is copied. |
| ELF/Mach-O/COFF processing via `tools.aqua.turnkey` 1.0.0 | Evidence insufficient to remove across every platform | First try original binaries, explicit core-then-JNI loading and existing RPATHs. Gate platform claims on actual runner results; inspect dependencies on failure. |
| Native dependency metadata | Replace with explicit two-library platform table initially | Verify both binary headers and missing libraries; external CRT/libc/libstdc++ requirements remain platform prerequisites. Expand only with measured need. |
| Runtime extraction, platform detection, dependency ordering | Retain behavior in small Java helper | Private temporary directory, fixed resource names, preserved error causes, JVM class initialization serialization. |
| Shutdown/cleanup and multiple classloaders | Retain relevant tests; no process-global cache | Java delete-on-exit is best effort, especially for mapped Windows DLLs. Do not promise arbitrary coexistence of different Z3 versions/classloaders. |
| CI shared test-runner artifact and native OS tests | Retain principle with a smaller initial matrix | One packaging job, immutable JAR artifacts, native Linux x64/Windows x64/macOS arm64 smoke jobs, Java 8 and 17. Other combinations remain unverified. |
| Many JVM vendors, Node/Prettier, PMD, SpotBugs, task-tree/version plugins | Omit from initial contribution | They serve turnkey's broader project policy; they are not needed for this loader experiment. Java 8/17 coverage is retained. |
| Source/Javadoc, Maven metadata and signing | Retain for a future official release | Existing turnkey Gradle configuration uses a Central plugin and signing; its checked-in CI has build/test/dependency jobs but no explicit publish step. |

The external dependencies were also inspected at their pinned 1.0.0 releases:
[`turnkey-support`](https://github.com/tudo-aqua/turnkey-support/tree/8b3965afe55204cccb532b89a494a64d6b3bc38b)
and [`turnkey-gradle-plugin`](https://github.com/tudo-aqua/turnkey-gradle-plugin/tree/ea7629e62fbbe2978bc20f90f3563e42934db560).
The plugin builds a dependency graph, prunes it to JNI's transitive dependencies,
and writes `turnkey.xml` with bundled libraries, system libraries and load order.
The support runtime identifies OS/CPU, reads that XML, extracts the selected
files and executes the listed absolute-path loads. ELF processing uses
`patchelf` to alter RPATH, SONAME and needed-library names; Mach-O processing
uses `otool`/`install_name_tool` to alter IDs and dependencies. **The COFF task
does not rewrite DLLs**: it analyzes imports with `readobj` and generates an
explicit dependency load order. Its dependency handling serves a real purpose.
The proposed two-library loading policy replaces this machinery only for the
tested upstream binaries; it is not a general replacement for TurnKey's native
dependency analysis or its broader platform behavior.

## Recommended first change

1. Add a package-private Java loader called from generated `Native` initialization.
   Keep the two system-loading attempts and the skip property. On failure,
   extract both libraries from `com/microsoft/z3/native/<classifier>/`, then
   load the core before the JNI bridge using absolute paths. Preserve all three
   errors and identify the platform/resource/loading stage.
2. Assemble a base API JAR and **self-contained platform classifier JARs**,
   as in #10529, plus an **`all` universal JAR**. Each bundled form contains
   one copy of the same API classes. The universal JAR contains the exact union
   of the selected platform resources, with a platform manifest, per-library
   hashes and each input's license. Consumers select either `all` or one platform
   classifier; do not add the base or another bundled form alongside it.
   Native-only companion dependencies are deferred.
3. Python owns assembly, validation and provenance. It must reject duplicate
   entries, incomplete inputs, version drift, unexpected classes/resources and
   binary architecture mismatch. Stable ZIP entry order and timestamps allow
   repeatability checks. No native code is compiled by the packaging job.
4. Fast CI downloads only exact hash-pinned release assets. It uses the current
   generator and loader with same-release headers and official API classes,
   compiles all generated `Native*.class` files with Java 8 compatibility,
   compares their JVM member signatures to the release, and packages them.
   This proves the changed code is tested without claiming that release JNI
   implements newly added APIs in master.

Files: `scripts/update_api.py`, `src/api/java/CMakeLists.txt`, new
`src/api/java/NativeLibraryLoader.java`, `scripts/mk_java_package.py`,
`scripts/java/` test preparation/smoke tools and release lock,
`scripts/tests/test_java_package.py`, and `.github/workflows/java-packaging.yml`.

## CI sequence and Maven ownership

Packaging Test CI runs on relevant PRs, with read-only permissions and no
publishing credentials. A single Linux job prepares the selected platform JARs;
native runner jobs consume those exact files, verify hashes and exercise
Context/version/SAT/UNSAT, concurrent initialization, system loading and failure
diagnostics against both their platform JAR and the **same universal JAR bytes**.
The extraction check requires exactly the current platform's two libraries;
foreign-platform resources remain in the JAR. Both bundled forms also exercise
system-first loading in the presence of embedded resources. Linux/Windows
initially test Java 8 and 17; macOS arm64 tests Java
17 and 21, avoiding an assumption that Temurin 8 has a native macOS arm64 build.
It never calls CMake or a native distribution build script.

`.github/workflows/java-full-flow.yml` is the controlled Full-Flow CI. Its
three native jobs invoke the existing `mk_unix_dist.py`/`mk_win_dist.py`
producers, with unrelated language bindings disabled. It does not copy the
release workflow or its publishing jobs. `workflow_inputs.py` records and checks
commit/version/OS/architecture, run ID, run attempt and ZIP hash. A separate
packaging job accepts only those same-run artifacts, with no native recompilation
or substitution of downloaded release binaries; Java 17 smoke jobs consume its
final platform and universal JARs. It can be dispatched manually after reaching a default branch. On
the initial fork branch, only a commit explicitly marked `[java-full-flow]`
starts the expensive native jobs, which permits initial validation without
altering the fork's default branch.
Rerun all jobs when retrying Full Flow: successful producers from an earlier
run attempt are intentionally rejected instead of being silently mixed.
The existing release workflow defaults `publish_github=true`; do not invoke it
as a test without explicitly disabling publication.

No Maven coordinates are claimed. Prototype POMs require explicit coordinates;
CI uses `invalid.z3.prototype:z3` with a test-only version. Official groupId,
artifactId, namespace rights, maintainer identity and signing custody require
maintainer agreement. Release versions should follow the Z3 tag without `z3-`;
PR tests use a `-packaging-SNAPSHOT` suffix and provenance marks the mixed test
source/release-binary inputs.

Future release: Python prepares JARs/provenance, Maven attaches them with
standard plugins. Generate sources from the **same** API source/generator inputs
and Javadoc from those sources. Sources/Javadoc cannot be honestly supplied
from a precompiled JAR alone. Use standard source/Javadoc/GPG plugins as needed;
no custom Maven plugin. [Central requirements](https://central.sonatype.org/publish/requirements/)
include source/Javadoc companions, signatures, checksums and complete POM metadata
(license, developers, SCM). [Central Portal's Maven publishing plugin](https://central.sonatype.org/publish/publish-portal-maven/)
and an approved namespace/token are separate from
[deploy-file](https://maven.apache.org/plugins/maven-deploy-plugin/deploy-file-mojo.html)
uploads to GitHub Packages. Neither publication path is enabled in this prototype.

## Open questions and boundaries

- The pinned 5.3.2 inputs link without rewriting on the three tested runner
  platforms. Additional CPU/OS combinations, versioned SONAME/install-name
  behavior and minimum glibc/macOS versions need their own measured tests.
  The 5.3.2 Windows x64 core imports MSVCP140, VCRUNTIME140 and VCRUNTIME140_1;
  the official ZIP ships these. This prototype currently treats the supported
  VC++ runtime as a prerequisite and bundles only Z3/JNI. Success on developer
  or hosted-runner machines does not prove a clean Windows installation has
  that runtime. Redistribution scope/licensing and clean-machine testing must
  be resolved before claiming a standalone Windows distribution.
- Platform names follow #10529 (`linux-x64`, `osx-arm64`, `win-x64` etc.); add
  architectures only with pinned JNI inputs and native execution evidence.
- Temp-directory availability, failure diagnostics, skip behavior and Java 8
  compatibility are required. Cleanup of mapped DLLs and multiple independent
  classloaders remain explicitly bounded behavior.
- Do not interpret a closed PR as upstream rejection of this design. Propose a
  complete, reproducibly tested PR; after submission, request review after
  roughly 2 weeks and reassess after 6-8 weeks without substantive review.
  These are proposed project checkpoints, not upstream promises. An explicit
  rejection or prolonged stagnation can trigger a separate-project decision;
  no independent public project is created now.

## Running the prototype

Every assembly emits `z3-VERSION.jar` (API only),
`z3-VERSION-PLATFORM.jar` for each selected platform, and
`z3-VERSION-all.jar` (API plus all selected platforms). The `--platform` list
defines that assembly's exact platform set; `all` does not silently include
unselected entries from the release inventory. CI selects Linux x64, Windows
x64 and macOS arm64, the current tested scope. A one-platform local assembly
therefore has a one-platform `all` JAR; use the full CI selection for the
cross-platform distribution.

For Maven consumers, choose `<classifier>all</classifier>` for the shared
cross-platform JAR, or e.g. `<classifier>win-x64</classifier>` for the smaller
platform JAR. Coordinates are still test-only; none of these files has been
published to a Maven registry. The default artifact remains API-only for
compatibility with external native installations.

Use Python 3.10+ and JDK 17+ for preparation (JDK 8+ for smoke tests). From the
repository root, use fresh output directories; downloads may be reused after
hash verification. Example for Windows x64:

```text
python -m unittest discover -s scripts/tests -p test_java_package.py -v
python scripts/java/prepare.py --work-dir build/java-test --platform win-x64
python scripts/mk_java_package.py --release-lock scripts/java/release.json --artifacts-dir build/java-test/downloads --api-jar build/java-test/prepared-api.jar --preparation build/java-test/preparation.json --out-dir build/java-packages --platform win-x64 --group-id invalid.z3.prototype --artifact-id z3 --version 5.3.2-packaging-SNAPSHOT
python scripts/java/smoke.py --packages build/java-packages --platform win-x64 --work-dir build/java-smoke
```

The conventional system-library test configures the OS dependency search path
as well as `java.library.path`. The embedded test sets an empty JNI search
directory and checks that only the current platform's two resources were
extracted. `smoke.py` defaults to testing both forms; `--jar-kind all` and
`--jar-kind platform` select one form. Each mode uses a fresh JVM. Receipts
record each tested JAR's name, hash and modes separately. Native JVM
diagnostics are retained, including Java 25's
restricted-native-access warnings; this prototype does not claim future JDK
native-access defaults are covered by Java 8/17/21 tests.
