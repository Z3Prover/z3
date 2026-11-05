# Java packaging evidence

This records experiments for an upstream contribution. It does not establish an
official Maven release or platform coverage beyond the rows below.

## Linux ARM64 extension

The workflow matrix now includes native `ubuntu-24.04-arm` runners. Packaging
Test uses the existing hash-pinned 5.3.2 Linux ARM64 ZIP with current-branch Java
classes, and tests both the platform JAR and the same four-platform `all` JAR
on Temurin 8 and 17. The Maven/Gradle consumer matrix also tests this platform,
including Maven automatic selection for `aarch64`.

Full Flow builds Linux ARM64 from the checked-out source on an ARM64 runner.
Release and Nightly reuse their existing cross-built `UbuntuArm64` ZIP with a
source/run/attempt/hash receipt. All callers pass that artifact to the shared
package job; this job does not rebuild native libraries. The existing receipt
gates require Linux ARM64 smoke and consumer results before accepting the
expanded artifact family. Run-specific results are recorded in the PR; adding
a matrix entry alone is not evidence of a passing native test.

This targets glibc-based Linux. It does not extend coverage to musl, Android,
older glibc releases or other architectures.

## Initial classifier Packaging Test CI

- [First successful run](https://github.com/nieyuanhong/z3/actions/runs/40814341795)
  at `79db3b2e4e2adf09297f07418e872980b9389829`.
- [Regression after same-run artifact validation](https://github.com/nieyuanhong/z3/actions/runs/40814911425)
  at `72bf314c711acb75e0796195a1bce2b64c914f6f`.

Both runs passed the packaging job and all six native smoke jobs:

| Native runner | Classifier | JVMs | Result |
| --- | --- | --- | --- |
| Ubuntu 24.04 x64 | `linux-x64` | Temurin 8, 17 | PASS |
| Windows 2025 x64 | `win-x64` | Temurin 8, 17 | PASS |
| macOS 15 arm64 | `osx-arm64` | Temurin 17, 21 | PASS |

Downloaded smoke receipts confirm native JVM architectures (`amd64` on Linux
and Windows; `aarch64` on macOS). Both JVM tests for each classifier used the
same JAR bytes in the second run:

| Classifier | JAR SHA-256 |
| --- | --- |
| `linux-x64` | `78007db7816afbe3f1189b0355468524f430a68f731f564571373f4d2c70a34b` |
| `win-x64` | `c450e0e79f2426b4d0e4da118ea68757801fbd07751fe42f9b16add0cf8c420c` |
| `osx-arm64` | `4811139c5d4be4ef2e4b7cfc55b72955aa07e7b479c9a2a505da01b542f76689` |

Inputs are hash-pinned Z3 5.3.2 release ZIPs and release headers. The **current
branch's** generator and helper are compiled for Java 8, replacing the entire
eight-class `Native` family after JVM member-signature comparison. Unrelated
API JAR entries remain byte-for-byte equal to the release. Platform JARs are
assembled once and passed to the smoke jobs through Actions artifacts; their
hashes are checked before use. Repeated assembly compares all artifact hashes.

Each smoke job verifies Context creation, native version `5.3.2.0`, SAT, UNSAT,
four-thread initialization, actual embedded extraction with an empty JNI search
directory, the conventional external installation, missing resources,
unsupported architecture, `z3.skipLibraryLoad`, temporary-directory I/O errors,
and nine OS/CPU aliases. All bundled native bytes are unmodified.

This supports omitting native rewriting on these three tested configurations.
It does not establish macOS x64, Windows x86/arm64, Linux arm64, musl, Android,
old glibc/macOS versions, clean Windows CRT availability, or multiple independent
classloaders. Classifier entries in `release.json` for other platforms are an
inventory, not an assertion of tested support.

## Initial local checks

Windows x64 / OpenJDK 25.0.3 / Python 3.14.4:

- 16 packaging/source-artifact regression tests passed, including mismatched
  run, retry attempt, commit, version, architecture and resource rejection.
- Three existing `test_update_api.py` tests passed.
- Eight generated Native classes matched the release JVM signatures.
- Repeated assembly was byte-for-byte deterministic under the same toolchain.
- All six native smoke modes and nine platform alias cases passed locally.
- Python syntax, workflow structure and `git diff --check` passed. The structure
  check is not an actionlint result; actual hosted runs are the stronger evidence.

Java 25 emits restricted-native-access warnings. The prototype preserves these
JVM diagnostics; future native-access defaults require separate compatibility
work. Developer/hosted-runner success does not establish a clean Windows CRT
installation requirement is unnecessary.

## Initial classifier Full Flow

[Current-source run](https://github.com/nieyuanhong/z3/actions/runs/40814912126)
passed at `72bf314c711acb75e0796195a1bce2b64c914f6f`: all three native build
jobs, the separate package job and all three final smoke jobs succeeded.
Linux x64, Windows x64 and macOS arm64 built the current 5.3.3 source; their
packaged native version was checked as `5.3.3.0` on Java 17. The package job
downloaded only these same-run artifacts, verified their identities and hashes,
and assembled the final JARs without native compilation or external binary
downloads. This run predates the universal-JAR change; it is evidence for the
initial classifier implementation only.

## Universal and platform packaging

Implementation commit: `07aabfcfd8c8e13ad29db264604a3b344764df7c`.

[Packaging Test CI](https://github.com/nieyuanhong/z3/actions/runs/40835923119)
passed the package job and all six native runner jobs. Every runner tested both
its platform JAR and `z3-5.3.2-packaging-SNAPSHOT-all.jar`. Downloaded receipts
confirm the **same universal JAR** on Linux x64 (Java 8/17), Windows x64
(Java 8/17) and macOS arm64 (Java 17/21):

```text
SHA-256 227b0e7042f1641eced35cd066c9b46749f40b5d6d656bb55fef2da52f1e8172
```

Each form passed seven fresh-JVM modes: embedded loading, conventional system
loading with embedded resources present, API-only system loading, missing
resources, unsupported CPU, skipped loading and temporary-directory failure.
Embedded mode requires exactly the current platform's two library filenames in
one private directory, including when foreign-platform resources are present in
the universal JAR. Context/version/SAT/UNSAT and four-thread initialization run
in both embedded and system modes. Nine OS/CPU alias cases pass for each form.

The 21 Python regression tests passed locally and in Packaging Test CI. New
cases check the universal resource union against all platform JARs, identical
API classes, per-platform license preservation, deterministic outputs under
reordered platform selection, rejection of incomplete or wrong-CPU selected
inputs before output creation, and detection of changed/missing/extra resources,
platforms or API classes. Three existing generator tests also passed locally.
Windows x64 / OpenJDK 25.0.3 additionally passed all seven modes for both forms.

[Full Flow](https://github.com/nieyuanhong/z3/actions/runs/40835923208) also
passed at that implementation commit: three current-source native builds, one
separate package job and three Java 17 smoke jobs. The package job reused only
the same run/attempt's Linux x64, Windows x64 and macOS arm64 distributions;
it neither rebuilt nor downloaded replacement native libraries. Both JAR forms
passed all seven modes with native version `5.3.3.0`. All three downloaded
receipts report one identical source-built universal JAR:

```text
SHA-256 4919db57d50df2442d66a18eb500236b37474667846489e46c14c59d73d5d057
```

The two universal hashes differ because fast CI packages 5.3.2 release natives
and Full Flow packages the current 5.3.3 source. Equality is required across
native runners within each run, not between these different inputs.

The universal JAR contains the selected three-platform set. Other release
inventory entries and clean Windows CRT availability remain outside these
results. It uses the existing loader unchanged and does not rewrite native
binaries.

Official coordinates, sources/Javadoc companions, signing, a Central publishing
owner and an authorized release gate remain future work. Nothing here publishes
to GitHub Releases, GitHub Packages, Maven Central, NuGet or PyPI.

## Release attachment integration (PR #11441)

Implementation commit: `95f7ee180d517949d8c37d0cfd50212b34338c8a`, based on
upstream `e1715501f71ec2fe659087b7af0c0cc3cc6bc6d9`. The subsequent
`441a9d9` correction adds `.github/workflows` to fast CI's sparse checkout for
the attachment-selection test and makes Windows Bash discovery portable.

Local Windows checks passed:

- 32 packaging/release tests, including exact stable version checks,
  rejection of mixed test inputs, cross-platform API class equality,
  missing/stale/incomplete smoke receipt rejection, output checksum coverage,
  and execution of the actual publisher's attachment-selection shell logic.
- Three existing generator tests.
- actionlint 1.7.12 on `java-packaging.yml`, `java-full-flow.yml`,
  `java-package-artifacts.yml` and `release.yml`, with ShellCheck disabled.
- The updated smoke tool ran both existing Windows platform and universal
  artifacts through seven JVM modes and nine platform aliases. This is
  compatibility evidence for the tool, not a current-source release build.

Hosted validation is tracked at
[Packaging Test](https://github.com/nieyuanhong/z3/actions/runs/40857766755)
and [Java Full Flow](https://github.com/nieyuanhong/z3/actions/runs/40857306477).
At this checkpoint, validation is pending; neither run is recorded as passing.
The first fast run exposed the missing workflow in the sparse checkout, which
was corrected before the linked fast run. Full Flow uses the shared release
assembly/native smoke/receipt gate and cannot publish.

The full multi-language Release Build and actual GitHub publication have not
been exercised. Maven publication, signing, official coordinates, additional
architectures and clean Windows CRT availability remain outside this PR's
validation. See [RELEASE.md](RELEASE.md) for the release artifacts and rehearsal
procedure. PR #11441 remains a draft until its hosted checks can be assessed.

## Maven preparation follow-up (2026-10-30, PR #11454)

The preceding paragraphs are historical checkpoints. Rechecking upstream on
2026-10-30 confirmed that PR #11441 was merged on 2026-10-29 at
`68ba6f35daba276596e49f63ed1398130c4f0ff1`.
[Fast CI at its final head](https://github.com/nieyuanhong/z3/actions/runs/40858779996)
passed. [Full Flow](https://github.com/nieyuanhong/z3/actions/runs/40857306477)
passed at implementation commit `95f7ee1`; that run does not establish an
exact-head Full Flow result for the subsequent documentation/CI corrections.
The official `z3-5.3.3` Release now includes the API, three platform and universal
JARs, provenance, validation and checksums.

[PR #11454](https://github.com/Z3Prover/z3/pull/11454) starts from upstream
`1b859b6bc7637a9c802a92a0dee72df9e843274d` on the separate
`feat/java-maven-artifacts` branch. Local Windows evidence for the implementation:

- 38 packaging/release/Maven tests and three generator tests passed.
- actionlint 1.7.12 passed for all five affected Java/release workflows, with
  ShellCheck disabled; `git diff --check` passed.
- The pinned 5.3.2 Java sources, current generated Native and loader compiled
  with Java 8 compatibility. All 157 classes and JVM member signatures match
  the prepared API, allowing compiler member-order differences only.
- The actual loader/Native source bytes match preparation hashes. A regression
  also rejects a changed body with the same signature.
- Maven Source/Javadoc plugins produced real companion archives. All nine JAR
  hashes in the one-platform Windows test family reproduced in a separate
  output/work directory under the same local toolchain.
- Maven and checksum-verified Gradle 9.8.2 each resolved the Windows platform
  and universal forms plus their corresponding source/Javadoc classifiers from
  isolated file repositories. Resolved hashes, bundled extraction, Context,
  runtime version, SAT/UNSAT and concurrent initialization passed in all four
  consumer cases. Local source compilation used JDK 25 with `--release 8`.

These local prototype inputs remain deliberately pinned to 5.3.2 and are not
current-source native builds. The new CI schedules Java 17 consumer checks on
Linux x64, Windows x64 and macOS arm64; those hosted checks and the new Full Flow
have **not run** at this checkpoint. The fork's Actions are disabled. Dispatch
returns HTTP 422: `Actions has been disabled for this repository.` Restoring that
repository setting requires the owner's decision. The PR remains Draft; no
registry publication or publishing credentials were used. See [MAVEN.md](MAVEN.md)
for scope and the remaining namespace, ownership and signing decisions.

## Optional Maven platform selector (2026-10-31)

This follow-up starts from upstream `974e3512dbf462dc537b5eda4a2166910ac9f9cf`.
The publication discussion is [issue #11471](https://github.com/Z3Prover/z3/issues/11471).
It adds an unpublished POM-only selector to the repository rehearsal; it does
not choose official coordinates or add a publisher.

Local Windows x64 checks passed with Maven 3.9.12, Gradle 9.8.2 and JDK 25.0.3:

- All 55 packaging/release/Maven regression tests passed. New cases cover the
  generated selector, deterministic metadata, rejection of duplicate runtime
  JARs or unrelated POMs, and exact selector receipts at the final bundle gate.
- Maven resolved and executed the explicit platform, universal and automatic
  forms. Gradle resolved and executed both existing explicit forms. All five
  cases verified runtime/source/Javadoc hashes, embedded JNI extraction,
  Context/version/SAT/UNSAT and concurrent initialization.
- The automatic consumer declared no classifier or OS profiles. Its actual
  dependency POM and selected Windows JAR matched their expected SHA-256 values.
  This initial implementation also tested a CLI override, but the hosted Linux
  consumer subsequently exposed a Maven 3.10 incompatibility in the override
  profile. That result does not establish portable CLI override support.
- actionlint 1.7.12 passed for the five Java packaging/consumer/rehearsal
  workflows with ShellCheck disabled; `git diff --check` passed.

These local consumer checks reused existing 5.3.2 prototype native/API inputs
with source identity `1b859b6bc7637a9c802a92a0dee72df9e843274d`. Their provenance
was preserved when preparing the Maven family with the current script. The
local harness reused cached Maven plugins and a file mirror to avoid repeated
network downloads. These results do not establish current-source native builds
or automatic selection on another operating system.

At this checkpoint, hosted Packaging Test and Full Flow results for this
follow-up are pending. The consumer matrix exercises automatic selection on
Linux x64, Windows x64 and macOS arm64; the existing native smoke coverage is
unchanged. The PR remains Draft until hosted validation can be assessed.

The hosted Linux consumer at `1605bb5` failed with a recursive expression in
`z3.platform`; Windows passed. Maven 3.10's external profile activation also
consults the dependency's own properties. The follow-up removes property-based
activation and CLI override support, keeping only OS/architecture profiles.
Cross-target builds use the existing explicit platform or `all` dependency.
The new negative metadata fixture checks failure when no platform profile
matches, and consumer receipts now record Maven's version. Validation of that
correction is pending at this checkpoint.

Local checks after removing property-based activation passed: all 55 regression
tests, all five Windows Maven/Gradle consumer cases, the offline negative
metadata fixture, and actionlint for the five Java workflows. A subsequent
message-only change renamed the unavailable classifier to direct users toward
an explicit classifier; all four selector tests passed again. Hosted results
for the corrected implementation remain pending.
