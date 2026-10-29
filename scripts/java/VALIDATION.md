# Java packaging evidence

This records experiments for an upstream contribution. It does not establish an
official Maven release or platform coverage beyond the rows below.

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
