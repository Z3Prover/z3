# Java packaging evidence

This records experiments for an upstream contribution. It does not establish an
official Maven release or platform coverage beyond the rows below.

## Packaging Test CI

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

## Local checks

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

## Full Flow

[Current-source run](https://github.com/nieyuanhong/z3/actions/runs/40814912126)
passed at `72bf314c711acb75e0796195a1bce2b64c914f6f`: all three native build
jobs, the separate package job and all three final smoke jobs succeeded.
Linux x64, Windows x64 and macOS arm64 built the current 5.3.3 source; their
packaged native version was checked as `5.3.3.0` on Java 17. The package job
downloaded only these same-run artifacts, verified their identities and hashes,
and assembled the final JARs without native compilation or external binary
downloads. Follow-up documentation commits do not change the tested code.

Official coordinates, sources/Javadoc companions, signing, a Central publishing
owner and an authorized release gate remain future work. Nothing here publishes
to GitHub Releases, GitHub Packages, Maven Central, NuGet or PyPI.
