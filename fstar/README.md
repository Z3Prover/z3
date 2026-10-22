# F* Formalization, Source Audits, and Proof Checking

This directory contains three related activities:

| Activity | Purpose | Details and reports |
|---|---|---|
| **1. Formalization of SMT theories** | Define abstract, value-level semantics and mechanically prove theory laws in F*. | [Formalization](FORMALIZATION.md) |
| **2. Neuro-Formal audits of Z3 source code** | Examine selected C++ implementations against the formalized semantics, verify their semantic obligations, and document findings and scope limits. | [Source audits](SOURCE_AUDITS.md) |
| **3. Proof checking of Z3 proofs** | Build verified checkers that validate proof steps and certificates using the formalized semantics and lemmas. | [Proof checking](PROOF_CHECKING.md) |

The formalization is the shared foundation. **Source audits and proof
checking are independent activities**: both depend on the formalization,
but neither depends on the other.

```text
                 1. SMT theory formalization
                          /       \
                         v         v
              2. Source audits   3. Proof checking
```

An audit studies the correctness of selected source-code behavior; a
checker validates an individual proof against supported rules. An audit
does not replace checking a proof, and checking a proof does not establish
correctness of the C++ implementation that produced it. The activity pages
link the relevant modules, reports, coverage results, and limitations.
For the current single-executable SMT-LIB workflow, see
[direct native checking](PROOF_CHECKING.md#extraction-and-execution).
For incremental SMT-LIB sessions, run the built executable with
`--interactive`. It registers the extracted F* checker through Z3's proof
callback and emits `; proof-check ACCEPT`, `PARTIAL n`, or `REJECT` after
UNSAT answers. See [interactive mode](OCAML_CHECKER_REPORT.md#interactive-certifying-smt-lib-session)
for protocol, ownership, and certification limits.

## Shared toolchain

The documented toolchain is [F*](https://github.com/FStarLang/FStar)
`v2026.09.27` (Windows x64). The proof-checker harness builds and installs
Z3 from this checkout before verification or testing. F* and Pulse use
the installed `build\install\bin\z3.exe`, not F*'s historical Z3 4.13.3
backend or an executable found incidentally on `PATH`. The harness reads
the installed version and supplies F*'s matching `--z3version` option;
the version check remains enabled.

From a Windows C++20 developer PowerShell, build and test both the native
checker and the in-memory Pulse checkers:

```powershell
.\tools\build_ocaml_checker.ps1 -RunTests
```

The Windows installation is local to the build directory. The native
OCaml producer is separately built and installed in WSL, then linked
from that installation. See [build options and prerequisites](OCAML_CHECKER_REPORT.md#build-status-and-trust-boundary).

### GitHub Actions regression report

**Pulse verification and native checker regressions**
(`.github/workflows/pulse-checker-regressions.yml`) runs automatically on
pushes and pull requests changing `fstar/**`, and can also be dispatched
manually on a branch containing the checker. Automatic runs use the
default dispatch settings. It builds and installs that checkout's Z3, verifies the Pulse
modules and their tests, extracts and links the native F* checker, and
runs its bridge/CLI self-tests. The Linux path uses the same
`tools/build_ocaml_checker.ps1` module lists as the Windows/WSL build,
with pinned F* `v2026.09.27` and OCaml `5.3.0`.
F* and enabled OCaml compiler warnings fail the build. Extracted constructor
projectors receive explicit rejecting out-of-domain arms using OCaml's
AST, without suppressing partial-match warnings or changing checker rules.

The first default corpus is every `.smt2` file recursively under
`Z3Prover/z3test`'s `regressions/proofs`, including the optional larger
`lean/real` input. Dispatch inputs select the corpus ref/directory, sorted
case cap (zero means all), solver timeout, whole-case timeout, and total
test budget. Manifest `.txt` lists and saved `.proof` objects are not
executed. Inputs are passed unchanged to the native API, which checks the
parsed final assertion set, not an incremental sequence of commands.

The same job also evaluates all **225 inputs** under
`Z3Prover/z3test`'s `regressions/smtlib-sample`: **25 UNSAT-annotated
benchmarks per logic** for QF_UF, QF_AX, QF_LIA, QF_LRA, QF_IDL, QF_UFLIA,
QF_AUFLIA, AUFLIA, and UFLIA. This is a newly reconstructed reduced
seed-42 sample from the official SMT-LIB 2025 non-incremental archives,
not a replay of the historical 900-input manifest. The corpus manifest
records upstream archive checksums, original paths, and each unchanged
input's SHA-256. The harness verifies exact manifest membership and every
input hash before executing any case, and requires exactly 225 inputs.
The proof-corpus `max_cases` cap does not truncate this sample. A manually
selected `z3test_ref` must contain the sample and its manifest.

An independent **110-input extended sample** is bundled under
`fstar/benchmarks/smtlib-sample`: 25 inputs each for **QF_DT, QF_NIA, UF,
and QF_BV**, plus **all 10 UNSAT-annotated UFLRA inputs** in the upstream
release. UFLRA contains only 15 benchmarks total; the other five are
SAT-annotated and are not certificate examples. These unchanged inputs
come from the same SMT-LIB 2025 non-incremental release,
[Zenodo record 16740866](https://zenodo.org/records/16740866), licensed
CC BY 4.0. Original authorship, source, and license metadata are preserved
inside each benchmark. Archive sizes, published MD5 checksums, archive
SHA-256 hashes, original member paths, and input SHA-256 hashes are frozen
in the bundled manifest. Git treats the SMT-LIB files as binary for
checkout purposes to preserve their exact bytes.

Selection considers UNSAT-annotated regular `.smt2` archive members up to
256 KiB each, keeping the checked-in corpus small rather than selecting
by solver outcome. Independently per logic, a Python seed-42 generator
shuffles the sorted member lists within each top-level benchmark family,
then shuffles the sorted family list. Round-robin selection pops one member
per nonempty family until 25 inputs are selected or all families are
exhausted. Thus the small UFLRA population is included in full, rather than
duplicated to reach 25. The manifest records eligible families and counts.
CI downloads no archives and does not resample: it verifies all 110 inputs
before checking them. This step has its own configurable 3600-second
budget, report, and diagnostic replay, and runs independently of the
external z3test checkout. The original 225-input cohort is unchanged.
The five UF `misc/set*.smt2` inputs declare an uninterpreted sort named
`Set`. The shared parser removes obsolete built-in sort aliases when
`set-logic` follows API context initialization, leaving this name available
under UF. All five previously failing inputs now certify as `ACCEPT`;
regressions cover native batch and interactive checking.

The job summary and downloadable report artifact record resolved producer
and corpus commits, build/test outcomes, build and per-case wall time,
available solve/marshal/check timings, and explicit outcome rates.
`ACCEPT` alone counts as proof-checking success; `PARTIAL`, `REJECT`,
`SAT`, unknowns, timeouts, and process errors remain separate categories.
The report is a coverage measurement, not a pass rate for z3test's other
proof backends. Pulse modules are verified, but the executable benchmarked
on the corpus uses the extracted F* kernel, **not linked Pulse code**.
Build/self-test failures and checker errors/crashes/protocol mismatches
fail the job; unsupported proofs and timeouts are reported without failing
this coverage-measurement job. The corpus step also has a 35-minute CI
limit, independent of the configurable budget. Always-run reporting/upload
steps preserve available results and build logs on failure.
After coverage measurement, a separately budgeted diagnostic pass replays
only `PARTIAL` and `REJECT` cases with `--diagnostics`. It does not change
the original verdicts or case timings. Reports rank remaining rule/fingerprint
families by sole-family proofs blocked, then affected proofs and obligation
counts; only replays matching the original verdict and pending count
contribute. Raw replay logs and `diagnostics.jsonl` retain timeouts,
nonmatching results, and diagnostic errors separately. Each corpus has a
900-second diagnostic budget and twice its original whole-case timeout.
The SMT-LIB sample has its own report, per-logic outcome counts, input
manifest, raw logs, and phase timings under the artifact's `smtlib-sample/`
directory. It uses the same configurable solver and whole-case timeouts,
a 4 GiB address-space limit, and a separate default 3,600-second execution
budget (`smtlib_total_timeout_seconds`), with a 65-minute CI step limit.
An incomplete manifest-driven sample run fails the job; unsupported
proofs and timeouts still remain explicit coverage outcomes. The sample
step runs even if the earlier proof-corpus execution fails, provided the
build and corpus checkout succeeded.

For a local Linux build, activate an OCaml 5.3.0 opam switch with
`ocamlfind` and `zarith`, then run the same harness with `pwsh`,
`-FstarExe /path/to/fstar.exe`, `-OpamSwitch <switch>`, and `-RunTests`.
On Linux, `-Z3WindowsBuildDir` names the local CMake build directory and
`-WslBuildDir` names the local checker output directory; WSL is not used.
That one Z3 installation supplies both the verifier and the native link.

After the harness has installed Z3, a standalone module can use it explicitly:

```powershell
$z3 = Join-Path (Resolve-Path '..') 'build\install\bin\z3.exe'
$version = [regex]::Match((& $z3 -version), 'Z3 version (\d+\.\d+\.\d+)').Groups[1].Value
C:\fstar\fstar\bin\fstar.exe --smt $z3 --z3version $version --include $PWD Z3AstTheory.fst
```

Consult each report for its verification results, assumptions, and scope.
In particular, [`Z3NlArith.fst`](Z3NlArith.fst) uses nine explicitly
labeled real-analysis assumptions about `exp`/`log`/`sin`/`cos`/`atan2`;
see the [non-linear arithmetic report](NL_ARITH_REPORT.md).
[`Z3Native.fsti`](Z3Native.fsti) separately declares the foreign Z3 API
boundary; its implementation is trusted native interoperability, not an
arithmetic or proof-validity axiom. The [arithmetic certificate
report](ARITHMETIC_CERTIFICATE_REPORT.md) documents the remaining
semantic-model contract limitation; the current checker is not an
unconditional end-to-end SMT-LIB soundness proof.
