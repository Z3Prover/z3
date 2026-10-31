# F* Formalization, Source Audits, and Proof Checking

This directory contains three related activities:

| Activity | Purpose | Details and reports |
|---|---|---|
| **1. Formalization of SMT theories** | Define abstract, value-level semantics and mechanically prove theory laws in F*. | [Formalization](FORMALIZATION.md) |
| **2. Neuro-Formal audits of Z3 source code** | Examine selected C++ implementations against the formalized semantics, verify their semantic obligations, and document findings and scope limits. | [Source audits](SOURCE_AUDITS.md) |
| **3. Proof checking of Z3 proofs** | Build verified checkers that validate proof steps and certificates using the formalized semantics and lemmas. | [Proof checking](PROOF_CHECKING.md); [technical report](TECHNICAL_CHECKER_REPORT.md) ([LaTeX source](TECHNICAL_CHECKER_REPORT.tex)) |

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
`v2026.10.25` (Windows x64). The proof-checker harness builds and installs
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

### Standalone Cherry checker

The native checker also has a **Cherry-generated C kernel and C++ frontend**,
with no OCaml runtime or OCaml bindings. It extracts the same
`Z3NativeProof` marshaler, document checker, and sort-indexed datatype checker.
The handwritten C++ foreign adapter supplies Z3 handles and candidate proof
metadata; it cannot construct checked facts. Both executables link static Z3
and solve, marshal, and check in process. Their input options, incremental
protocol, diagnostics, and exit codes are the same.

Cherry currently requires **Linux x86-64 or AArch64, GCC/G++ 15+**, and a
Cherry-capable F*. CI pins **nightly-2026-10-30**, commit
`c68959fe1f070cd66a5ed2e92965185505f109ce`, separately from the OCaml verifier.
`tools/checker_modules.json` supplies the dependency-ordered shared module and
test lists to both build paths. Its `cherry_modules` list names Cherry-only
implementations, such as `Z3IdTable-c.cherry.fst` (the proof-id caches as
immutable arrays instead of `Z3IdTable.fst`'s binary trie), which F* selects
over the default implementation when generating Cherry code. Every source is
verified before extraction; the installed checkout Z3 is explicitly selected as
the SMT backend.

To add Cherry to the existing Windows/WSL or Linux build, pass
`-BuildCherry -CherryFstarExe <Linux-path-to-fstar.exe>` to
`tools/build_ocaml_checker.ps1`. On Windows, this is a WSL executable path;
use `-WslDistribution Ubuntu` when necessary. The second executable is
`<WslBuildDir>/cherry/checker`. `-RunTests` exercises both backends.

A Cherry-only Linux build does not require opam or OCaml. After installing
static Z3 from this checkout, run:

```sh
python3 fstar/tools/build_cherry_checker.py \
  --fstar /path/to/fstar/bin/fstar.exe \
  --z3-install /path/to/z3/install \
  --build-dir /path/to/cherry-checker --run-tests
/path/to/cherry-checker/checker --stats input.smt2
```

The installed prefix must contain `bin/z3`, `include/z3.h`, and `lib/libz3.a`.
Use `--sanitize` for an ASan/UBSan build. The generated kernel retains Cherry
debug checks and guaranteed tail calls; neither verification nor runtime
safety checks are disabled. `Z3CherryTests` and native bridge tests exercise
accepted, unsupported, and malformed proof documents, including mismatched
original assertions. The shared CLI suite covers batch and interactive
checking, clause proofs, datatypes, arrays, bit-vectors, exact arithmetic,
timeouts, diagnostics, and input errors.

The datatype shape witness uses a non-erased Boolean carrier to avoid a
reproduced nightly compiler bug in reference-counting unit-valued closures,
reported as **FStarLang/FStar#4783**. The inhabitance algorithm and all its
proof obligations remain verified.

### GitHub Actions regression report

**Build Pulse native checkers** (`.github/workflows/pulse-checker-build.yml`)
runs automatically on pushes and pull requests changing `fstar/**` or either
checker workflow, and can also be dispatched manually. It builds and installs
that checkout's Z3, verifies the Pulse modules and their tests, extracts and
links the native F* checker, and
runs both executables' bridge/CLI self-tests. The Linux path uses the same
`tools/checker_modules.json` lists as the Windows/WSL build,
with pinned F* `v2026.10.25` and OCaml `5.3.0` for the OCaml executable,
and the separately pinned nightly and GCC/G++ 15 for Cherry.
F* and enabled OCaml compiler warnings fail the build. The OCaml checker is
extracted in one whole-program Custard run (`--codegen OCaml --custard_split`)
and linked in `ocamldep -sort` order; a call outside a refinement's domain
raises `Match_failure` rather than returning a value.

It also runs after a successful default-branch **Nightly Build**, building that
nightly's exact source commit rather than the latest branch tip. On success,
an isolated publication job attaches both checker tarballs and their SHA-256
files to the GitHub release tagged **`Nightly`**. Publication is serialized with
the nightly deploy and skipped explicitly if that release has advanced to a
different commit. PR, push, and manual checker builds never modify the release.

Successful builds upload **`pulse-checker-ocaml-linux-x86_64`**,
**`pulse-checker-cherry-linux-x86_64`**, and **`pulse-checker-build-report`**.
Each checker artifact contains a checksummed `.tar.gz` with an executable `checker`,
build/toolchain metadata, runtime-library dependencies, licenses, and usage
instructions. Extract the tarball to preserve executable permissions.
Neither executable needs a build-time F* or OCaml installation, an external
`z3`, or Python to run. Standard Linux shared libraries are still required;
the OCaml binary also requires `libgmp.so.10`. Both packages are smoke-tested
with a clean environment.

Successful completion triggers **Pulse verification and native checker regressions**
(`.github/workflows/pulse-checker-regressions.yml`) through `workflow_run`.
It downloads the packages and build report from that exact build run and
checks out the source revision recorded in the build artifact, including for
nightly-triggered builds; it does not rebuild Z3, F*, or either checker.
The consumer has only read permissions, including for PR builds, and no secrets
are passed to the downloaded executables. Failed or cancelled builds do not
start regression jobs. The regression workflow must be on the default branch
for GitHub to deliver the completion trigger. For a manual regression run,
provide the successful producer's `build_run_id` along with any corpus or
timeout overrides. Automatic runs use the default regression settings.

The first regression job downloads the OCaml package and reruns the CLI suite.
A second job downloads the Cherry package from the same build, reruns
the CLI suite without installing build toolchains, then replays the same
z3test commit and the **identical 225/285 sampled inputs, 300 fixed QF_BV inputs,
and 25 QF_FF inputs**
from the OCaml report artifact. It does not download the Zenodo archives again.
Cherry coverage and timing reports are published separately.
These executables run the extracted F* document-checker kernel; the
in-memory Pulse checker regressions are also verified during the build,
not substituted for the document-checker CLI.

The first default corpus is every `.smt2` file recursively under
`Z3Prover/z3test`'s `regressions/proofs`, including the optional larger
`lean/real` input. Dispatch inputs select the corpus ref/directory, sorted
case cap (zero means all), solver timeout, whole-case timeout, and total
test budget. Manifest `.txt` lists and saved `.proof` objects are not
executed. Inputs are passed unchanged to the native API, which checks the
parsed final assertion set, not an incremental sequence of commands.

The same job also evaluates two freshly sampled SMT-LIB cohorts:
**225 inputs**, with **25 UNSAT-annotated benchmarks per logic** for QF_UF,
QF_AX, QF_LIA, QF_LRA, QF_IDL, QF_UFLIA, QF_AUFLIA, AUFLIA, and UFLIA;
and **285 extended inputs**, with 25 each for **QF_DT, QF_NIA, UF,
QF_UFBV, QF_UFDT, QF_ABV, QF_AUFBV, QF_UFLRA, QF_NRA,
UFDT, and UFDTLIA** plus **all 10 UNSAT-annotated UFLRA inputs**.
UFLRA has only 15 benchmarks total; its five SAT-annotated inputs are not
certificate examples. QF_LIRA is omitted because the pinned archive supplies
only two eligible UNSAT inputs under the size limit. QF_UFDTLIA is omitted
because its archive contains only unknown-annotated inputs.
CI skips QF_BV during archive sampling because its large archive repeatedly
times out; a separate fixed QF_BV cohort is checked out from z3test instead.
The existing manifests in `Z3Prover/z3test/regressions/smtlib-sample`
and `fstar/benchmarks/smtlib-sample` now supply the archive URLs, pinned
SHA-256 hashes, compressed sizes, and required counts, not the CI input
lists. A manually selected `z3test_ref` must contain its source manifest.
The checked-in fixed cohorts remain available for local regression replay.
Both sampled cohorts come from the SMT-LIB 2025 non-incremental release,
[Zenodo record 16740866](https://zenodo.org/records/16740866), licensed
CC BY 4.0. Original authorship, source, and license metadata are preserved
inside each unchanged benchmark.

`tools/sample_checker_benchmarks.py` downloads and verifies one archive at
a time, streams decompression without unpacking the complete corpus, and
keeps only the requested number of candidates in memory. Eligible inputs
are regular UNSAT-annotated `.smt2` members of at most 256 KiB. Independently
per logic, selection takes the lowest SHA-256 priorities of
`seed NUL logic NUL relative-POSIX-path`. This is pseudorandom sampling
without replacement, independent of archive traversal order, and does not
select by solver or checker outcome. It is stratified by logic, not by
benchmark family. Unsafe paths, links, duplicates, incorrect archive
hashes, and insufficient eligible populations fail preparation explicitly.

The default seed is `github.run_id`: new runs use different seeds, while
rerunning the same workflow run retains its seed. Dispatch input
`smtlib_sample_seed` reproduces a recorded selection against the same archive
configuration and sampler. UFLRA necessarily remains the same ten inputs. The two
cohorts retain their separate execution/diagnostic budgets and require
exactly 225/285 manifested inputs; `max_cases` does not truncate them.
The extended cohort remains independent of the external z3test checkout.
Each report artifact includes `inputs/` with the selected original files
and manifest, the seed, source-manifest hash, archive/member provenance,
input SHA-256 hashes, and `sampling.log`. The harness verifies exact
manifest membership and every input hash before executing any case.

A fixed **300-input QF_BV cohort** comes from the checked-out z3test's
`regressions/smtlib-qfbv` directory. All inputs retain their upstream UNSAT
annotations and original bytes, are at most **8 KiB**, and have distinct hashes.
They were selected once from the pinned SMT-LIB 2025 QF_BV archive using the
lowest SHA-256 priorities with fixed seed `pulse-qfbv-300-v1`, without using
solver or checker results. The manifest records the archive provenance, size
bound, member paths, and every input hash. Both backends replay the same fixed
300 files; neither downloads QF_BV from Zenodo in CI. These inputs are not
rotated by `smtlib_sample_seed` or truncated by `max_cases`. A manual
`z3test_ref` must include this directory. The cohort has a separate
`qfbv_total_timeout_seconds` execution budget.

A separate **25-input QF_FF cohort** uses the checked-out z3test's
`regressions/finite_field/test_qfff.py` generator and exhaustive small-field
oracle. It selects five distinct UNSAT formulas for each prime 2, 3, 5, 7,
and 17, covering the generator's field arithmetic, bitsums, conditionals,
equalities, disequalities, and Boolean combinations. Selection uses the
same recorded run seed, not solver or checker results. Generation fails
if it cannot supply every case. Its manifest records the z3test revision,
generator hash, moduli, and individual input hashes. Both backends run
these exact inputs with the normal certificate harness; unsupported proof
steps remain visible as PARTIAL rather than solver-only passes.
The `qfff/` report includes generated inputs, provenance, per-case logs,
coverage, timings, and separate diagnostics. Dispatch input
`qfff_total_timeout_seconds` controls its execution budget (default 600
seconds); the other per-case limits are shared with the existing cohorts.

This is a normal GitHub-hosted Actions job, not a gh-aw agent job with a
network allowlist. `permissions: contents: read` limits GitHub API access,
not public outbound HTTPS; anonymous Zenodo downloads need no additional
token permission. The pinned archives total about 4.17 GB compressed per
run. Preparation has a separate 30-minute limit for each cohort; archive
downloads are bounded and retried, and each archive is removed after
sampling. Zenodo may still be unavailable or rate-limit a runner, in which
case the workflow reports a sampling failure rather than silently reusing
the fixed cohort.

For environments that cannot reach Zenodo, an alternative preparation
step can sample from a larger checksummed snapshot hosted in z3test, a
GitHub Release, or a pre-provisioned runner cache. Refresh that pool
separately, record its version and the seed, and produce the same input
manifest for the existing validation/diagnostic steps. The pool must be
larger than the per-run cohort: drawing 25 out of the same 25 files changes
only execution order, not benchmark coverage.

The bundled UF regression cohort includes five `misc/set*.smt2` inputs
declaring an uninterpreted sort named `Set`. The shared parser removes
obsolete built-in sort aliases when `set-logic` follows API context
initialization, leaving this name available under UF. All five previously
failing inputs certify as `ACCEPT`; regressions cover native batch and
interactive checking.

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
this coverage-measurement job. In particular, checker exit code 1 with `REJECT`
and exit code 3 with `PARTIAL n` are non-fatal coverage outcomes, not successful
proof checks. The harness still exits nonzero for infrastructure/protocol errors
or unfinished manifested cohorts; its exit code is not ignored.
The corpus step also has a 35-minute CI
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
