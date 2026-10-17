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
