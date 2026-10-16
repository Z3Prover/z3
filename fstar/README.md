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
`v2026.09.27` (Windows x64), with Z3 `4.13.3` as its SMT backend.
F* pins an exact Z3 version; this is independent of the Z3 binary built
from this repository or used to produce proofs for checking.

From this directory, typecheck a module with:

```powershell
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe --include C:\z3\fstar <File>.fst
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
