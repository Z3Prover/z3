# F* Formal-Verification Audits of Z3's Rewriters — Index

This directory contains a series of independent F* audits that
formalize and mechanically verify selected rewrite rules of Z3's
rewriter/converter source files. Each audit defines a self-contained,
abstract (never Z3-internal-type-dependent) value-level theory for its
subject area, proves that the corresponding C++ code's symbolic
rewrite shortcuts are equal to evaluating that theory, and explicitly
documents what was judged out of scope (and why).

Toolchain used throughout: [F*](https://github.com/FStarLang/FStar)
`v2026.09.27` (Windows x64) with Z3 `4.13.3` as the SMT backend (F*
pins an exact Z3 version; this is independent of the Z3 binary built
from this repository). Typecheck any file with:

```
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe <File>.fst
```

All `.fst` files in this directory type-check and discharge all
verification conditions with no `admit`/`assume`/axioms.

## Audits

| Audit | Report | Theory file(s) | Proof file(s) | Subject |
|---|---|---|---|---|
| Sequences | [`SEQ_REPORT.md`](SEQ_REPORT.md) | `Z3SeqTheory.fst` | `Z3SeqRewrites.fst` | `src/ast/rewriter/seq_rewriter.cpp` |
| Floating point | [`FPA_REPORT.md`](FPA_REPORT.md) | `Z3FpaTheory.fst`, `Z3FpaConverter.fst` | `Z3FpaRewrites.fst`, `Z3FpaConverter.fst` | `src/ast/rewriter/fpa_rewriter.cpp`, `src/ast/fpa/fpa2bv_converter.cpp` |

See each linked report for the full scope decision, function-by-function
coverage table, notable results, and remaining gaps for that audit.
