# Proof-checker pending dashboard

Updated: **2026-11-16T02:37:56-08:00**. Goal: eliminate pending proof obligations
and meet or beat the legacy checker on `fstar-build` and SMT-LIB.

**Definition** is the independent checker with definition, NNF and Skolem
replay. **Core** is the same sort-indexed checker without those extensions;
both use a value family indexed by sort, not `Z3ValueTheory.fst`.
**Legacy** uses `Z3ValueTheory.fst`. Counts are for Definition unless stated.

PENDING counts are weighted unresolved proof-rule obligations, not PARTIAL
proofs. Current observed counts appear below; **N/M** means not measured.
Per-rule counts for undiagnosed cases and unobserved timeout tails are N/M,
not zero.

<!-- BEGIN CURRENT PENDING -->
## Current SMT-LIB diagnostic collection

Updated `2026-11-15T23:11:35-08:00`; latest case `2026-11-15T23:11:34-08:00`; checker `245dd5c801e3`. Counts below cover only successful diagnostic results; UNKNOWN, timeouts, errors and unrun cases may hide additional pending obligations.

| Cohort | Latest case | Observed / selected | Diagnostics / observed | Diagnostic errors | ACCEPT | PARTIAL | UNKNOWN | TIMEOUT | SAT | REJECT | Crash / error | NOT_RUN |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| smtlib-sample | `2026-11-15T22:37:19-08:00` | 225 / 225 | 186 / 225 | 0 | 100 | 86 | 20 | 19 | 0 | 0 | 0 | 0 |
| smtlib-extended | `2026-11-15T23:11:34-08:00` | 285 / 285 | 210 / 285 | 0 | 74 | 136 | 68 | 7 | 0 | 0 | 0 | 0 |

| Rule | Sample observed PENDING | Extended observed PENDING |
| --- | ---: | ---: |
| `apply-def` | 203 | 0 |
| `arith/farkas` | 0 | 59 |
| `arith/lp-monomial-interval` | 0 | 46 |
| `arith/lp-monomial-substitute` | 0 | 1 |
| `assumed:nlsat` | 0 | 152 |
| `def-axiom` | 3 | 89 |
| `der` | 6 | 0 |
| `intro-def` | 272 | 164 |
| `quant-intro` | 42 | 83 |
| `rewrite` | 140 | 24789 |
| `th-lemma` | 3499 | 6407 |

State: **stages complete**. Diagnostic errors are excluded from rule totals. Per-case logs, timestamps and pins: session `files\periodic-smtlib-20261116T055834Z`.
<!-- END CURRENT PENDING -->

<!-- BEGIN CURRENT FSTAR PENDING -->
## Current fstar-build diagnostic collection

Updated `2026-11-16T02:31:10-08:00`; latest case `2026-11-16T02:31:10-08:00`; checker `35ef16e3adce`. Counts include observed timeout prefixes only; unobserved proof tails and cases with diagnostic errors may contain additional PENDING.

| Observed / selected | Completed | TIMEOUT | Error / crash | NOT_RUN | Diagnosed proof sessions / observed | Diagnostic errors |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 583 / 583 | 542 | 41 | 0 | 0 | 570 / 583 | 0 |

Observed proofs: **10898 ACCEPT / 377 PARTIAL / 0 UNKNOWN / 0 REJECT**; solver UNKNOWN queries: **452**.

| Rule | Observed PENDING |
| --- | ---: |
| `arith/farkas` | 9 |
| `arith/lp-monomial-interval` | 2 |
| `assumed:nlsat` | 436 |
| `nnf-neg` | 24 |
| `quant-intro` | 42 |
| `rewrite` | 11 |
| `sk` | 18 |
| `th-lemma` | 1079 |

State: **complete**. Per-case evidence and pins: session `files\product-fstar-pending-01`.
<!-- END CURRENT FSTAR PENDING -->

<!-- BEGIN PREVIOUS FSTAR PENDING -->
## Previous complete fstar-build diagnostics

Collected `2026-11-15T21:57:17-08:00`; checker `245dd5c801e3`. All 583 inputs observed: 543 completed, 40 timed out; 570 sessions had proof diagnostics.
Observed proofs: **10,929 ACCEPT / 383 PARTIAL**; 462 solver UNKNOWN queries. Timeout tails and undiagnosed evidence are N/M.

| Rule | Observed PENDING |
| --- | ---: |
| `arith/farkas` | 10 |
| `arith/lp-monomial-interval` | 5 |
| `assumed:nlsat` | 436 |
| `nnf-neg` | 24 |
| `quant-intro` | 45 |
| `rewrite` | 14 |
| `sk` | 20 |
| `th-lemma` | 1,043 |

This is a prior checker snapshot, not an identical-proof burn-down against the live run. Evidence: session `files\current-fstar-pending-01\state.json`.
<!-- END PREVIOUS FSTAR PENDING -->

## Burn-down: matched proofs

Compare only identical frozen proofs and checker versions within each row.
Positive gains mean fewer pending obligations; unmeasured cohorts are not
assumed unchanged.

| Date | Cohort | Rule | Before | After | Newly checked | Remaining |
| --- | --- | --- | ---: | ---: | ---: | ---: |
| Nov 15 | fstar-build, 147 proofs | `rewrite` | 2 | 0 | 2 | 0 |
| Nov 15 | smtlib-sample, 1 ring proof | `th-lemma` | 15 | 0 | 15 | 0 |
| Nov 15 | smtlib-sample, 11 proofs | `rewrite` | 1,039 | 43 | 996 | 43 |
| Nov 15 | smtlib-sample, 11 proofs | all pending | 1,923 | 927 | 996 | 927 |
| Nov 15 | smtlib-sample, 11 proofs | all pending | 927 | 927 | 0 | 927 |
| Nov 15 | smtlib-sample, 11 proofs, array draft | `th-lemma` | 681 | 0 | 681 | 0 |
| Nov 15 | smtlib-sample, 11 proofs, array draft | `rewrite` | 43 | 36 | 7 | 36 |
| Nov 15 | smtlib-sample, 11 proofs, array draft | all pending | 927 | 239 | 688 | 239 |
| Nov 15 | fstar-build, Math.Exp query 7, product draft | `arith/lp-monomial-interval` | 4 | 2 | 2 | 2 |
| Nov 15 | fstar-build, Math.Exp query 7, combined product draft | `arith/lp-monomial-interval` | 4 | 0 | 4 | 0 |
| Nov 16 | fstar-build, Math.Exp query 7, checkout candidate | `arith/lp-monomial-interval` | 4 | 0 | 4 | 0 |
| Nov 16 | fstar-build, CancellableInvariant query 2, division draft | `th-lemma` | 2 | 1 | 1 | 1 |

Checker SHA-256 prefixes: fstar-build `b73878ccdb7d` -> `245dd5c801e3`;
sample ring `702a6993aaac` -> `9c022c1f9f84`; sample rewrite
`9c022c1f9f84` -> `b73878ccdb7d`; pre-array sample row
`b73878ccdb7d` -> `245dd5c801e3`; array draft
`245dd5c801e3` -> `123dfe2cdd80`; product draft
`245dd5c801e3` -> `8bf2b8733eb5`; combined product draft
`245dd5c801e3` -> `2492999310f8`; checkout candidate
`245dd5c801e3` -> `35ef16e3adce`; division draft
`35ef16e3adce` -> `96d0c8a1b994`. The fstar-build change promoted two
PARTIAL proofs to ACCEPT. These are subset results, not full-cohort
burn-downs. Array root certification can discharge obligations without
independently certifying each original entry. Evidence: session
`files\generic-array-sample-weighted-01.json`, `files\large-real-compare-02.json`,
`files\bounds-sample-01.json`, `files\large-real-sample-01.json`,
`files\integer-cut-sample-02.json`, `files\existential-der-measure-01.json`,
`files\real-nonnegative-math-exp-01.json`,
`files\real-greater-one-math-exp-01.json`, `files\real-product-checkout-math-exp-01.json`,
`files\real-division-cancellable-01.json`.
The Math.Exp proof remains PARTIAL with nine other PENDING. The separately
measured drafts are not retained; the product checkout candidate is retained.

## Latest benchmark outcomes

| Dataset / checker | Identical proofs | ACCEPT | PARTIAL |
| --- | ---: | ---: | ---: |
| fstar-build, retained `b73878ccdb7d` | 147 | 144 | 3 |
| fstar-build, product checkout `35ef16e3adce` | 147 | 146 | 1 |
| smtlib-sample, legacy | 11 | 11 | 0 |
| smtlib-sample, retained `245dd5c801e3` | 11 | 1 | 10 |
| smtlib-sample, product checkout `35ef16e3adce` | 11 | 1 | 10 |
| smtlib-sample, unretained array draft `123dfe2cdd80` | 11 | 5 | 6 |

Five alternating pairs gave product-checkout/retained median time ratios
**1.093** on Math.Exp and **0.999** over five sample proofs. The array draft
had ratio **1.96** on five sample proofs and is not retained. These are subset
results, not whole-cohort parity or speedup. Root certification may use an
augmented proof and does not independently certify every original entry.
Evidence: session `files\real-product-checkout-fstar-01.json`,
`files\large-real-fstar-01.json`, `files\large-real-compare-02.json`,
`files\real-product-checkout-sample-01.json`,
`files\real-product-checkout-math-exp-timing-01.json`,
`files\real-product-checkout-sample-subset-timing-01.json`,
`files\generic-array-sample-subset-timing-01.json`.

## Active / next

- Complete pinned per-rule collection; unobserved evidence remains N/M.
- Burn down `th-lemma`, `rewrite` and arithmetic obligations with matched proofs.
  The prior extended snapshot has 59 `arith/farkas` PENDING across six cases.
  One newly frozen proof has five such obligations; three inspected indices
  have unit-coefficient native `arith bound` hints, and two require reasoning
  about multiple zero products. Other causes remain N/M. This is not evidence
  of a faulty linear certificate. A separate capture timed out without a proof.
  Evidence: session `files\extended-farkas-capture-02.json`,
  `files\extended-farkas-capture-01.json`.
- Product checkout passed strict downstream F* verification for 118 modules,
  focused tests, SMT/Python/help smoke checks, and 11 build-scope tests.
  Two POSIX wiring tests were skipped; two finite-field tests and one
  uncovered-binder fixture were excluded. Native shell and test-z3 build and
  `/a` tests passed for the preceding large-Real candidate. Evidence:
  `files\real-greater-one-downstream-01.json`,
  `files\real-product-checkout-build-01.json`,
  `files\real-product-checkout-smoke-01.json`,
  `files\large-real-native-check-01.json`.
- Six-hour SMT-LIB measurements remain scheduled; finite-field work is paused.
  Native stages use the shared lock and a 30-second quiet pause.

## Touched files

| File | Change |
| --- | --- |
| `Z3IndependentRealBounds.fst`, `.fsti` | Verify Real equations |
| `Z3SortedProof.fst` | Replay large equations |
| `tools\test_independent_bounds.ml` | Test rewrite and product guards |
| `Z3IndependentRealNonnegative.fst`, `.fsti` | Prove nonnegative products |
| `Z3IndependentRealGreaterOne.fst`, `.fsti` | Prove products above one |
| `tools\checker_modules.json`, `tools\build_ocaml_checker.ps1` | Register product modules |
| `tools\test_checker_scope.py` | Update module count |
| `PORTING_INSTANCES.csv` | Full-run instance ledger |
| `PORTING_PROGRESS.md` | Pending burn-down dashboard |
