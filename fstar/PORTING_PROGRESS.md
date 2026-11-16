# Proof-checker pending dashboard

Updated: **2026-11-16T00:57:41-08:00**. Goal: eliminate pending proof obligations
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

Updated `2026-11-16T00:57:41-08:00`; latest case `2026-11-16T00:57:41-08:00`; checker `35ef16e3adce`. Counts include observed timeout prefixes only; unobserved proof tails and cases with diagnostic errors may contain additional PENDING.

| Observed / selected | Completed | TIMEOUT | Error / crash | NOT_RUN | Diagnosed proof sessions / observed | Diagnostic errors |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 117 / 583 | 116 | 1 | 0 | 466 | 114 / 117 | 0 |

Observed proofs: **2549 ACCEPT / 64 PARTIAL / 0 UNKNOWN / 0 REJECT**; solver UNKNOWN queries: **30**.

| Rule | Observed PENDING |
| --- | ---: |
| `assumed:nlsat` | 7 |
| `nnf-neg` | 2 |
| `quant-intro` | 2 |
| `rewrite` | 1 |
| `sk` | 2 |
| `th-lemma` | 107 |

State: **stage complete**. Per-case evidence and pins: session `files\product-fstar-pending-01`.
<!-- END CURRENT FSTAR PENDING -->

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

Checker SHA-256 prefixes: fstar-build `b73878ccdb7d` -> `245dd5c801e3`;
sample ring `702a6993aaac` -> `9c022c1f9f84`; sample rewrite
`9c022c1f9f84` -> `b73878ccdb7d`; pre-array sample row
`b73878ccdb7d` -> `245dd5c801e3`; array draft
`245dd5c801e3` -> `123dfe2cdd80`; product draft
`245dd5c801e3` -> `8bf2b8733eb5`; combined product draft
`245dd5c801e3` -> `2492999310f8`; checkout candidate
`245dd5c801e3` -> `35ef16e3adce`. The fstar-build change promoted two
PARTIAL proofs to ACCEPT. These are subset results, not full-cohort
burn-downs. Array root certification can discharge obligations without
independently certifying each original entry. Evidence: session
`files\generic-array-sample-weighted-01.json`, `files\large-real-compare-02.json`,
`files\bounds-sample-01.json`, `files\large-real-sample-01.json`,
`files\integer-cut-sample-02.json`, `files\existential-der-measure-01.json`,
`files\real-nonnegative-math-exp-01.json`,
`files\real-greater-one-math-exp-01.json`, `files\real-product-checkout-math-exp-01.json`.
The Math.Exp proof remains PARTIAL with nine other PENDING. The separately
measured drafts are not retained; the checkout candidate is retained.

## Latest benchmark outcomes

| Dataset / checker | Coverage | ACCEPT | PARTIAL | Solver UNKNOWN | TIMEOUT | REJECT / crash / error | NOT_RUN |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| fstar-build, previous full-run Definition `d87b731ba6aa` | 583 inputs | 10,774 proofs | 382 proofs | 443 | 45 sessions | 0 | 0 inputs |
| fstar-build, frozen retained | 147 proofs | 144 | 3 | 0 | 0 | 0 | 0 |
| fstar-build, frozen candidate | 147 proofs | 146 | 1 | 0 | 0 | 0 | 0 |
| fstar-build, unretained array draft `123dfe2cdd80` | 147 proofs | 146 | 1 | 0 | 0 | 0 | 0 |
| fstar-build, unretained product draft `8bf2b8733eb5` | 147 proofs | 146 | 1 | 0 | 0 | 0 | 0 |
| fstar-build, combined product draft `2492999310f8` | 147 proofs | 146 | 1 | 0 | 0 | 0 | 0 |
| fstar-build, retained product checkout `35ef16e3adce` | 147 proofs | 146 | 1 | 0 | 0 | 0 | 0 |
| smtlib-sample, frozen legacy | 11 proofs | 11 | 0 | 0 | 0 | 0 | 0 |
| smtlib-sample, retained Definition `245dd5c801e3` | 11 proofs | 1 | 10 | 0 | 0 | 0 | 0 |
| smtlib-sample, unretained array draft `123dfe2cdd80` | 11 proofs | 5 | 6 | 0 | 0 | 0 | 0 |
| smtlib-sample, unretained product draft `8bf2b8733eb5` | 11 proofs | 1 | 10 | 0 | 0 | 0 | 0 |
| smtlib-sample, combined product draft `2492999310f8` | 11 proofs | 1 | 10 | 0 | 0 | 0 | 0 |
| smtlib-sample, retained product checkout `35ef16e3adce` | 11 proofs | 1 | 10 | 0 | 0 | 0 | 0 |

Full fstar-build proof counts include timed-out session prefixes; its solver
UNKNOWN count is query-level. Current SMT-LIB outcomes and checker pin are in the live collection above. Legacy parity and
whole-corpus performance remain unestablished. Evidence: session
`files\periodic-smtlib-state.json`, `files\large-real-fstar-01.json`.
The product draft preserved all verdicts on 147 matched fstar-build and 11
sample proofs. On five selected sample proofs, five alternating pairs per
proof gave a median candidate/retained time ratio of **0.998** (per-proof
medians 0.96–1.005); this is not a full-cohort measurement. Evidence:
`files\real-nonnegative-fstar-01.json`, `files\real-nonnegative-sample-01.json`,
`files\real-nonnegative-sample-subset-timing-01.json`.
The combined draft preserved all 147 matched fstar-build and 11 sample
verdicts. Five alternating pairs gave median candidate/retained time ratios
of **1.09** on the separate Math.Exp proof and **1.022** across five selected
sample proofs (per-proof medians 1.004–1.046). Neither is a full-cohort measurement.
The checkout candidate's median ratios were **1.093** on Math.Exp and
**0.999** over five selected sample proofs (per-proof medians 0.991–1.094).
Evidence: `files\real-greater-one-fstar-01.json`,
`files\real-greater-one-sample-01.json`, `files\real-greater-one-math-exp-timing-01.json`,
`files\real-greater-one-sample-subset-timing-01.json`,
`files\real-product-checkout-math-exp-timing-01.json`,
`files\real-product-checkout-sample-subset-timing-01.json`.
The array draft promoted four matched sample proofs without a verdict
regression; on 147 matched fstar-build proofs it changed no verdicts.
On five selected sample proofs, five alternating paired runs per proof gave
a median candidate/retained time ratio of **1.96** (per-proof medians
0.996–2.04); this is not a full-cohort measurement. The draft is not promoted.
On those 147 fstar-build proofs, weighted PENDING was unchanged at 6:
`nnf-neg` 1, `quant-intro` 4 and `sk` 1; no verdicts were unobserved.
Root certification need not independently certify each original proof entry.
Evidence: session `files\generic-array-sample-01.json`,
`files\generic-array-fstar-01.json`, `files\generic-array-fstar-pending-01.json`,
`files\generic-array-sample-subset-timing-01.json`.

## Active / next

- **Collect current per-rule totals** for all three datasets using pinned
  inputs and checker, recording diagnostic coverage, timeouts and unobserved
  tails. Add comparable snapshots here; do not treat missing data as zero.
- **Burn down `th-lemma` and `rewrite`**, alternating fstar-build and sample;
  investigate unsupported Farkas, integer-cut and interval evidence at its
  producer before changing replay.
- **Arithmetic evidence:** two frozen `arith/bound` examples require
  nonlinear reasoning; they do not establish faulty linear Farkas certificates.
  Current producer code exports flattened bound parameters but attempts
  structured LP evidence for conflicts. The previous extended snapshot has
  59 Farkas PENDING across six cases (57 QF_NIA, 2 QF_NRA); their individual
  causes are N/M. Evidence: `files\commmonoid-bound-obligations-01.json`,
  `files\periodic-smtlib-20261116T055834Z`.
- **Candidate validation:** strict F* kernel and downstream verification,
  focused tests and SMT/Python/help smoke tests passed. Two known finite-field
  tests and one known uncovered-binder fixture were excluded from the checker
  build. Native `shell` / `test-z3` build and `/a` unit tests passed.
  Evidence: session `files\large-real-build-02.json`,
  `files\large-real-native-check-01.json`.
- **Product checkout:** strict downstream verification passed for 118
  modules; checkout build and focused tests passed with the exclusions above.
  The checkout candidate preserved all 147 matched fstar-build and 11 sample
  verdicts; SMT, Python and help smoke checks passed. Eleven build-scope tests
  passed; two POSIX PowerShell wiring tests were skipped. Evidence:
  `files\real-greater-one-downstream-01.json`, `files\real-product-checkout-build-01.json`,
  `files\real-product-checkout-fstar-01.json`, `files\real-product-checkout-sample-01.json`,
  `files\real-product-checkout-smoke-01.json`.
- **Six-hour SMT-LIB measurement** remains scheduled; finite-field work is
  paused. All native work uses the shared lock and a 30-second quiet pause.

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
