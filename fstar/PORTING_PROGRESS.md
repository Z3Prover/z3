# Proof-checker pending dashboard

Updated: **2026-11-15T23:36:11-08:00**. Goal: eliminate pending proof obligations
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

Updated `2026-11-15T21:57:17-08:00`; latest case `2026-11-15T21:57:17-08:00`; checker `245dd5c801e3`. Counts include observed timeout prefixes only; unobserved proof tails and cases with diagnostic errors may contain additional PENDING.

| Observed / selected | Completed | TIMEOUT | Error / crash | NOT_RUN | Diagnosed proof sessions / observed | Diagnostic errors |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 583 / 583 | 543 | 40 | 0 | 0 | 570 / 583 | 0 |

Observed proofs: **10929 ACCEPT / 383 PARTIAL / 0 UNKNOWN / 0 REJECT**; solver UNKNOWN queries: **462**.

| Rule | Observed PENDING |
| --- | ---: |
| `arith/farkas` | 10 |
| `arith/lp-monomial-interval` | 5 |
| `assumed:nlsat` | 436 |
| `nnf-neg` | 24 |
| `quant-intro` | 45 |
| `rewrite` | 14 |
| `sk` | 20 |
| `th-lemma` | 1043 |

State: **complete**. Per-case evidence and pins: session `files\current-fstar-pending-01`.
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

Checker SHA-256 prefixes: fstar-build `b73878ccdb7d` -> `245dd5c801e3`;
sample ring `702a6993aaac` -> `9c022c1f9f84`; sample rewrite
`9c022c1f9f84` -> `b73878ccdb7d`; pre-array sample row
`b73878ccdb7d` -> `245dd5c801e3`; array draft
`245dd5c801e3` -> `123dfe2cdd80`. The fstar-build change promoted two
PARTIAL proofs to ACCEPT. These are subset results, not full-cohort
burn-downs. Array root certification can discharge obligations without
independently certifying each original entry. Evidence: session
`files\generic-array-sample-weighted-01.json`, `files\large-real-compare-02.json`,
`files\bounds-sample-01.json`, `files\large-real-sample-01.json`,
`files\integer-cut-sample-02.json`, `files\existential-der-measure-01.json`.

## Latest benchmark outcomes

| Dataset / checker | Coverage | ACCEPT | PARTIAL | Solver UNKNOWN | TIMEOUT | REJECT / crash / error | NOT_RUN |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| fstar-build, previous full-run Definition `d87b731ba6aa` | 583 inputs | 10,774 proofs | 382 proofs | 443 | 45 sessions | 0 | 0 inputs |
| fstar-build, frozen retained | 147 proofs | 144 | 3 | 0 | 0 | 0 | 0 |
| fstar-build, frozen candidate | 147 proofs | 146 | 1 | 0 | 0 | 0 | 0 |
| fstar-build, unretained array draft `123dfe2cdd80` | 147 proofs | 146 | 1 | 0 | 0 | 0 | 0 |
| smtlib-sample, frozen legacy | 11 proofs | 11 | 0 | 0 | 0 | 0 | 0 |
| smtlib-sample, retained Definition `245dd5c801e3` | 11 proofs | 1 | 10 | 0 | 0 | 0 | 0 |
| smtlib-sample, unretained array draft `123dfe2cdd80` | 11 proofs | 5 | 6 | 0 | 0 | 0 | 0 |

Full fstar-build proof counts include timed-out session prefixes; its solver
UNKNOWN count is query-level. Current SMT-LIB outcomes and checker pin are in the live collection above. Legacy parity and
whole-corpus performance remain unestablished. Evidence: session
`files\periodic-smtlib-state.json`, `files\large-real-fstar-01.json`.
The array draft promoted four matched sample proofs without a verdict
regression; on 147 matched fstar-build proofs it changed no verdicts.
On five selected sample proofs, five alternating paired runs per proof gave
a median candidate/retained time ratio of **1.96** (per-proof medians
0.996–2.04); this is not a full-cohort measurement. The draft is not promoted.
The fstar-build weighted comparison is pending.
Root certification need not independently certify each original proof entry.
Evidence: session `files\generic-array-sample-01.json`,
`files\generic-array-fstar-01.json`,
`files\generic-array-sample-subset-timing-01.json`.

## Active / next

- **Collect current per-rule totals** for all three datasets using pinned
  inputs and checker, recording diagnostic coverage, timeouts and unobserved
  tails. Add comparable snapshots here; do not treat missing data as zero.
- **Burn down `th-lemma` and `rewrite`**, alternating fstar-build and sample;
  investigate unsupported Farkas, integer-cut and interval evidence at its
  producer before changing replay.
- **Candidate validation:** strict F* kernel and downstream verification,
  focused tests and SMT/Python/help smoke tests passed. Two known finite-field
  tests and one known uncovered-binder fixture were excluded from the checker
  build. Native `shell` / `test-z3` build and `/a` unit tests passed.
  Evidence: session `files\large-real-build-02.json`,
  `files\large-real-native-check-01.json`.
- **Six-hour SMT-LIB measurement** remains scheduled; finite-field work is
  paused. All native work uses the shared lock and a 30-second quiet pause.

## Touched files

| File | Change |
| --- | --- |
| `Z3IndependentRealBounds.fst`, `.fsti` | Verify Real equations |
| `Z3SortedProof.fst` | Replay large equations |
| `tools\test_independent_bounds.ml` | Test rewrite guards |
| `PORTING_INSTANCES.csv` | Full-run instance ledger |
| `PORTING_PROGRESS.md` | Pending burn-down dashboard |
