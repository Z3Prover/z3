# Proof-checker pending dashboard

Updated: **2026-11-16T09:54:19-08:00**. Goal: eliminate pending proof obligations
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

Updated `2026-11-16T08:08:20-08:00`; latest case `2026-11-16T08:08:19-08:00`; checker `98ecf978a307`. Counts below cover only successful diagnostic results; UNKNOWN, timeouts, errors and unrun cases may hide additional pending obligations.

| Cohort | Latest case | Observed / selected | Diagnostics / observed | Diagnostic errors | ACCEPT | PARTIAL | UNKNOWN | TIMEOUT | SAT | REJECT | Crash / error | NOT_RUN |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| smtlib-sample | `2026-11-16T07:37:29-08:00` | 225 / 225 | 186 / 225 | 0 | 100 | 86 | 20 | 19 | 0 | 0 | 0 | 0 |
| smtlib-extended | `2026-11-16T08:08:19-08:00` | 285 / 285 | 209 / 285 | 0 | 74 | 135 | 69 | 7 | 0 | 0 | 0 | 0 |

| Rule | Sample observed PENDING | Extended observed PENDING |
| --- | ---: | ---: |
| `apply-def` | 203 | 0 |
| `arith/farkas` | 0 | 20 |
| `arith/lp-monomial-interval` | 0 | 40 |
| `assumed:nlsat` | 0 | 146 |
| `def-axiom` | 3 | 89 |
| `der` | 6 | 0 |
| `intro-def` | 272 | 139 |
| `quant-intro` | 42 | 83 |
| `rewrite` | 140 | 24692 |
| `th-lemma` | 3499 | 6238 |

State: **stages complete**. Diagnostic errors are excluded from rule totals. Per-case logs, timestamps and pins: session `files\periodic-smtlib-20261116T150132Z`.
<!-- END CURRENT PENDING -->

<!-- BEGIN CURRENT FSTAR PENDING -->
## Current fstar-build diagnostic collection

Updated `2026-11-16T09:21:47-08:00`; latest case `2026-11-16T09:21:47-08:00`; checker `98ecf978a307`. Counts include observed timeout prefixes only; unobserved proof tails and cases with diagnostic errors may contain additional PENDING.

| Observed / selected | Completed | TIMEOUT | Error / crash | NOT_RUN | Diagnosed proof sessions / observed | Diagnostic errors |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 583 / 583 | 543 | 40 | 0 | 0 | 570 / 583 | 0 |

Observed proofs: **10906 ACCEPT / 348 PARTIAL / 0 UNKNOWN / 0 REJECT**; solver UNKNOWN queries: **472**.

| Rule | Observed PENDING |
| --- | ---: |
| `arith/farkas` | 6 |
| `arith/lp-monomial-interval` | 2 |
| `assumed:nlsat` | 376 |
| `nnf-neg` | 24 |
| `quant-intro` | 43 |
| `rewrite` | 8 |
| `sk` | 18 |
| `th-lemma` | 977 |

State: **complete**. Per-case evidence and pins: session `files\multiple-zero-fstar-pending-01`.
<!-- END CURRENT FSTAR PENDING -->

## Last 10 incremental improvements

Refresh this rolling timeline on every dashboard update; retain existing rows
when no new improvement has been measured. Times are evidence-file completion
or last-modified times in PST. Counts are for the specified frozen proofs, not
whole cohorts; overlapping candidate gains must not be added.

| Time (PST) | Improvement and scope | Measured effect | Evidence in session `files\` |
| --- | --- | --- | --- |
| Nov 16 09:52 | Guarded Int quotient draft, fstar-build, UInt128, 1 proof; **not retained** | Root `th-lemma` +63 / 136 PENDING | `int-quotient-uint128-01.json` |
| Nov 16 05:27 | Multi-zero products, extended, 1 proof | `arith/farkas` +2 / 3 PENDING; `th-lemma` +2 / 5 PENDING | `multiple-zero-extended-02.json` |
| Nov 16 03:12 | Guarded Real division, fstar-build, Math.Exp query 7 | `th-lemma` +1 / 3 PENDING | `real-division-checkout-math-exp-01.json` |
| Nov 16 00:23 | Real product intervals, fstar-build, Math.Exp query 7 | `arith/lp-monomial-interval` +4 / 0 PENDING | `real-product-checkout-math-exp-01.json` |
| Nov 15 23:39 | Nonnegative product draft, same Math.Exp proof; superseded by combined product replay | `arith/lp-monomial-interval` +2 / 2 PENDING | `real-nonnegative-math-exp-01.json` |
| Nov 15 23:29 | Generic-array draft, sample, 11 proofs; **not retained** | Root PENDING: `th-lemma` +681 / 0; `rewrite` +7 / 36; 4 proofs promoted. Paired median time ratio 1.96 | `generic-array-sample-weighted-01.json`, `generic-array-sample-subset-timing-01.json` |
| Nov 15 18:27 | Larger Real equations, fstar-build, 147 proofs | `rewrite` +2 / 0 PENDING; 2 proofs promoted | `large-real-compare-02.json` |
| Nov 15 17:52 | Arithmetic bounds rewrites, sample, 11 proofs | `rewrite` +996 / 43 PENDING; 1 proof promoted | `bounds-sample-01.json` |
| Nov 15 15:41 | Integer cuts, sample, ring proof | `th-lemma` +15 / 0 PENDING; 28 other obligations remain | `integer-cut-sample-02.json` |
| Nov 15 14:11 | Existential DER, sample, 1 proof | `der` +1 / 0 PENDING; proof promoted | `existential-der-measure-01.json` |

Root certification may discharge obligations without independently
certifying each original entry. Evidence files contain checker and proof pins.

## Burn-down: identical frozen proofs

| Dataset | Checker SHA-256 prefixes | Rule | Before | Newly checked | Remaining |
| --- | --- | --- | ---: | ---: | ---: |
| fstar-build, Math.Exp query 7 | `245dd5c801e3` → `35ef16e3adce` | `arith/lp-monomial-interval` | 4 | 4 | 0 |
| fstar-build, Math.Exp query 7 | `35ef16e3adce` → `38203471c053` | `th-lemma` | 4 | 1 | 3 |
| fstar-build, CancellableInvariant query 2 | `35ef16e3adce` → `38203471c053` | `th-lemma` | 2 | 1 | 1 |
| smtlib-extended, 1 proof | `38203471c053` → `98ecf978a307` | `arith/farkas` | 5 | 2 | 3 |
| smtlib-extended, 1 proof | `38203471c053` → `98ecf978a307` | `th-lemma` | 7 | 2 | 5 |
| fstar-build, UInt128, 1 proof; draft | `98ecf978a307` → `a0ca7df92173` | `th-lemma` | 199 | 63 | 136 |

These are subset results, not full-cohort burn-downs. Evidence: session
`files\real-product-checkout-math-exp-01.json`,
`files\real-division-checkout-math-exp-01.json`,
`files\real-division-checkout-cancellable-01.json`,
`files\multiple-zero-extended-02.json`, `files\int-quotient-uint128-01.json`.

## Matched acceptance and timing

| Dataset | Checker | Proofs | ACCEPT | PARTIAL |
| --- | --- | ---: | ---: | ---: |
| fstar-build | retained `38203471c053` | 147 | 146 | 1 |
| fstar-build | multi-zero `98ecf978a307` | 147 | 146 | 1 |
| smtlib-sample | legacy | 11 | 11 | 0 |
| smtlib-sample | retained `38203471c053` | 11 | 1 | 10 |
| smtlib-sample | multi-zero `98ecf978a307` | 11 | 1 | 10 |

Five alternating pairs gave multi-zero/retained median time ratios of **1.030**
on the extended proof and **1.004** over five sample proofs. These subsets do
not establish whole-cohort parity or speedup. Evidence: session
`files\multiple-zero-fstar-02.json`, `files\multiple-zero-sample-02.json`,
`files\multiple-zero-extended-timing-01.json`,
`files\multiple-zero-sample-timing-01.json`.

## Current work

The multi-zero replay proves zero factors and resulting product bounds before
checking a linear contradiction; strict downstream F* verification, checkout
native tests and SMT/Python/help smoke checks passed. Scope tests passed with
seven Windows skips. Evidence: session `files\multiple-zero-downstream-01.json`,
`files\multiple-zero-checkout-build-01.json`, `files\multiple-zero-checkout-smoke-01.json`.

The reader combines native `arith bound` and `arith farkas` hints under
`arith/farkas`. Inspected pending cases include nonlinear bound propagation;
they do not demonstrate faulty linear Farkas certificates. Current source
exports propagation coefficients but attempts structured LP proof export for
conflicts; the captured binary's exact source provenance is unverified.
Evidence: session `files\farkas-bound-producer-analysis-01.json`,
`files\extended-farkas-capture-02.json`.

Six-hour SMT-LIB measurements remain scheduled; finite-field work is paused.
Timeout tails, missing diagnostics and unmeasured candidate cohorts remain N/M.
The quotient draft passed strict downstream verification and native tests;
matched acceptance and paired timing controls are in progress.
