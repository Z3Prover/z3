# Proof-checker pending dashboard

Updated: **2026-11-18T11:07:35-08:00**. Goal: eliminate pending proof obligations
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

Updated `2026-11-18T10:12:19-08:00`; latest case `2026-11-18T10:12:19-08:00`; checker `2671dc150931`. Counts below cover only successful diagnostic results; UNKNOWN, timeouts, errors and unrun cases may hide additional pending obligations.

| Cohort | Latest case | Observed / selected | Diagnostics / observed | Diagnostic errors | ACCEPT | PARTIAL | UNKNOWN | TIMEOUT | SAT | REJECT | Crash / error | NOT_RUN |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| smtlib-sample | `2026-11-18T09:40:40-08:00` | 225 / 225 | 186 / 225 | 0 | 100 | 86 | 20 | 19 | 0 | 0 | 0 | 0 |
| smtlib-extended | `2026-11-18T10:12:19-08:00` | 285 / 285 | 209 / 285 | 0 | 74 | 135 | 69 | 7 | 0 | 0 | 0 | 0 |

| Rule | Sample observed PENDING | Extended observed PENDING |
| --- | ---: | ---: |
| `arith/farkas` | 0 | 15 |
| `arith/lp-monomial-interval` | 0 | 40 |
| `assumed:nlsat` | 0 | 148 |
| `def-axiom` | 3 | 89 |
| `der` | 6 | 0 |
| `intro-def` | 272 | 136 |
| `quant-intro` | 42 | 83 |
| `rewrite` | 133 | 24678 |
| `th-lemma` | 3499 | 6237 |

State: **stages complete**. Diagnostic errors are excluded from rule totals. Per-case logs, timestamps and pins: session `files\periodic-smtlib-20261118T170450Z`.
<!-- END CURRENT PENDING -->

<!-- BEGIN CURRENT FSTAR PENDING -->
## Current fstar-build diagnostic collection

Updated `2026-11-16T15:05:01-08:00`; latest case `2026-11-16T15:05:01-08:00`; checker `a0ca7df92173`. Counts include observed timeout prefixes only; unobserved proof tails and cases with diagnostic errors may contain additional PENDING.

| Observed / selected | Completed | TIMEOUT | Error / crash | NOT_RUN | Diagnosed proof sessions / observed | Diagnostic errors |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 583 / 583 | 546 | 37 | 0 | 0 | 570 / 583 | 0 |

Observed proofs: **10960 ACCEPT / 348 PARTIAL / 0 UNKNOWN / 0 REJECT**; solver UNKNOWN queries: **463**.

| Rule | Observed PENDING |
| --- | ---: |
| `arith/farkas` | 4 |
| `arith/lp-monomial-interval` | 2 |
| `assumed:nlsat` | 358 |
| `nnf-neg` | 23 |
| `quant-intro` | 41 |
| `rewrite` | 11 |
| `sk` | 18 |
| `th-lemma` | 823 |

State: **complete**. Per-case evidence and pins: session `files\int-quotient-fstar-pending-01`.
<!-- END CURRENT FSTAR PENDING -->

## Last 10 incremental improvements

Refresh this rolling timeline on every dashboard update; retain existing rows
when no new improvement has been measured. Times are evidence-file completion
or last-modified times in PST. Counts are for the specified frozen proofs, not
whole cohorts; overlapping candidate gains must not be added.

| Time (PST) | Improvement and scope | Measured effect | Evidence in session `files\` |
| --- | --- | --- | --- |
| Nov 18 10:59 | Current checker pin vs. pre-conditional baseline, sample, 11 matched proofs; combined confirmation, not an additive gain | `apply-def` PENDING 80 → 0; `rewrite` 43 → 36; zero verdict regressions or unobserved proofs | `conditional-current-baseline-2671-01.json` |
| Nov 16 17:34 | Lattice replay draft, experimental QF_LIA ring proof; **not retained** | Same checker and proof, lattice payloads erased → present: `arith/lp-integer-lattice` PENDING 18 → 0; `intro-def` remains 4 | `lattice-same-producer-01.json` |
| Nov 16 15:46 | Int ITE/add factoring, sample, 11 frozen proofs | Root `rewrite` PENDING 43 → 36; no verdict regressions. Seven-proof paired median ratio 0.982 | `ite-add-weighted-02.json`, `ite-add-sample-timing-02.json` |
| Nov 16 13:06 | Conditional definition replay, sample, 11 frozen proofs | Root `apply-def` PENDING 80 → 0; no verdict regressions. Seven-proof paired median ratio 1.014 | `conditional-weighted-01.json`, `conditional-sample-timing-01.json` |
| Nov 16 11:33 | Filtered array draft, sample, 11 proofs; **not retained** | Root `th-lemma` +681 / 0 PENDING; `rewrite` +7 / 36 PENDING; 4 proofs promoted. Two promoted proofs: paired median time ratios 1.66 and 1.94 | `array-prefilter-weighted-01.json`, `array-prefilter-sample-timing-01.json` |
| Nov 16 09:52 | Guarded Int quotient, fstar-build, UInt128, 1 proof | Root `th-lemma` +63 / 136 PENDING | `int-quotient-uint128-01.json` |
| Nov 16 05:27 | Multi-zero products, extended, 1 proof | `arith/farkas` +2 / 3 PENDING; `th-lemma` +2 / 5 PENDING | `multiple-zero-extended-02.json` |
| Nov 16 03:12 | Guarded Real division, fstar-build, Math.Exp query 7 | `th-lemma` +1 / 3 PENDING | `real-division-checkout-math-exp-01.json` |
| Nov 16 00:23 | Real product intervals, fstar-build, Math.Exp query 7 | `arith/lp-monomial-interval` +4 / 0 PENDING | `real-product-checkout-math-exp-01.json` |
| Nov 15 23:39 | Nonnegative product draft, same Math.Exp proof; superseded by combined product replay | `arith/lp-monomial-interval` +2 / 2 PENDING | `real-nonnegative-math-exp-01.json` |

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
| fstar-build, UInt128, 1 proof | `98ecf978a307` → `a0ca7df92173` | `th-lemma` | 199 | 63 | 136 |
| smtlib-sample, 11 proofs | `a0ca7df92173` → `79de3a41dcdb` | `apply-def` | 80 | 80 | 0 |
| smtlib-sample, 11 proofs | `79de3a41dcdb` → `2671dc150931` | `rewrite` | 43 | 7 | 36 |
| smtlib-sample, 11 proofs; array draft | `98ecf978a307` → `bac3ba06e1c1` | `th-lemma` | 681 | 681 | 0 |
| smtlib-sample, 11 proofs; array draft | `98ecf978a307` → `bac3ba06e1c1` | `rewrite` | 43 | 7 | 36 |

These are subset results, not full-cohort burn-downs. Evidence: session
`files\real-product-checkout-math-exp-01.json`,
`files\real-division-checkout-math-exp-01.json`,
`files\real-division-checkout-cancellable-01.json`,
`files\multiple-zero-extended-02.json`, `files\int-quotient-uint128-01.json`,
`files\array-prefilter-weighted-01.json`, `files\conditional-weighted-01.json`,
`files\ite-add-weighted-02.json`.

## Matched acceptance and timing

| Dataset | Checker | Proofs | ACCEPT | PARTIAL |
| --- | --- | ---: | ---: | ---: |
| fstar-build | retained `38203471c053` | 147 | 146 | 1 |
| fstar-build | multi-zero `98ecf978a307` | 147 | 146 | 1 |
| smtlib-sample | legacy | 11 | 11 | 0 |
| smtlib-sample | retained `38203471c053` | 11 | 1 | 10 |
| smtlib-sample | multi-zero `98ecf978a307` | 11 | 1 | 10 |
| smtlib-sample | array draft `bac3ba06e1c1` | 11 | 5 | 6 |
| smtlib-sample | ITE/add `2671dc150931` | 11 | 1 | 10 |

Five alternating pairs gave multi-zero/retained median time ratios of **1.030**
on the extended proof and **1.004** over five sample proofs. These subsets do
not establish whole-cohort parity or speedup. Evidence: session
`files\multiple-zero-fstar-02.json`, `files\multiple-zero-sample-02.json`,
`files\multiple-zero-extended-timing-01.json`,
`files\multiple-zero-sample-timing-01.json`.

The quotient replay preserved verdicts and rule counts on 11 sample
proofs. Five alternating pairs on five of those proofs gave a median per-proof
candidate/retained time ratio of **1.006**; five paired UInt128 runs gave
**1.007**. Evidence: `files\int-quotient-sample-01.json`,
`files\int-quotient-sample-timing-02.json`,
`files\int-quotient-uint128-timing-01.json`.

The filtered array draft's overall median paired ratio was **1.009** over five
sample proofs, but two promoted proofs slowed by **1.66x** and **1.94x**.
It is not retained. Evidence: `files\array-prefilter-sample-timing-01.json`.

Conditional definition replay preserved verdicts on 11 sample proofs and
eliminated their 80 weighted `apply-def` obligations. Five alternating pairs
on seven frozen sample proofs gave a median per-proof candidate/retained time
ratio of **1.014**; this does not establish cohort performance. Evidence:
`files\conditional-weighted-01.json`, `files\conditional-sample-timing-01.json`.

Int ITE/add factoring eliminated seven weighted `rewrite` obligations on the
frozen QF_LIA ring proof, which remains PARTIAL with four `intro-def`
obligations. Five alternating pairs on seven frozen sample proofs gave a
median candidate/retained time ratio of **0.982** (ring **0.951**). Evidence:
`files\ite-add-sample-02.json`, `files\ite-add-weighted-02.json`,
`files\ite-add-sample-timing-02.json`.

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

On the pinned `2671dc150931` extended cohort, the 15 weighted `arith/farkas`
PENDING occur in five QF_NIA/QF_NRA inputs (13 and 2 respectively). Their
fingerprints hide operands, so they cannot establish whether each certificate
is linear or whether its producer evidence is malformed. The sample cohort has
zero `arith/farkas` PENDING. On the identical frozen QF_LIA ring proof
`23fedbd874be`, all five Farkas steps are accepted by Legacy and both
independent-checker arms; the remaining independent PENDING are definitions
and rewrites. The separate QF_NIA AProVE producer capture uses checker
`35ef16e3adce`, not `2671dc150931`, and does not establish proof identity.
Evidence: session `files\periodic-smtlib-20261118T170450Z`,
`files\ite-add-sample-02.json`, `files\extended-farkas-capture-02.json`.

An experimental integer-input binding bridge passed LP unit tests, but on the
same QF_LIA ring input it changed the generated proof and increased root
PENDING from 15 to 33, adding 18 `arith/lp-integer-lattice` obligations.
An isolated lattice replay draft verified 173 F* modules and passed positive and
negative controls for all 18 nodes. On its pinned experimental proof, the
same checker reported 18 → 0 lattice PENDING when only the lattice payloads
were restored; four `intro-def` obligations remain. Eleven frozen sample
proofs had no verdict regressions and identical weighted counts; seven-proof paired timing
had median candidate/retained ratio 0.998. The retained producer's original
ring proof also has four pending obligations, so this is not yet a measured
end-to-end improvement. The bridge and replay remain unretained; linear-time
checking has not been established. Evidence:
`files\lp-binding-ring-compare-01.json`,
`files\lattice-integration-verification-01.json`,
`files\lattice-integration-controls-03.json`,
`files\lattice-same-producer-01.json`,
`files\lattice-sample-weighted-02.json`,
`files\lattice-sample-timing-01.json`.

Six-hour SMT-LIB measurements remain scheduled; finite-field work is paused.
Timeout tails, missing diagnostics and unmeasured candidate cohorts remain N/M.
The quotient replay passed strict downstream verification, checkout native
controls, SMT/Python/help smoke checks and scope tests (seven Windows skips).
Evidence: `files\int-quotient-downstream-02.json`,
`files\int-quotient-checkout-controls-01.json`,
`files\int-quotient-checkout-smoke-01.json`,
`files\int-quotient-scope-tests-02.json`. The diagnostic tables specify their
checker pins; matched acceptance and timings cover only frozen subsets.
Conditional replay also passed strict downstream verification, checkout native
controls, SMT/Python/help smoke checks and scope tests (seven skipped).
Evidence: `files\conditional-downstream-02.json`,
`files\conditional-checkout-controls-01.json`,
`files\conditional-checkout-smoke-01.json`,
`files\conditional-scope-tests-01.json`.
A matched-proof comparison of pre-conditional baseline `a0ca7df92173` against
current checker `2671dc150931` passed on 11 identical sample proofs:
`apply-def` PENDING 80 → 0 and `rewrite` 43 → 36, with zero verdict
regressions or unobserved proofs. These are combined confirmations of the
conditional and ITE/add changes, not an additional cohort gain. Evidence:
session `files\conditional-current-baseline-2671-01.json`.
