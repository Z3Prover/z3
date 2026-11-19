# Proof-checker pending dashboard

Updated: **2026-11-18T23:10:28-08:00**. Goal: eliminate pending proof obligations
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

Updated `2026-11-18T23:10:28-08:00`; latest case `2026-11-18T23:10:28-08:00`; checker `2671dc150931`. Counts below cover only successful diagnostic results; UNKNOWN, timeouts, errors and unrun cases may hide additional pending obligations.

| Cohort | Latest case | Observed / selected | Diagnostics / observed | Diagnostic errors | ACCEPT | PARTIAL | UNKNOWN | TIMEOUT | SAT | REJECT | Crash / error | NOT_RUN |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| smtlib-sample | `2026-11-18T22:38:23-08:00` | 225 / 225 | 186 / 225 | 0 | 100 | 86 | 20 | 19 | 0 | 0 | 0 | 0 |
| smtlib-extended | `2026-11-18T23:10:28-08:00` | 285 / 285 | 209 / 285 | 0 | 74 | 135 | 69 | 7 | 0 | 0 | 0 | 0 |

| Rule | Sample observed PENDING | Extended observed PENDING |
| --- | ---: | ---: |
| `arith/farkas` | 0 | 14 |
| `arith/lp-monomial-interval` | 0 | 40 |
| `assumed:nlsat` | 0 | 149 |
| `def-axiom` | 3 | 89 |
| `der` | 6 | 0 |
| `intro-def` | 272 | 140 |
| `quant-intro` | 42 | 83 |
| `rewrite` | 133 | 24687 |
| `th-lemma` | 3499 | 6212 |

State: **stages complete**. Diagnostic errors are excluded from rule totals. Per-case logs, timestamps and pins: session `files\periodic-smtlib-20261119T060109Z`.
<!-- END CURRENT PENDING -->

<!-- BEGIN CURRENT FSTAR PENDING -->
## Current fstar-build diagnostic collection

Updated `2026-11-18T17:44:43-08:00`; latest case `2026-11-18T17:41:52-08:00`; checker `2671dc150931`. Counts include observed timeout prefixes only; unobserved proof tails and cases with diagnostic errors may contain additional PENDING.

| Observed / selected | Completed | TIMEOUT | Error / crash | NOT_RUN | Diagnosed proof sessions / observed | Diagnostic errors |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 253 / 583 | 237 | 16 | 0 | 330 | 249 / 253 | 0 |

Observed proofs: **6061 ACCEPT / 158 PARTIAL / 0 UNKNOWN / 0 REJECT**; solver UNKNOWN queries: **138**.

| Rule | Observed PENDING |
| --- | ---: |
| `assumed:nlsat` | 72 |
| `nnf-neg` | 5 |
| `quant-intro` | 9 |
| `rewrite` | 7 |
| `sk` | 5 |
| `th-lemma` | 198 |

Aggregation correction at 17:44:43 PST: 106 repeated input paths in `current-fstar-pending-2671-06` were excluded, retaining the first observation per path. Duplicate input hashes and verdicts match; proof counts differ on 103 rows and rule vectors on 5, so reruns are not counted as coverage or checker improvement. State: **stage complete**. Per-case evidence and pins: sessions `files\current-fstar-pending-2671-01`, `files\current-fstar-pending-2671-05`, and `files\current-fstar-pending-2671-06`.
<!-- END CURRENT FSTAR PENDING -->

## Last 10 incremental improvements and measurement corrections

Refresh this rolling timeline on every dashboard update; retain existing rows
when no new improvement has been measured. Label measurement corrections
explicitly and do not credit them as checker gains. Times are evidence-file
completion or last-modified times in PST. Counts are for the specified frozen
proofs, not whole cohorts; overlapping candidate gains must not be added.

| Time (PST) | Improvement and scope | Measured effect | Evidence in session `files\` |
| --- | --- | --- | --- |
| Nov 18 23:10 | Scheduled same-pin, same-input SMT-LIB rerun; measurement correction, no checker change | All 510 input hashes matched; ACCEPT/PARTIAL counts unchanged, with one sample UNKNOWN → TIMEOUT. Two extended QF_NIA PARTIAL vectors and three proof-node counts changed; Farkas shift is QF_NIA, not QF_LIA. No matched-proof burn-down | `periodic-smtlib-20261119T060109Z`, prior `periodic-smtlib-20261118T235842Z` |
| Nov 18 17:44 | fstar-build aggregation correction, current pin; no checker change | 359 raw rows → 253 distinct inputs; excluded 106 repeated paths. Duplicate hashes/verdicts match, but proof counts differ in 103 rows and rule vectors in 5; no burn-down credit | `current-fstar-pending-2671-01`, `current-fstar-pending-2671-05`, `current-fstar-pending-2671-06` |
| Nov 18 15:30 | Current-pin fstar-build prefix extension, five inputs; no checker change | Four inputs completed and one timed out; 88 ACCEPT / 1 PARTIAL / 7 solver UNKNOWN, with one new `th-lemma` PENDING. The timeout's observed 56-proof prefix is included; its tail is N/M. Coverage refresh, not a same-proof burn-down | `current-fstar-pending-2671-05` |
| Nov 18 14:59 | Exact current-pin QF_LIA ring arithmetic-hint trace; no checker change | Frozen proof hash matches `23fedbd874be`; one native `arith bound` (655) and four native `arith farkas` nodes (460, 912, 846, 929) all pass as `ArithmeticFarkas`. This case shows no QF_LIA rounding failure | `ring-native-hints-2671-01.json`, `ring-native-hints-2671-01.stderr`, `ring-definitions-trace-2671-03.json` |
| Nov 18 14:37 | Bounded-integers fstar-build diagnostic replay, 10 queries; no checker change | Three `th-lemma` PENDING remain with identical fingerprints; replay reports 9 ACCEPT / 1 PARTIAL. Proof-node counts differ on queries 7-10 and proof hash is N/M, so this is not a matched-proof burn-down | `fstar-build-bounded-integers-2671-03.json` |
| Nov 18 14:24 | Current-pin arithmetic hint bridge diagnosis; one QF_NIA Count proof, no checker change | Native `bound` and `farkas` hints both become `ArithmeticFarkas` before replay. The Count failures retain nonlinear residuals, so this does not establish a QF_LIA rounding/certificate defect | `count-farkas-trace-2671-01.json`, `count-farkas-trace-2671-01.txt`, `Z3Native.ml:437-477`, `Z3NativeProof.fst:309-316` |
| Nov 18 14:13 | Current-pin QF_NIA Count `arith bound` provenance trace; no checker change | Same input, different proof: 10-s baseline PARTIAL 74 / Farkas 2409 vs 60-s capture PARTIAL 172 / Farkas 4159,4160. The latter leave 10 and 9 residual monomials over visible premises; not a matched burn-down, omitted-premise provenance unresolved | `count-farkas-trace-2671-01.json`, `count-farkas-trace-2671-01.txt`, `extended-farkas-capture-2671-05.json`, `extended-farkas-capture-2671-06.json` |
| Nov 18 12:27 | Current-pin QF_LIA subset breakdown; same frozen SMT-LIB capture, no checker change | Sample: 25 selected, 17 ACCEPT / 1 PARTIAL / 2 TIMEOUT / 5 UNKNOWN; the sole PARTIAL has four `intro-def` obligations and all five ring arithmetic steps are accepted. Extended has no selected QF_LIA inputs in this capture | `periodic-smtlib-20261118T170450Z\smtlib-sample\results.jsonl`, `ring-definitions-trace-2671-03.json` |
| Nov 18 12:10 | Current-pin QF_NIA/QF_NRA Farkas provenance, four matched 10-second captures | 13 weighted PENDING across 10 nodes are native `arith bound` hints; preparation succeeds but linear acceptance fails with residual terms. Producer path emits bound weights and a consequent, but does not apply its Farkas-conflict validation to this hint. This narrows the gap to bound evidence/replay; it does not establish malformed certificates or explain every residual | `extended-farkas-capture-2671-05.json`, `NativeFarkasTrace2671.ml` |
| Nov 18 11:40 | Current-pin QF_LIA ring definition diagnosis, 1 frozen proof | Four `intro-def` PENDING are nullary Int ITE branch definitions; replay shape gates do not match. Five arithmetic steps accepted (one native bound, four native Farkas) | `ring-definitions-trace-2671-03.json`, `ite-add-sample-02.json` |

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

An additional bounded-integers `fstar-build` diagnostic covered 10 queries:
the replay reports 9 ACCEPT / 1 PARTIAL and preserves three `th-lemma`
PENDING fingerprints. Proof-node counts differ on queries 7-10 and the proof
document hash is N/M, so this does not establish a matched-proof burn-down or
change the aggregate 158/583 cohort counts. Evidence:
`files\fstar-build-bounded-integers-2671-03.json`.

The current worktree's strict verification uses pinned F* 2026.10.25, but
`Z3UnifiedProof.fst` timed out at 1800 seconds; no module was verified in that
attempt. The conditional-definition modules retain their previously passing
strict and checkout controls, and the 11-proof baseline comparison has zero
regressions or unobserved proofs. Do not promote the separate uncommitted
worktree edits based on the timeout. Evidence:
`files\current-unified-fstar-verification-05.json`,
`files\conditional-downstream-02.json`,
`files\conditional-checkout-current-2671-02.json`,
`files\conditional-current-baseline-2671-01.json`.

On the pinned `2671dc150931` extended cohort, the 15 weighted `arith/farkas`
PENDING occur in five QF_NIA/QF_NRA inputs (13 and 2 respectively); the
sample cohort has zero. Same-timeout traces recaptured four inputs: 13 weighted
PENDING across 10 nodes, all with native `arith bound` hints. The 10-second
Count capture timed out, but a 60-second same-input control completed with a
different 5,142-entry proof: `PARTIAL 172` with Farkas PENDING at 4159 and
4160, versus the 10-second baseline's `PARTIAL 74` and index 2409. This is not
a matched-proof comparison. Both new nodes carry 32 rational weights for 31
visible premises plus the negated conclusion. F* preparation succeeds, but
the weighted sums leave 10 and 9 residual monomials, including nonlinear
products; they are not plain-linear certificates over the visible premises.
Evidence: `count-farkas-trace-2671-01.json` and
`count-farkas-trace-2671-01.txt`.

The native bridge recognizes `farkas` and `bound` as different parameter-1
hints in `fstar/ocaml_runtime/Z3Native.ml`, but exposes both coefficient lists
as `proof_view.farkas`; `Z3NativeProof.native_rule` maps either to
`ArithmeticFarkas`. The hint distinction is lost before checker dispatch, so
no bound-specific integer-rounding or cut check can be selected there. In
`src/smt/theory_lra.cpp`, LP bound propagation calls
`set_proof_params(m_bound, true)`, which emits explanation weights and a unit
consequent coefficient. The producer's `check_farkas_conflict` validation is
gated to `m_farkas`, not `m_bound`; moreover, `set_evidence` omits hard
definition constraints and constraints with no SAT-core source. These facts
make a bound-evidence/replay gap plausible, but do not show that skipped
constraints occur in the Count nodes. Their nonlinear residuals mean the
visible payload is not a complete plain-linear certificate. On the exact
frozen QF_LIA ring proof `23fedbd874be`, a same-process trace matches the
frozen proof hash and finds five arithmetic nodes: native `arith bound` at
655 and native `arith farkas` at 460, 912, 846 and 929. All five pass the
current checker after both hint kinds are mapped to `ArithmeticFarkas`; the
bound node is a valid linear certificate in this proof, not an
integer-rounding failure. Recover full provenance for the separate nonlinear
Count nodes before changing the Farkas checker or producer.
Evidence: `ring-native-hints-2671-01.json`,
`ring-native-hints-2671-01.stderr` and
`ring-definitions-trace-2671-03.json`.

On the identical frozen QF_LIA ring proof `23fedbd874be`, all five arithmetic
steps are accepted by Legacy and both independent-checker arms; the remaining
independent PENDING are definitions and rewrites. The current-pin trace shows
the four `intro-def` entries define nullary integer `z3name!` symbols using
paired ITE branch clauses. The independent definition replay accepts
unary-Boolean paired definitions or direct nullary equalities, so neither
route covers this shape; this is a checker coverage gap, not evidence of
faulty Farkas generation. Evidence: session
`files\periodic-smtlib-20261118T170450Z`,
`files\ite-add-sample-02.json`, `files\extended-farkas-capture-2671-05.json`,
`files\extended-farkas-capture-2671-06.json`,
`files\ring-definitions-trace-2671-03.json`.

The QF_LIA slice of that SMT-LIB sample capture contains 25 selected inputs:
17 ACCEPT, one PARTIAL, two TIMEOUT and five UNKNOWN. The only PARTIAL is the
ring proof above, with four `intro-def` PENDING; its five arithmetic nodes
(one native bound and four native Farkas) are accepted. The extended capture
contains no selected QF_LIA inputs, so it provides no QF_LIA comparison. Two
definitions have cross-entry dependencies,
including `z3name!3` referring to `z3name!2` before the latter's definition
entry. A sound replay therefore needs freshness checks and dependency-aware
interpretation of all four constants; recognizing one paired-ITE formula in
isolation would not close the proof. Evidence: session
`files\periodic-smtlib-20261118T170450Z`,
`files\ring-definitions-trace-2671-03.json`.

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
