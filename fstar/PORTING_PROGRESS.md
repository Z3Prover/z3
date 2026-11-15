# Checker porting progress

**Old historical:** archived measurements of the legacy `Z3NativeMain` checker,
whose dependency closure includes `Z3ValueTheory.fst`. These are not matched
current measurements; `old` / `legacy` in paired tables means the separately
pinned legacy control.

**Core:** the new ValueTheory-free independent checker, default `sorted-core` route.

**Definition:** the same independent checker with `--definition-replay`
(`sorted-definition`): Core plus verified definition, NNF and Skolem replay.
**Both Core and Definition** use a dependent carrier family `base : sort -> Type0`
and sort-indexed values `Z3DatatypeValue.value base sigma s`. The name
"Definition" identifies additional proof replay, not a different value-domain
architecture. See [values](Z3DatatypeValue.fst) and [mode contracts](Z3IndependentChecker.fsti).

Updated: **2026-11-15T13:26:26-08:00** (America/Los_Angeles).

**Goal:** beat the legacy `fstar-build` baseline before retiring `Z3ValueTheory.fst`.
Not established yet. Finite-field work remains paused.

**Toolchain correction, Nov 15 00:45 PST:** the independent checker's native
stubs used OCaml 5.4 headers with a 5.3 runtime (GC roots at `0xc0` instead
of `0xa0`). The legacy baseline uses the correct layout. The pre-ABI-fix rollout
below is retained as **ABI-affected historical evidence, not parity evidence**;
do not extend or mix it with corrected-binary results. Pure frozen-document
replay timings remain document-only measurements, not source-instance parity.
Corrected-header binding clears the reproducible abort in **3/3** core reruns;
each completes **16 ACCEPT**, versus 11 ACCEPT then abort before correction.
Corrected-binary strict F*, 185-file independent closure, 20 non-field CLI tests,
OCaml example and nine-case SMT-LIB guard pass. Corrected observations now cover
all **583 inputs per mode**; coverage/performance parity remains unestablished.

<!-- BEGIN ALL INSTANCE STATUS -->
## All 583 fstar-build instances

Audited **2026-11-14 20:04:08 PST**. [583-instance ledger](PORTING_INSTANCES.csv): input SHA-256, historical session/proof counts, timeout prefixes, and latest matched replay status. All 583 historical input hashes match; `NOT_MEASURED` is not a pass.

| Session status | Old historical | Independent build-10 historical |
| --- | --- | --- |
| ACCEPT | 119 | 204 |
| PARTIAL | 49 | 76 |
| UNKNOWN | 0 | 3 |
| NO_UNSAT_PROOF | 4 | 5 |
| TIMEOUT | 12 | 21 |
| NOT_RUN | 399 | 274 |
| Crash/error | 0 | 0 |
| Total inputs | 583 | 583 |

Completed sessions: **172 old / 288 build-10**. These are historical references, **not the current candidate**. Total budgets differ: 1,800 / 3,600 s; both use 60-s sessions and 10,000-ms solver queries. Do not infer a speedup or coverage gain from these unmatched totals. Historical execution timestamps/binary hashes were not recorded.

| Observed proof/judgment count | Old historical | Build-10 historical |
| --- | --- | --- |
| ACCEPT | 5188 | 6973 |
| PARTIAL | 188 | 286 |
| UNKNOWN | 0 | 103 |
| REJECT | 0 | 0 |
| pending_judgements | 424 | 707 |
| unattributed_pending_judgements | 424 | 66 |

Proof/judgment totals **include emitted timeout prefixes**; a timed-out session is never counted complete. Solver UNKNOWN responses: **123 old / 174 build-10**, separate from checker UNKNOWN. `NO_UNSAT_PROOF` means no proof was available (four old sessions previously labeled UNKNOWN). Counts are observations, not estimates for unrun inputs.

### Per-rule PARTIAL / REJECTED judgments

**Matched current comparison:** 147 identical documents from ten streams; diagnostics collected `2026-11-14T20:03:34-08:00`. Old diagnostics were recomputed with the pinned old runtime; current core/definition diagnostics were read from their completed exact-replay results. Every observed outer rule is listed. PARTIAL counts sum weighted diagnostic obligations, **not partial proofs**. Inner-certificate failures are not separately attributed by this API.

| Rule | Outer entries | Old P / R | New core P / R | New definition P / R |
| --- | --- | --- | --- | --- |
| `and-elim` | 9 | 0 / 0 | 0 / 0 | 0 / 0 |
| `arith/farkas` | 100 | 0 / 0 | 0 / 0 | 0 / 0 |
| `asserted` | 6280 | 0 / 0 | 0 / 0 | 0 / 0 |
| `commutativity` | 126 | 0 / 0 | 0 / 0 | 0 / 0 |
| `def-axiom` | 8853 | 0 / 0 | 0 / 0 | 0 / 0 |
| `hypothesis` | 7178 | 0 / 0 | 0 / 0 | 0 / 0 |
| `iff-false` | 798 | 0 / 0 | 0 / 0 | 0 / 0 |
| `iff-true` | 687 | 0 / 0 | 0 / 0 | 0 / 0 |
| `intro-def` | 9 | 9 / 0 | 9 / 0 | 0 / 0 |
| `lemma` | 1795 | 0 / 0 | 0 / 0 | 0 / 0 |
| `monotonicity` | 43422 | 0 / 0 | 0 / 0 | 0 / 0 |
| `mp` | 16944 | 0 / 0 | 0 / 0 | 0 / 0 |
| `mp~` | 2903 | 0 / 0 | 0 / 0 | 0 / 0 |
| `nnf-neg` | 70 | 6 / 0 | 6 / 0 | 1 / 0 |
| `nnf-pos` | 2785 | 10 / 0 | 10 / 0 | 0 / 0 |
| `quant-inst` | 6682 | 0 / 0 | 0 / 0 | 0 / 0 |
| `quant-intro` | 3154 | 25 / 0 | 25 / 0 | 4 / 0 |
| `refl` | 2827 | 0 / 0 | 0 / 0 | 0 / 0 |
| `rewrite` | 15330 | 2 / 0 | 2 / 0 | 2 / 0 |
| `sk` | 147 | 6 / 0 | 6 / 0 | 1 / 0 |
| `symm` | 16613 | 0 / 0 | 0 / 0 | 0 / 0 |
| `th-lemma` | 173 | 0 / 0 | 0 / 0 | 0 / 0 |
| `trans` | 7339 | 0 / 0 | 0 / 0 | 0 / 0 |
| `trans*` | 15601 | 0 / 0 | 0 / 0 | 0 / 0 |
| `unit-resolution` | 33005 | 0 / 0 | 0 / 0 | 0 / 0 |
| **Total** | 192830 | **58 / 0** | **58 / 0** | **8 / 0** |

Matched proof verdicts: old/core **129 ACCEPT / 18 PARTIAL**, definition **144 / 3**; zero UNKNOWN, REJECT, timeout, or crash. **573 other streams are outside this frozen cohort; full-current end-to-end 583-instance parity remains unestablished.** Root-certified versus unsupported formula status is not a local rule rejection.

<details>
<summary>Historical whole-corpus rule attribution (incomplete diagnostics)</summary>

Old historical logs did not request per-rule diagnostics: **all 424 pending judgments are unattributed**, so old per-rule PARTIAL is **N/A, not zero**. Build-10 attributes 641 of 707; 66 remain unattributed. No REJECT proof verdicts were observed in either run; per-entry rejection attribution was not recorded and is marked N/A, not inferred. This historical table is not a current-candidate comparison.

| Rule | Old PARTIAL | Build-10 PARTIAL | Old / new observed REJECTED |
| --- | --- | --- | --- |
| `arith/farkas` | N/A | 2 | N/A / N/A |
| `assumed:nlsat` | N/A | 115 | N/A / N/A |
| `intro-def` | N/A | 9 | N/A / N/A |
| `nnf-neg` | N/A | 35 | N/A / N/A |
| `nnf-pos` | N/A | 10 | N/A / N/A |
| `quant-intro` | N/A | 149 | N/A / N/A |
| `rewrite` | N/A | 7 | N/A / N/A |
| `sk` | N/A | 37 | N/A / N/A |
| `th-lemma` | N/A | 277 | N/A / N/A |
| Unattributed pending | 424 | 66 | N/A / N/A |
| Total pending | 424 | 707 | N/A / N/A |

</details>

Sources: session `files\all-instance-history-audit-01.json`, `files\matched-rule-counts-02.json`, `files\legacy-cached-entry-02.json`. The ledger keeps historical and frozen columns separate; cohorts overlap and must not be added together.
<!-- END ALL INSTANCE STATUS -->

<!-- BEGIN CURRENT CORPUS -->
## Pre-ABI-fix end-to-end corpus rollout (historical)

Updated `2026-11-15T00:31:50-08:00`. All **583 inputs selected**; historical old ACCEPT sessions first, then input size. Pinned old/current binaries, identical input hashes, serial 900-s stages; 10,000-ms solver / 60-s session / 4,096-MiB caps. Solver proof shapes can differ; this is **not** the identical-document timing experiment above. First observed full-window session outcome retained per input/arm; stage-censored prefixes are retained until a full-window rerun. Overlapping reruns, historical and frozen counts are not added.

Binary SHA-256: old `0b5ceec2db9d2fadf279dbf37a843022a3ebb02adcb13349c9b9ed2676b0ada3`, new `b034b4ea3fa632ca682ca5501ef34a51002d43e491ec173de38c5ccdbc195b47`.

| Runtime | Completed | TIMEOUT | Stage-cut | Error/crash | NOT_RUN | Proof ACCEPT | PARTIAL | UNKNOWN | REJECT | Solver UNKNOWN | nnf-pos roots/pending | nnf-neg roots/pending |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| legacy | 483 | 10 | 0 | 0 | 90 | 7784 | 299 | 0 | 0 | 272 | N/A | N/A |
| current-core | 480 | 12 | 0 | 1 | 90 | 7759 | 300 | 0 | 0 | 269 | 80698/0 | 4354/20 |
| current-definition | 481 | 12 | 0 | 0 | 90 | 7782 | 263 | 0 | 0 | 264 | 80068/0 | 4343/4 |

Proof/root totals include emitted timeout prefixes; NOT_RUN is not success. Solver UNKNOWN is separate. Current per-instance results are in the [583-row ledger](PORTING_INSTANCES.csv).
current-core vs old: **480** complete pairs, **7582** aligned UNSAT, **12** observed query-index ACCEPT differences, **38** solver/query differences. Any loss requires identical-proof isolation before calling it a missing rule.
current-core: **3 old-complete / candidate-interrupted sessions**, **24** old UNSAT queries in unobserved tails; these are not passes.
current-core: **5** of those differences reproduced as producer-dependent: identical captures agree in every kernel, but producer histories include contrasting query verdicts. Raw index differences remain counted.
- `pulse/queries-Pulse.Lib.FractionalAnchoredPreorder-1.smt2` q9: `files\fractional-anchored1-isolation-01.json` (2026-11-14T22:58:07-08:00).
- `queries-FStar.Seq.Base.smt2` q33: `files\seq-base-isolation-01.json` (2026-11-14T23:57:31-08:00).
- `queries-FStar.Sequence.Base.smt2` q35: `files\sequence-base-isolation-01.json` (2026-11-14T23:00:15-08:00).
- `queries-FStar.UInt-1.smt2` q9: `files\uint1-isolation-04.json` (2026-11-14T20:59:34-08:00).
- `queries-FStar.UInt128-5.smt2` q44: `files\uint128-5-isolation-01.json` (2026-11-14T22:11:30-08:00).
current-core: **7** differences investigated but **unresolved**: the original contrasting verdicts did not reproduce in bounded producer captures. No old ACCEPT loss occurred on captured identical documents; target-query verdict/pending vectors agree across kernels. This does not discharge the original raw losses or classify them as producer-dependent. See investigation evidence below.
- `queries-FStar.List.Pure.Properties.smt2` q22: `files\list-pure-isolation-01.json` (2026-11-14T22:35:40-08:00).
- `queries-FStar.List.Tot.Properties-1.smt2` q8: `files\list-tot1-isolation-01.json` (2026-11-15T00:01:04-08:00).
- `queries-FStar.List.Tot.Properties.smt2` q58: `files\list-tot-isolation-01.json` (2026-11-14T22:40:55-08:00).
- `queries-FStar.List.Tot.Properties.smt2` q63: `files\list-tot-isolation-01.json` (2026-11-14T22:40:55-08:00).
- `queries-FStar.Matrix.smt2` q4: `files\matrix-isolation-01.json` (2026-11-14T21:36:34-08:00).
- `queries-FStar.UInt128-5.smt2` q46: `files\uint128-5-isolation-01.json` (2026-11-14T22:11:30-08:00).
- `queries-FStar.UInt128-5.smt2` q47: `files\uint128-5-isolation-01.json` (2026-11-14T22:11:30-08:00).
current-definition vs old: **481** complete pairs, **7651** aligned UNSAT, **14** observed query-index ACCEPT differences, **36** solver/query differences. Any loss requires identical-proof isolation before calling it a missing rule.
current-definition: **2 old-complete / candidate-interrupted sessions**, **16** old UNSAT queries in unobserved tails; these are not passes.
current-definition: **5** of those differences reproduced as producer-dependent: identical captures agree in every kernel, but producer histories include contrasting query verdicts. Raw index differences remain counted.
- `pulse/queries-Pulse.Lib.FractionalAnchoredPreorder-1.smt2` q9: `files\fractional-anchored1-isolation-01.json` (2026-11-14T22:58:07-08:00).
- `queries-FStar.List.Tot.Properties.smt2` q23: `files\list-tot-isolation-01.json` (2026-11-14T22:40:55-08:00).
- `queries-FStar.Sequence.Base.smt2` q35: `files\sequence-base-isolation-01.json` (2026-11-14T23:00:15-08:00).
- `queries-FStar.UInt-1.smt2` q9: `files\uint1-isolation-04.json` (2026-11-14T20:59:34-08:00).
- `queries-FStar.UInt128-5.smt2` q44: `files\uint128-5-isolation-01.json` (2026-11-14T22:11:30-08:00).
current-definition: **9** differences investigated but **unresolved**: the original contrasting verdicts did not reproduce in bounded producer captures. No old ACCEPT loss occurred on captured identical documents; target-query verdict/pending vectors agree across kernels. This does not discharge the original raw losses or classify them as producer-dependent. See investigation evidence below.
- `pulse/queries-Pulse.Lib.FractionalAnchoredPreorder-1.smt2` q11: `files\fractional-anchored1-isolation-01.json` (2026-11-14T22:58:07-08:00).
- `pulse/queries-Pulse.Lib.PCM.Fraction.smt2` q8: `files\fraction-target-isolation-02.json` (2026-11-14T21:35:01-08:00).
- `queries-FStar.Algebra.CommMonoid.Fold.smt2` q11: `files\fold-isolation-01.json` (2026-11-14T22:12:28-08:00).
- `queries-FStar.FiniteSet.Base-2.smt2` q26: `files\finite-set-base2-isolation-01.json` (2026-11-14T22:37:36-08:00).
- `queries-FStar.List.Pure.Properties.smt2` q22: `files\list-pure-isolation-01.json` (2026-11-14T22:35:40-08:00).
- `queries-FStar.List.Tot.Properties.smt2` q47: `files\list-tot-isolation-01.json` (2026-11-14T22:40:55-08:00).
- `queries-FStar.List.Tot.Properties.smt2` q54: `files\list-tot-isolation-01.json` (2026-11-14T22:40:55-08:00).
- `queries-FStar.Matrix.smt2` q4: `files\matrix-isolation-01.json` (2026-11-14T21:36:34-08:00).
- `queries-FStar.UInt128-5.smt2` q45: `files\uint128-5-isolation-01.json` (2026-11-14T22:11:30-08:00).

Observed pending judgments by rule (proof shapes may differ):

| Rule | Old PARTIAL | Core PARTIAL | Definition PARTIAL |
| --- | ---: | ---: | ---: |
| `arith/farkas` | 7 | 9 | 4 |
| `arith/lp-monomial-interval` | 1 | 5 | 5 |
| `assumed:nlsat` | 260 | 275 | 236 |
| `nnf-neg` | 20 | 20 | 4 |
| `nnf-pos` | 0 | 0 | 0 |
| `quant-intro` | 64 | 64 | 12 |
| `rewrite` | 12 | 8 | 13 |
| `sk` | 23 | 23 | 4 |
| `th-lemma` | 888 | 895 | 945 |
| Unattributed | 0 | 0 | 0 |
| Total pending | 1275 | 1299 | 1223 |

Rule-level REJECTED attribution is not available from these CLI logs; REJECT proof totals are shown above. Full-corpus parity is **not yet established**. Evidence: session `files\current-corpus-summary-01.json` and its listed pinned raw-log cohorts.
<!-- END CURRENT CORPUS -->

<!-- BEGIN RETAINED TIMEOUT GAP CONTROLS -->
### Retained-checker timeout-gap controls (completed)

Updated `2026-11-15T11:23:07-08:00`. Four pinned source sessions, three rotated serial arms, 10,000-ms solver / 60-s session / 4,096-MiB / 900-s stage caps. Legacy and retained checkers contain different producers: aligned query indices do not establish identical proofs.

| Route | Completed | TIMEOUT | NOT_RUN | Error/crash | ACCEPT | PARTIAL | Proof UNKNOWN | REJECT | Solver UNKNOWN | nnf-pos roots / pending | nnf-neg roots / pending |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| legacy | 4 | 0 | 0 | 0 | 244 | 41 | 0 | 0 | 3 | N/A | N/A |
| current-core | 3 | 1 | 0 | 0 | 233 | 42 | 0 | 0 | 3 | 2584 / 0 | 76 / 3 |
| current-definition | 2 | 2 | 0 | 0 | 241 | 34 | 0 | 0 | 5 | 2702 / 0 | 73 / 2 |

Legacy/Definition completed pairs **2/4**, aligned UNSAT queries **167**, raw query-index ACCEPT differences **0**, solver/query differences **1**. Interrupted-prefix results are retained; unobserved tails are not successes. No per-rule coverage gain or identical-proof loss is inferred from these producer-dependent runs.
Legacy NNF data unavailable. Per-query results, diagnostic obligations, pins, raw logs and input hashes: `files\retained-timeout-gap-controls-01`.

**Diagnostic completed Nov 15 11:29:34 PST:** ABI01 captured `Math.Lemmas-3`
queries 2/4 from both producers; Core completed and Definition timed out after
both captures. Each origin's two documents replayed in all three kernels:
legacy/Core were PARTIAL on both; Definition was PARTIAL on q2, ACCEPT on q4.
Per origin, `nnf-pos` **19 roots / 0 pending** in all kernels; `nnf-neg`
**2 / 2** legacy/Core and **2 / 1** Definition. No new rules implemented.
These are older ABI01 diagnostics, not retained-checker performance evidence;
producer histories can differ. `files\math-lemmas-hotspot-isolation-01.json`.
<!-- END RETAINED TIMEOUT GAP CONTROLS -->

<!-- BEGIN ABI CORRECTED CORPUS -->
## ABI-corrected end-to-end corpus rollout (live)

Updated `2026-11-15T08:57:09-08:00`. All **583 inputs selected**; historical old ACCEPT sessions first, then input size. Pinned old/current binaries, identical input hashes, serial 900-s stages; 10,000-ms solver / 60-s session / 4,096-MiB caps. Solver proof shapes can differ; this is **not** the identical-document timing experiment above. First observed full-window session outcome retained per input/arm; stage-censored prefixes are retained until a full-window rerun. Overlapping reruns, historical and frozen counts are not added.

Binary SHA-256: old `0b5ceec2db9d2fadf279dbf37a843022a3ebb02adcb13349c9b9ed2676b0ada3`, new `d87b731ba6aa0185b496bf8d0342c4934b09fa49db20e8d76d7a89bb6647ef89`.

| Runtime | Completed | TIMEOUT | Stage-cut | Error/crash | NOT_RUN | Proof ACCEPT | PARTIAL | UNKNOWN | REJECT | Solver UNKNOWN | nnf-pos roots/pending | nnf-neg roots/pending |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| legacy | 547 | 36 | 0 | 0 | 0 | 10856 | 520 | 0 | 0 | 450 | N/A | N/A |
| current-core | 546 | 37 | 0 | 0 | 0 | 10808 | 509 | 0 | 0 | 464 | 120719/10 | 5746/74 |
| current-definition | 538 | 45 | 0 | 0 | 0 | 10774 | 382 | 0 | 0 | 443 | 119178/0 | 5625/19 |

Proof/root totals include emitted timeout prefixes; NOT_RUN is not success. Solver UNKNOWN is separate. Current per-instance results are in the [583-row ledger](PORTING_INSTANCES.csv).
current-core vs old: **545** complete pairs, **9149** aligned UNSAT, **11** observed query-index ACCEPT differences, **45** solver/query differences. Any loss requires identical-proof isolation before calling it a missing rule.
current-core: **2 old-complete / candidate-interrupted sessions**, **18** old UNSAT queries in unobserved tails; these are not passes.
current-core: **5** of those differences reproduced as producer-dependent: identical captures agree in every kernel, but producer histories include contrasting query verdicts. Raw index differences remain counted.
- `pulse/queries-Pulse.Lib.BoundedIntegers.smt2` q11: `files\abi-bounded-integers-isolation-01.json` (2026-11-15T03:23:09-08:00).
- `pulse/queries-Pulse.Lib.FractionalAnchoredPreorder-1.smt2` q9: `files\abi-fractional-anchored1-isolation-01.json` (2026-11-15T03:49:51-08:00).
- `pulse/queries-Pulse.Lib.PCM.Fraction.smt2` q8: `files\abi-fraction-isolation-01.json` (2026-11-15T02:16:32-08:00).
- `pulse/queries-PulseCore.Heap.smt2` q34: `files\abi-heap-isolation-01.json` (2026-11-15T03:26:39-08:00).
- `queries-FStar.UInt128-5.smt2` q46: `files\abi-uint128-5-isolation-01.json` (2026-11-15T02:57:33-08:00).
current-core: **6** differences investigated but **unresolved**: the original contrasting verdicts did not reproduce in bounded producer captures. No old ACCEPT loss occurred on captured identical documents; target-query verdict/pending vectors agree across kernels. This does not discharge the original raw losses or classify them as producer-dependent. See investigation evidence below.
- `pulse/queries-Pulse.Lib.FractionalAnchoredPreorder.smt2` q10: `files\abi-fractional-anchored-isolation-02.json` (2026-11-15T01:14:12-08:00).
- `queries-FStar.FiniteSet.Base-2.smt2` q22: `files\abi-finite-set-base2-isolation-01.json` (2026-11-15T03:20:22-08:00).
- `queries-FStar.Math.Lemmas-3.smt2` q18: `files\abi-math-lemmas3-isolation-02.json` (2026-11-15T06:55:53-08:00).
- `queries-FStar.Matrix.smt2` q4: `files\abi-matrix-isolation-01.json` (2026-11-15T02:19:25-08:00).
- `queries-FStar.SizeT.smt2` q21: `files\abi-sizet-isolation-01.json` (2026-11-15T01:53:44-08:00).
- `queries-FStar.UInt-1.smt2` q9: `files\abi-uint1-isolation-01.json` (2026-11-15T01:51:45-08:00).
current-definition vs old: **538** complete pairs, **8942** aligned UNSAT, **14** observed query-index ACCEPT differences, **39** solver/query differences. Any loss requires identical-proof isolation before calling it a missing rule.
current-definition: **9 old-complete / candidate-interrupted sessions**, **73** old UNSAT queries in unobserved tails; these are not passes.
current-definition: **5** of those differences reproduced as producer-dependent: identical captures agree in every kernel, but producer histories include contrasting query verdicts. Raw index differences remain counted.
- `pulse/queries-Pulse.Lib.FractionalAnchoredPreorder-1.smt2` q9: `files\abi-fractional-anchored1-isolation-01.json` (2026-11-15T03:49:51-08:00).
- `queries-FStar.List.Pure.Properties.smt2` q18: `files\abi-list-pure-isolation-01.json` (2026-11-15T03:16:51-08:00).
- `queries-FStar.Math.Lib.smt2` q18: `files\abi-mathlib-isolation-01.json` (2026-11-15T01:58:22-08:00).
- `queries-FStar.UInt128-5.smt2` q45: `files\abi-uint128-5-isolation-01.json` (2026-11-15T02:57:33-08:00).
- `queries-FStar.UInt128-5.smt2` q46: `files\abi-uint128-5-isolation-01.json` (2026-11-15T02:57:33-08:00).
current-definition: **9** differences investigated but **unresolved**: the original contrasting verdicts did not reproduce in bounded producer captures. No old ACCEPT loss occurred on captured identical documents; target-query verdict/pending vectors agree across kernels. This does not discharge the original raw losses or classify them as producer-dependent. See investigation evidence below.
- `queries-FStar.Algebra.CommMonoid.Fold.smt2` q11: `files\abi-fold-isolation-01.json` (2026-11-15T02:53:29-08:00).
- `queries-FStar.FiniteSet.Base-2.smt2` q22: `files\abi-finite-set-base2-isolation-01.json` (2026-11-15T03:20:22-08:00).
- `queries-FStar.FiniteSet.Base-2.smt2` q23: `files\abi-finite-set-base2-isolation-01.json` (2026-11-15T03:20:22-08:00).
- `queries-FStar.List.Tot.Properties.smt2` q29: `files\abi-list-tot-isolation-01.json` (2026-11-15T03:31:20-08:00).
- `queries-FStar.Matrix.smt2` q4: `files\abi-matrix-isolation-01.json` (2026-11-15T02:19:25-08:00).
- `queries-FStar.Seq.Base.smt2` q21: `files\abi-seq-base-isolation-01.json` (2026-11-15T04:13:43-08:00).
- `queries-FStar.Sequence.Base.smt2` q37: `files\abi-sequence-base-isolation-01.json` (2026-11-15T03:53:40-08:00).
- `queries-FStar.UInt-1.smt2` q9: `files\abi-uint1-isolation-01.json` (2026-11-15T01:51:45-08:00).
- `queries-FStar.UInt128-5.smt2` q47: `files\abi-uint128-5-isolation-01.json` (2026-11-15T02:57:33-08:00).

Observed pending judgments by rule (proof shapes may differ):

| Rule | Old PARTIAL | Core PARTIAL | Definition PARTIAL |
| --- | ---: | ---: | ---: |
| `arith/farkas` | 13 | 5 | 8 |
| `arith/lp-monomial-interval` | 1 | 5 | 5 |
| `assumed:nlsat` | 405 | 387 | 437 |
| `intro-def` | 9 | 9 | 0 |
| `nnf-neg` | 75 | 74 | 19 |
| `nnf-pos` | 10 | 10 | 0 |
| `quant-intro` | 219 | 215 | 39 |
| `rewrite` | 15 | 22 | 14 |
| `sk` | 77 | 76 | 14 |
| `th-lemma` | 1073 | 1031 | 1073 |
| Unattributed | 0 | 0 | 0 |
| Total pending | 1897 | 1834 | 1609 |

Rule-level REJECTED attribution is not available from these CLI logs; REJECT proof totals are shown above. Full-corpus parity is **not yet established**. Evidence: session `files\abi-corrected-corpus-summary-01.json` and its listed pinned raw-log cohorts.
<!-- END ABI CORRECTED CORPUS -->

**Pairing scope:** ACCEPT/solver differences use both-COMPLETED sessions only.
Timeout prefixes contribute proof/rule totals, not paired differences;
prefix parity remains unestablished.

### Timeout-prefix audit (separate comparison)

Final stage-24 snapshot **Nov 15 08:57:19 PST**, 46 interrupted inputs; same canonical pins/caps.

| Candidate | Interrupted pairs | Missing-arm pairs | Aligned UNSAT | Raw ACCEPT contrasts | Solver differences | Unobserved old UNSAT tail | Unfinished proofs |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Core | 38 | 0 | 2096 | 10 | 43 | 79 | 0 |
| Definition | 45 | 0 | 2150 | 6 | 42 | 242 | 0 |

These pairs complement the both-completed pairs; tail counts **include**, not add
to, the old-complete gaps above. TIMEOUT remains TIMEOUT. Query indices do not
establish identical proofs.
`OrdSet-3` and `Seq.Properties-1` TIMEOUT in all modes.
`HashTable-1`, `Sort.Merge.Array`, `RWLock-2`, and `Typing.FV-1` TIMEOUT in all modes.
`Sort.Merge.Array` adds two Definition prefix-tail queries.
`Sort.Merge.Slice` TIMEOUT in all modes; counterparts now observed, with four
old UNSAT tail queries unobserved by each candidate. Original Core outcome retained.
`SeqMatch` and `IndirectionTheorySep-4` TIMEOUT in all modes; no new ACCEPT contrast.
`Reflection.Typing-2`: all modes TIMEOUT, 70 proofs each; old/Core
69 ACCEPT / 1 PARTIAL, Definition 70 ACCEPT. No new ACCEPT contrast.
`Pulse.Typing.Combinators-4`: old/Core completed (2 ACCEPT / 1 PARTIAL),
Definition TIMEOUT after one ACCEPT; two old UNSAT tail queries unobserved.
`Reflection.TermEq-1`: all modes TIMEOUT; old/Core 41 ACCEPT / 7 PARTIAL,
Definition 25 ACCEPT / 1 PARTIAL, with 22 old UNSAT tail queries unobserved.
`Matrix-3`: all modes TIMEOUT; old/Core/Definition 54/50/38 proofs.
Core adds two old UNSAT tail queries, Definition 16; solver differences stay separate.
`HashTable.Spec-2`: all modes TIMEOUT; old/Core/Definition 74/65/69 proofs.
**Definition raw contrast q62:** old ACCEPT / Definition PARTIAL;
proof ordinal 59 has five `assumed:nlsat` and two `th-lemma` obligations.
Pending NNF **0/0**. At **08:40:31 PST**, three selected q62 documents
ACCEPT in all three kernels (nine replays); original contrast remains unresolved.
All native origins TIMEOUT: **76/79/76** query responses; q62 observed in each.
**Core/Definition raw contrasts:** `PriorityQueue` q10/q11/q15, one `th-lemma`
obligation per target/mode. Five division-equality shapes; Definition q11 is
a clause shape. Target query/proof ordinals agree; pending NNF **0/0**.
At **08:45:44 PST**, nine captured documents agree in all kernels (27 proof checks);
all three targets have contrasting ACCEPT/PARTIAL producer captures.
Classified producer-dependent in both modes; original raw contrasts retained.
All native origins TIMEOUT: **61/58/56** query responses; all targets observed.
`HashTable`: all modes TIMEOUT, old/Core/Definition 44/45/46 proofs;
no additional ACCEPT contrast. Query-index differences are not kernel differences.
`UInt-5`: all modes TIMEOUT, old/Core/Definition 61/60/65 proofs, all ACCEPT;
no additional ACCEPT contrast. Solver UNKNOWN remains separate.
`Heap-5`: all modes TIMEOUT; old/Core 89/87 ACCEPT plus eight PARTIAL each,
Definition 98 ACCEPT. No new ACCEPT contrast; Core adds two old UNSAT tail queries.
`HashTableChained`: all modes TIMEOUT; old 82 ACCEPT / 1 PARTIAL,
Core/Definition 79/78 ACCEPT; no new contrast, four old tail queries each.
`Math.Fermat-3`: all modes TIMEOUT; old 10 ACCEPT / 3 PARTIAL,
Core 8 ACCEPT / 2 PARTIAL, Definition no emitted verdict.
Two old UNSAT tail queries unobserved by Core, 13 by Definition; not passes.
`Math.Lemmas-2`: Core COMPLETED; old/Definition TIMEOUT, adding 26 Definition
old UNSAT tail queries. This is not identical-proof native speed evidence.
`Math.Lemmas-3` adds 21 old-complete Definition tail queries, not passes.
**Investigated 16/16 affected-mode contrasts:** nine producer-dependent,
seven unresolved. Producer-dependent: `OrdSet-3` and `PriorityQueue` targets
in both modes, plus `Math.Lemmas-1` q26 in Core.
At **08:02:30 PST**, both `Math.Lemmas-2` q56 documents replay PARTIAL/1
in all three kernels (six proof checks); original contrast remains unresolved.
Old/Core captures completed 61 queries each; Definition TIMEOUT after 34,
q56 unobserved. Captured pending NNF **0/0**. Stage 22 prerequisite investigated,
not resolved; no coverage gain inferred.
At **07:36:51 PST**, eight `Math.Lemmas-1` documents agree in all kernels
(24 proof replays / nine arms): q14/q72 ACCEPT throughout; q26 PARTIAL/1 from
legacy, ACCEPT from Core/Definition. q14/q72 remain not-reproduced/unresolved.
Definition supplied no q72 document; all three producer captures TIMEOUT.
`Math.Lemmas-1` adds 18 Definition old UNSAT tail queries, not passes.
At **06:17:52 PST**, q63's three captured documents replay identically across
all kernels: legacy-origin PARTIAL/2, Core-origin PARTIAL/1, Definition-origin
ACCEPT/0. Nine replay arms; no identical-document old ACCEPT loss.
Raw contrasts remain counted; no missing rule or coverage gain inferred.
The eight earlier selected complete documents
ACCEPT in every kernel (15 replay arms), zero identical-document losses.
`Preorder-1` q52: two documents; Definition producer stopped before q52.
`UInt128-12` q13/q27: six documents; reused all three full-cap TIMEOUT captures
after fixing auxiliary selector handling of large Zarith values.
No new rule coverage or resolved raw contrasts claimed.
Evidence: session `files\abi-corrected-timeout-prefix-audit-24-final.json`
(ledger and selection hashes retained), `files\abi-preorder1-prefix-isolation-01.json`,
`files\abi-uint128-12-prefix-recovery-01.json`,
`files\abi-ordset3-prefix-isolation-01.json`,
`files\abi-math-lemmas1-prefix-isolation-01.json`,
`files\abi-math-lemmas2-prefix-isolation-01.json`,
`files\abi-hashtable-spec2-prefix-isolation-01.json`,
`files\abi-priorityqueue-prefix-isolation-01.json`.
Prior classifications retain the immutable stage-14 reference; q63 uses stage 17.
Later stages now automatically block on any uninvestigated prefix ACCEPT contrast.
Stage-censored pairs stay separate pending full-window reruns.

## Rule coverage

**Recovered 15 legacy-ACCEPT proofs:** `NonInformative` **+1**,
`MonotonicGhostRef` **+14**, in both core and definition modes.
Measured on **127 identical frozen proofs / nine sessions**.

| Rule | Root-coverage blockers removed vs preceding state | Still blocked in measured cases |
| --- | ---: | ---: |
| `quant-intro` | **35** | **0** |
| `nnf-pos` | **14** | **0** |

These are certificate/root-soundness gains, not new local-rule acceptance.
The fallback prunes unused, unscoped certificates and reruns the unchanged full
gate; assertions, scope checks and rejection behavior are preserved by proof.
All **18 guarded comparisons passed**; only zero-obligation UNKNOWN-to-ACCEPT
promotions occurred. The previous 58-proof guard stayed identical.

Across **2,109 `nnf-pos` / 60 `nnf-neg` outer roots**, local pending counts remain
**definition: 0 / 0; core: 10 / 5**. SMT-LIB per-rule counts remain unmeasured.
Other `rewrite`/Farkas partials are not targets without demonstrated legacy ACCEPT.
**Open query-level difference:** `PCM.FractionalPreorder`, query 4:
legacy ACCEPT -> definition PARTIAL, one arithmetic `rewrite`.
Three subsequent captures ACCEPT in both modes. Legacy has the same arithmetic
guard; this is not yet isolated as missing checker functionality.

<!-- BEGIN LEGACY FEATURE GAPS -->
**Legacy feature controls:** `2026-11-15T08:57:08-08:00`; 9/9 arms observed. 10,000-ms solver / 60-s session / 4,096-MiB / 900-s stage caps; identical hashed inputs, serial rotated arms. Solver runs can produce different proofs.

| Configuration | Completed | TIMEOUT | Unrun | Error/crash | ACCEPT | PARTIAL | UNKNOWN | REJECT | nnf-pos roots/pending | nnf-neg roots/pending |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| legacy | 0 | 3 | 0 | 0 | 181 | 12 | 0 | 0 | - | - |
| current-core | 0 | 3 | 0 | 0 | 174 | 10 | 0 | 0 | 2856/0 | 90/1 |
| current-definition | 0 | 3 | 0 | 0 | 176 | 0 | 0 | 0 | 2779/0 | 79/0 |

Legacy/current-definition: 0/3 completed pairs; 0 aligned UNSAT queries; 0 observed ACCEPT losses; 0 solver/query differences. Missing arms are unrun, not passed. Counts include interrupted prefixes. Other 580 sessions are outside these controls. Evidence: session `files\abi-corrected-corpus-controls-24`.
<!-- END LEGACY FEATURE GAPS -->

<!-- BEGIN LEGACY FROZEN -->
**Identical-document legacy comparison:** `2026-11-14T19:58:10-08:00`; completed, 30/30 arms closed; 147/147 proofs prevalidated.

| Runtime | Streams done | TIMEOUT | Unrun | ACCEPT | PARTIAL | UNKNOWN | REJECT | Check s | nnf-pos roots/pending | nnf-neg roots/pending |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| legacy | 10/10 | 0 | 0 | 129 | 18 | 0 | 0 | 67.258 | 2785/10 | 70/6 |
| core | 10/10 | 0 | 0 | 129 | 18 | 0 | 0 | 66.126 | 2785/10 | 70/6 |
| definition | 10/10 | 0 | 0 | 144 | 3 | 0 | 0 | 160.858 | 2785/0 | 70/1 |

Stage errors/crashes: **0**. Same hashed documents; compiler-checked declaration layouts; excluded certificate payloads prevalidated absent. Legacy extracted-runtime snapshot, not CLI/solver timing. 60-s stream / 900-s replay-stage / 4,096-MiB caps. Partial-arm totals are censored; compare timings only after matching streams finish. Other 573 sessions outside this frozen cohort. Evidence: session `files\legacy-cached-entry-02.json`.
Legacy ACCEPT losses: **0**.
<!-- END LEGACY FROZEN -->

**Frozen cost split:** audited **Nov 15 05:24 PST**, reusing the Nov 14 timings
above; no new run or full-corpus speed claim.

| Identical-proof subset | Proofs | Old check s | Core check s | Definition check s |
| --- | ---: | ---: | ---: | ---: |
| Legacy ACCEPT | 129 | 18.980 | 23.157 | 23.053 |
| Legacy PARTIAL, Definition ACCEPT | 15 | 24.032 | 19.915 | 59.200 |
| Still PARTIAL | 3 | 24.245 | 23.054 | 78.605 |

Definition is **+21.46%** on the legacy-ACCEPT slice in this single pair.
Still-PARTIAL targets: `FractionalAnchoredPreorder` proof ordinals **11/12**
and `Heap-4` ordinal **6**; all retain the same pending counts.
Optimize without changing verdicts or diagnostic vectors.
Evidence: session `files\matched-proof-cost-audit-01.json`.

<!-- BEGIN ACTIVE REPLAY -->
**Active frozen replay:** `2026-11-15T09:55:53-08:00`; 40/40 arms complete; 0 TIMEOUT; 0 error/crash. 20 exact comparisons passed.

| Route | Rule | Instances compared | Newly handled vs preceding checker | Still pending |
| --- | --- | ---: | ---: | ---: |
| core | `nnf-pos` | 2785 | +0 | 10 |
| core | `nnf-neg` | 70 | +0 | 6 |
| definition | `nnf-pos` | 2785 | +0 | 0 |
| definition | `nnf-neg` | 70 | +0 | 1 |

Only completed comparable pairs contribute; zero compared instances means unmeasured. Evidence: session `files\congruence-entry-frozen-01.json`.
<!-- END ACTIVE REPLAY -->

**Retained shared-diagnostics experiment, Nov 15 05:55:28 PST:**
separate from the active assertion-cache experiment above;
check time includes diagnostics. Allocation is cumulative, not peak memory.

| Route | Before / after check s | Time change | Before / after allocated GB | Allocation change |
| --- | ---: | ---: | ---: | ---: |
| Core control | 65.171 / 64.725 | -0.68% | 27.308 / 27.308 | 0% |
| Definition | 158.424 / 134.924 | **-14.83%** | 73.123 / 67.631 | **-7.51%** |

Same **129 ACCEPT / 18 PARTIAL Core**, **144 / 3 Definition** and full diagnostics.
Three still-PARTIAL targets: **77.096 -> 54.198 s (-29.70%)**.
Retained after strict F*, six native suites, 20 non-field CLI tests, 185-file
legacy-free closure, ABI controls (**16 ACCEPT each mode**) and the SMT-LIB
guard passed **05:55:28 PST**. Solver/help pass; Windows Python remains blocked
by the pre-existing DLL missing `Z3_set_proof_check_callback`.
This is not native full-corpus or legacy-baseline performance evidence.
Candidate `b2674329...` stays separate from the pinned `d87b731b...` corpus.
Controls: session `files\definition-diagnostics-controls-01.json`.

**Native `Heap-4`, Nov 15 06:24:24 PST:** separate fresh control, same input and
60-s / 10,000-ms / 4,096-MiB caps; cumulative corpus counts above are unchanged.

| Runtime | Session | Wall s | ACCEPT / PARTIAL | Proofs observed |
| --- | --- | ---: | ---: | ---: |
| Legacy | COMPLETED | 28.24 | 14 / 6 | 20 |
| Before Definition | TIMEOUT | 60.05 | 18 / 1 | 19 |
| Optimized Definition | COMPLETED | 49.51 | 19 / 1 | 20 |

All 19 common solver/verdict vectors agree; five NNF root-count vectors differ.
Producer histories therefore prevent an exact-proof native speedup claim.
Observed one additional query versus the fresh before arm, **zero newly ported
rules**, pending NNF **0/1**. The canonical before arm still retains its earlier
16-proof TIMEOUT and four unobserved tails; do not merge this candidate control.
Legacy remains faster on this case. Evidence:
session `files\definition-diagnostics-native-heap4-01\results.json`.

## Incremental changes

| Completed (PST) | Change | Rules | Newly handled vs preceding state | Still pending on measured definition route |
| --- | --- | --- | --- | --- |
| 16:29 | Allocation-free name counts | `nnf-pos`, `nnf-neg` | **+0, +0** | **0, 0** |
| 16:35 | Binder-first fallback | `nnf-pos`, `nnf-neg` | **+0, +0** | **0, 0** |
| 16:55 | Cache Boolean contextual checks | `nnf-pos`, `nnf-neg` | **+0, +0** | **0, 0** |
| 17:25 | Root certificate fallback | `quant-intro`, `nnf-pos` | **+35 / +14 root-covered; +15 proofs** | **0 root blockers** |
| 17:32 | Four paired legacy controls | `rewrite` difference | **0 ported; 1 loss / 1 promotion vs legacy** | **1 unisolated difference** |
| 17:34 | Eight unmeasured legacy controls | Coverage audit | **0 ported; 5 existing promotions vs legacy** | **0 NNF pending** |
| 17:51 | Next eight legacy controls | Coverage audit | **0 losses / 20 existing promotions**, 343 aligned | **1 nnf-neg pending** |
| 18:13 | Share root replay contexts | `nnf-pos`, `nnf-neg` | **+0, +0**; exact verdicts/diagnostics | **0, 0** |
| 18:25 | Remaining eight legacy controls | Coverage/performance audit | **0 losses / 7 existing promotions**, 169 aligned | **5 nnf-neg pending, including timeout prefix** |
| 18:30 | Attribute replay CPU | Diagnostic only | **+0**; 17 exact comparisons | **1 instrumented stream TIMEOUT** |
| 18:47 | Generic scope lookup, Heap-4 (not promoted) | `nnf-pos`, `nnf-neg` | **+0, +0**; core +1.66% / definition +0.28% time | **0/1** |
| 18:54 | Called index-zero lookup (not promoted) | `nnf-pos`, `nnf-neg` | **+0, +0**; core +1.99% / definition +2.21% time | **0/1** |
| 19:03 | Inline index-zero lookup, Heap-4 | `nnf-pos`, `nnf-neg` | **+0, +0**; core -1.46% / definition -2.04% time | **0/1** |
| 19:10 | Inline lookup, 127-proof guard | `nnf-pos`, `nnf-neg` | **+0, +0**; core -1.35% / definition -1.05% time | **0/0** |
| 19:17 | Fresh legacy comparison, 147 proofs | `nnf-pos`, `nnf-neg` | **0 legacy ACCEPT losses**; core still **+1.94%** time | **0/1** |
| 19:36 | Eager node cache (not promoted) | `nnf-pos`, `nnf-neg` | **+0, +0**; core -0.38%, definition +1.22% time | **0/1** |
| 19:49 | Deferred exact entry cache | `nnf-pos`, `nnf-neg` | **+0, +0**; core -4.69%, definition -0.80% time | **0/1** |
| 19:58 | Retained cache vs fresh legacy | `nnf-pos`, `nnf-neg` | **0 legacy ACCEPT losses**; core **-1.68%** time on 147 identical proofs | **0/1** |
| 20:03 | Complete rule attribution, 147 proofs | All 25 observed rules | **0 ported**; old/core **58**, definition **8** pending judgments | **1 nnf-neg** |
| 20:05 | Bind-1 historical gap control | `nnf-pos`, `nnf-neg` | **0 ported; ACCEPT in all three arms** | **0/0** |
| 20:31 | Rolling end-to-end controls, 101 inputs | All observed rules | **0 ported; no aligned old-to-core ACCEPT loss**; six solver/query differences | **0/0 NNF**, one definition TIMEOUT |
| 20:43 | Rolling controls, 141 inputs attempted | All observed rules | **0 ported**; 140 old/core complete pairs, no aligned ACCEPT loss | **0/0 NNF**; old/core TIMEOUT **1/1**, definition **2** |
| 20:52 | Rolling controls, 261 inputs attempted | `th-lemma` | **0 ported**; `FStar.UInt-1` q9 old ACCEPT -> new PARTIAL on different produced proofs | **1 unisolated difference** |
| 20:59 | UInt-1 two-producer cross-replay | `th-lemma` | **0 ported**; all 20 identical old/core/definition verdict/pending vectors agree | **0 checker gaps isolated** |
| 21:18 | Capped rolling controls, 323 inputs observed | All observed rules | **0 ported**; one raw producer-classified difference, no unisolated loss | **0/0 NNF**; one legacy arm stage-censored |
| 21:31 | Rolling controls, 362 inputs observed | All observed rules | **0 ported**; old/core 361 complete, definition 360 | Core **0/1 NNF**, definition **0/0**; two unresolved cases |
| 21:35 | Fraction full/target-only cross-replay | `rewrite` | **0 ported**; 18 full-history + 3 target captures agree in all kernels | Original definition q8 loss **unresolved** |
| 21:36 | Matrix three-producer cross-replay | All observed rules | **0 ported**; all 96 captured verdict/pending vectors agree | Original q4 loss **unresolved** |
| 21:53 | Rolling controls, old 402 / candidates 401 observed | All observed rules | **0 ported**; no new uninvestigated ACCEPT differences | NNF pending core **0/8**, definition **0/1**; 77 old UNSAT await each candidate |
| 22:08 | Rolling controls, 418 inputs observed per arm | `th-lemma`, `assumed:nlsat` differences | **0 ported**; two new cases queued for identical-document isolation | Core NNF **0/8**, definition **0/1**; two candidate-only interrupted sessions |
| 22:11 | UInt128-5 three-producer cross-replay | `th-lemma`, `assumed:nlsat` | **0 ported**; all 141 captured vectors agree; q44 producer-dependent | q45-47 original differences **unresolved** |
| 22:12 | Fold three-producer cross-replay | `th-lemma` | **0 ported**; all 39 captured vectors agree | Original q11 difference **unresolved** |
| 22:15 | UInt-3 completed legacy-origin replay subset | `nnf-pos`, `nnf-neg` | **0 losses** on 77 identical proofs; core **+5.00%** check time | **0/0 NNF**; later core capture TIMEOUT |
| 22:32 | Rolling controls, 436 inputs observed per arm | All observed rules | **0 ported**; three new cases queued for isolation | Core NNF **0/9**, definition **0/1**; 147 inputs unrun |
| 22:35 | Pure Properties captured replay | All observed rules | **0 ported**; no old ACCEPT loss on 66 documents; two existing definition promotions | Original q22 loss **unresolved** |
| 22:37 | FiniteSet Base-2 captured replay | All observed rules | **0 ported**; all 71 captured vectors agree | Original q26 loss **unresolved** |
| 22:40 | Tot Properties captured replay | All observed rules | **0 ported**; all 204 captured vectors agree; q23 producer-dependent | Original q47/54/58/63 losses **unresolved** |
| 22:55 | Rolling controls, 456 inputs observed per arm | All observed rules | **0 ported**; two new cases queued for isolation | Core NNF **0/10**, definition **0/1**; 127 inputs unrun |
| 22:58 | FractionalAnchoredPreorder-1 captured replay | All observed rules | **0 ported**; all 99 captured vectors agree; q9 producer-dependent | Original q11 loss **unresolved** |
| 23:00 | Sequence Base captured replay | All observed rules | **0 ported**; all 135 captured vectors agree; q35 producer-dependent | Raw differences retained |
| 23:07 | Root coverage before memo allocation (not retained) | `nnf-pos`, `nnf-neg` | **+0 / +0**; exact `.fsti`, six native suites, 20 CLI tests pass | Slower; see 23:18 |
| 23:18 | Root-gate-first exact replay (not retained) | `nnf-pos`, `nnf-neg` | **+0 / +0**; 20 exact comparisons; core **+7.75%**, definition **+2.88%** time | **10/6 core**, **0/1 definition**; unchanged |
| 23:25 | Pending-only memo cutoff (unpromoted) | `nnf-pos`, `nnf-neg` | **+0 / +0**; exact `.fsti`, six native suites, 20 CLI tests pass | Identical-proof performance pending |
| 23:38 | Pending-only memo cutoff (not retained) | `nnf-pos`, `nnf-neg` | **+0 / +0**; 20 exact comparisons; core **+0.52%**, definition **-0.38%** time | **10/6 core**, **0/1 definition**; unchanged |
| 23:56 | Stage 13 bounded rollout | All observed rules | **0 ported**; 35 completed / 5 TIMEOUT / 20 NOT_RUN arms | Core **0/11 NNF**, definition **0/2**; two new query differences |
| 23:57 | Seq.Base three-producer cross-replay | All observed rules | **0 ported**; no old ACCEPT loss on 230 identical captured documents | q33 producer-dependent; raw difference retained |
| Nov 15 00:01 | List.Tot.Properties-1 cross-replay | All observed rules | **0 ported**; no old ACCEPT loss on 207 captured documents | Original q8 difference unresolved |
| Nov 15 00:16 | Stage 14 bounded rollout | All observed rules | **0 ported**; 34 completed / 6 TIMEOUT / 20 NOT_RUN arms; no new raw losses | Core **0/16 NNF**, definition **0/2** |
| Nov 15 00:33 | Stage 15 and crash reproduction | Native marshalling | **0 ported**; 29 completed / 3 TIMEOUT / 1 CRASH / 27 NOT_RUN arms | Core PrettifyType-2 abort reproduced **3/3** |
| Nov 15 00:45 | Match OCaml runtime headers | Native marshalling | **+5 completed ACCEPT per crash rerun**, 3/3 core repetitions; no proof-gate change | Corrected full-corpus rebaseline pending |
| Nov 15 00:51 | Corrected ABI verification guards | All guard rules | **0 rule changes**; strict F*, 185-file closure, SMT-LIB guard pass | SMT-LIB **2/4/2/1/216** A/P/solver UNKNOWN/TIMEOUT/unrun |
| Nov 15 00:53 | Corrected ABI stage 1, 20 inputs | `nnf-pos`, `nnf-neg` | **0 legacy ACCEPT losses**; 78 ACCEPT each, no query differences | Core **357/41 roots**, definition **364/41**, pending **0/0** |
| Nov 15 01:08 | Corrected ABI stage 2, 80 cumulative inputs | All observed rules | **0 ported**; old/core/definition **1252/1251/1247 ACCEPT** | Core/definition NNF pending **0/0**; one raw core loss, one definition TIMEOUT |
| Nov 15 01:14 | ABI-matched q10 isolation, 43 documents | Legacy coverage audit | **0 ported; 0 identical-document ACCEPT losses** | Raw q10 contrast **not reproduced, unresolved** |
| Nov 15 01:26 | Corrected ABI stage 3, 40 new inputs | `nnf-pos`, `nnf-neg` | **0 ported; 0 new ACCEPT losses**; 956/955/955 old/core/definition ACCEPT | Core **11099/315**, definition **11055/316** roots; pending **0/0** |
| Nov 15 01:31 | Corrected ABI stage 4, 40 new inputs | `nnf-pos`, `nnf-neg` | **0 ported; 0 new ACCEPT losses**; 117 complete / 3 TIMEOUT arms | Each route **395/62** new roots; pending **0/0** |
| Nov 15 01:36 | Corrected ABI stage 5, 80 new inputs | `nnf-pos`, `nnf-neg` | **0 ported; 0 new ACCEPT losses**; 240/240 arms complete | Core **2228/270**, definition **2233/270** new roots; pending **0/0** |
| Nov 15 01:50 | Corrected ABI stage 6, 80 new inputs | All observed rules | **0 ported; 4 new raw ACCEPT losses**, three query targets; 240/240 arms complete | Core **7556/704**, definition **7712/708** new NNF roots; pending **0/0** |
| Nov 15 01:51 | ABI-matched `UInt-1` q9 isolation | Legacy coverage audit | **0 ported; 0 identical-document ACCEPT losses**, 30 documents | Raw contrast **not reproduced, unresolved** in both modes |
| Nov 15 01:53 | ABI-matched `SizeT` q21 isolation | Legacy coverage audit | **0 ported; 0 identical-document ACCEPT losses**, 72 documents | Raw core contrast **not reproduced, unresolved** |
| Nov 15 01:58 | ABI-matched `Math.Lib` q18 isolation | Legacy coverage audit | **0 ported; 0 identical-document ACCEPT losses**, 87 documents | Definition contrast **producer-dependent**; raw loss retained |
| Nov 15 02:13 | Corrected ABI stage 7, 43 new inputs | All observed rules | **0 ported; 3 new raw ACCEPT losses**; 129 complete / 111 NOT_RUN arms | Core **6664/508** new NNF roots, pending **0/1**; definition **6585/506**, pending **0/0** |
| Nov 15 02:16 | ABI-matched `PCM.Fraction` q8 isolation | Legacy coverage audit | **0 ported; 0 identical-document ACCEPT losses**, 18 documents | Core contrast **producer-dependent**; raw loss retained |
| Nov 15 02:19 | ABI-matched `Matrix` q4 isolation | Legacy coverage audit | **0 ported; 0 identical-document ACCEPT losses**, 96 documents | All target captures PARTIAL; original contrasts **unresolved** |
| Nov 15 02:35 | Corrected ABI stage 8 | All observed rules | **0 ported; 0 new raw ACCEPT losses**; 115 complete / 3 TIMEOUT / 122 NOT_RUN arms | Core **6327/348**, definition **6404/352** new NNF roots |
| Nov 15 02:51 | Corrected ABI stage 9 | All observed rules | **0 ported; 5 new raw ACCEPT losses**; 43 complete / 8 TIMEOUT / 189 NOT_RUN arms | Core **3699/354**, definition **3674/355** newly observed NNF roots |
| Nov 15 02:53 | ABI-matched `CommMonoid.Fold` q11 isolation | Legacy coverage audit | **0 ported; 0 identical-document ACCEPT losses**, 42 documents | Original definition contrast **not reproduced, unresolved** |
| Nov 15 02:57 | ABI-matched `UInt128-5` q45/q46/q47 isolation | Legacy coverage audit | **0 ported; 0 identical-document ACCEPT losses**, 141 documents | q45/q46 **producer-dependent**; q47 **unresolved**; raw losses retained |
| Nov 15 03:13 | Corrected ABI stage 10 | All observed rules | **0 ported; 7 new raw ACCEPT losses**; 48 complete / 6 TIMEOUT / 186 NOT_RUN arms | Core **6907/318**, definition **7116/324** new NNF roots |
| Nov 15 03:16 | ABI-matched `List.Pure.Properties` q18 isolation | Legacy coverage audit | **0 ported; 0 identical-document ACCEPT losses**, 69 documents | Definition contrast **producer-dependent**; raw loss retained |
| Nov 15 03:20 | ABI-matched `FiniteSet.Base-2` q22/q23 isolation | Legacy coverage audit | **0 ported; 0 identical-document ACCEPT losses**, 109 documents | All target captures ACCEPT; original contrasts **unresolved** |
| Nov 15 03:23 | ABI-matched `BoundedIntegers` q11 isolation | Legacy coverage audit | **0 ported; 0 identical-document ACCEPT losses**, 48 documents | Core contrast **producer-dependent**; raw loss retained |
| Nov 15 03:26 | ABI-matched `PulseCore.Heap` q34 isolation | Legacy coverage audit | **0 ported; 0 identical-document ACCEPT losses**, 190 documents | Legacy/core contrast **producer-dependent**; definition promotion preserved |
| Nov 15 03:31 | ABI-matched `List.Tot.Properties` q29 isolation | Legacy coverage audit | **0 ported; 0 identical-document ACCEPT losses**, 203 documents | All target captures ACCEPT; original definition contrast **unresolved** |
| Nov 15 03:46 | Corrected ABI stage 11 | All observed rules | **0 ported; 3 new raw ACCEPT losses**; 74 complete / 1 TIMEOUT / 165 NOT_RUN arms | Core **8685/400**, definition **8604/397** new NNF roots |
| Nov 15 03:49 | ABI-matched `FractionalAnchoredPreorder-1` q9 isolation | Legacy coverage audit | **0 ported; 0 identical-document ACCEPT losses**, 99 documents | Both-mode raw contrasts **producer-dependent**; retained |
| Nov 15 03:53 | ABI-matched `Sequence.Base` q37 isolation | Legacy coverage audit | **0 ported; 0 identical-document ACCEPT losses**, 133 documents | Only definition producer supplied q37 proof; original contrast **unresolved** |
| Nov 15 04:09 | Corrected ABI stage 12 | All observed rules | **0 ported; 1 new raw ACCEPT loss**; 26 complete / 6 TIMEOUT / 208 NOT_RUN arms | Core **6880/329**, definition **6434/320** new NNF roots |
| Nov 15 04:13 | ABI-matched `Seq.Base` q21 isolation | Legacy coverage audit | **0 ported; 0 identical-document ACCEPT losses**, 230 documents | All captured proofs ACCEPT; original definition contrast **unresolved** |
| Nov 15 04:30 | Corrected ABI stage 13 | All observed rules | **0 ported; 0 new raw ACCEPT losses**; 30 complete / 7 TIMEOUT / 203 NOT_RUN arms | Core **3805/112**, definition **3928/114** new NNF roots |
| Nov 15 04:46 | Corrected ABI stage 14 | All observed rules | **0 ported; 0 new completed-pair ACCEPT losses**; 26 complete / 4 TIMEOUT / 210 NOT_RUN arms | Core **7079/233**, definition **6961/231** new NNF roots |
| Nov 15 04:46 | Timeout-prefix audit | Legacy coverage audit | **0 ported; 3 newly reported prefix ACCEPT contrasts** (2 Core / 1 Definition) | Separate interrupted pairs; identical-document isolation pending |
| Nov 15 04:51 | ABI-matched `Preorder-1` q52 prefix isolation | Core legacy coverage | **0 ported; 0 identical-document losses** on 2 selected documents / 6 replay arms | Raw contrast unresolved; Definition origin supplied no q52 proof |
| Nov 15 04:55 | `UInt128-12` selector failure | Transport only | **0 proofs replayed**; three full-cap TIMEOUT captures retained | Zarith decoding failed in auxiliary selector; targets still uninvestigated |
| Nov 15 04:59 | ABI-matched `UInt128-12` q13/q27 prefix recovery | Core/Definition legacy coverage | **0 ported; 0 identical-document losses** on 6 selected documents / 9 replay arms | Both raw contrasts unresolved; all 3 prefix contrasts investigated |
| Nov 15 05:16 | Corrected ABI stage 15 | All observed rules | **0 ported; 0 new complete/prefix ACCEPT contrasts**; 15 complete / 6 TIMEOUT / 219 NOT_RUN arms | Core **2418/124**, definition **2447/125** new NNF roots |
| Nov 15 05:32 | Corrected ABI stage 16 | All observed rules | **0 ported; 0 new complete/prefix ACCEPT contrasts**; 38 complete / 4 TIMEOUT / 198 NOT_RUN arms | Core **4474/129**, definition **4356/121** new NNF roots |
| Nov 15 05:55 | Retain shared Definition diagnostics | `nnf-pos`, `nnf-neg` paths | **+0 / +0**; exact diagnostics; check **-14.83%**, allocation **-7.51%** on 147 identical documents | NNF **0 / 1**; 20 comparisons and strict/native/SMT-LIB controls pass |
| Nov 15 06:55 | `Math.Lemmas-3` q18 recovery | `th-lemma` contrast | **0 ported**; one document ACCEPT in all kernels | Original contrast unresolved; two producer targets missing |
| Nov 15 07:12 | Corrected ABI stage 19 | All observed rules | **0 ported; 0 new complete/prefix ACCEPT contrasts**; 21 complete / 10 TIMEOUT / 110 NOT_RUN arms | Core **3877/80**, Definition **3081/76** newly observed NNF roots; Definition pending **0/12** |
| Nov 15 07:30 | Corrected ABI stage 20 | All observed rules | **0 ported; 3 new Core prefix contrasts**; 33 complete / 6 TIMEOUT / 72 NOT_RUN arms | Core **2174/119**, Definition **2867/103** newly observed NNF roots; Definition pending **0/17** |
| Nov 15 07:36 | `Math.Lemmas-1` prefix isolation | `assumed:nlsat`, `th-lemma` contrasts | **0 ported; 0 identical-document losses** on eight documents | q26 producer-dependent; q14/q72 unresolved; targets pending NNF **0/0** |
| Nov 15 07:55 | Corrected ABI stage 21 | All observed rules | **0 ported; 1 new Core prefix contrast**; 15 complete / 8 TIMEOUT / 49 NOT_RUN arms | Core **5491/196**, Definition **5330/170** newly observed NNF roots; Definition pending **0/17** |
| Nov 15 08:19 | Corrected ABI stage 22 | All observed rules | **0 ported; no new ACCEPT contrast**; 11 complete / 10 TIMEOUT / 30 NOT_RUN arms | Core **4049/162**, Definition **3351/128** newly observed NNF roots; pending **10/73** / **0/19** |
| Nov 15 08:36 | Corrected ABI stage 23 | All observed rules | **0 ported; 7 new affected-mode prefix contrasts**; 9 complete / 12 TIMEOUT / 9 NOT_RUN arms | Core **2889/119**, Definition **3086/124** newly observed NNF roots; pending **10/73** / **0/19** |
| Nov 15 08:57 | Corrected ABI stage 24 | All observed rules | **0 ported; no new ACCEPT contrast**; 9 TIMEOUT / 0 NOT_RUN arms; all 583 observed per mode | Core **2856/90**, Definition **2779/79** newly observed NNF roots; pending **10/74** / **0/19** |

Prior speed-only pairs: name counting **-9.58% / -13.69%** core/definition;
binder-first **-7.38%** definition; Boolean caching **-3.77% / -1.22%**.
Latest fallback pair: core **49.689 -> 52.142 s (+4.94%)**;
definition **112.677 -> 111.330 s (-1.20%)**, now certifying 15 additional proofs.
Single-pair checker timings, not full-corpus speedup or significance claims.

## Benchmark status

| Measured cohort | ACCEPT | PARTIAL | UNKNOWN | TIMEOUT | Crash/error | Unmeasured |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| `fstar-build`: core/fallback, 127 proofs | 115 | 12 | 0 | 0 | 0 | 574 sessions |
| `fstar-build`: definition/fallback, same 127 proofs | 125 | 2 | 0 | 0 | 0 | 574 sessions |
| Four fresh sessions, each legacy/core/definition | 56 | 6 | 0 | 0 | 0 | 579 sessions |
| Eight fresh sessions, legacy | 68 | 27 | 0 | 0 | 0 | 575 sessions |
| Same eight sessions, definition | 73 | 22 | 0 | 0 | 0 | 575 sessions |
| Next eight sessions, legacy | 311 | 34 | 0 | 0 | 0 | 575 sessions |
| Same next eight sessions, definition | 331 | 13 | 0 | 0 | 0 | 575 sessions |
| Last eight sessions, legacy | 169 | 20 | 0 | 0 | 0 | 575 sessions |
| Same last eight, definition (includes timeout prefix) | 177 | 8 | 0 | 1 | 0 | 575 sessions; 4 trailing legacy UNSAT queries unobserved |
| Frozen `Heap-4`: legacy/core, each 20 proofs | 14 | 6 | 0 | 0 | 0 | No loss on these documents |
| Same frozen `Heap-4`: definition | 19 | 1 | 0 | 0 | 0 | End-to-end timeout remains open |
| Frozen 147 proofs: legacy/core, each | 129 | 18 | 0 | 0 | 0 | 573 sessions |
| Same 147 proofs: definition | 144 | 3 | 0 | 0 | 0 | 573 sessions |
| `Pulse.Checker.Bind-1`, each legacy/core/definition | 1 | 0 | 0 | 0 | 0 | 582 other sessions; one solver UNKNOWN in each arm |
| Frozen UInt-3 legacy-origin, each old/core/definition | 77 | 0 | 0 | 0 | 0 | Only completed replay subset; core producer capture TIMEOUT, definition capture unrun |

<!-- BEGIN SAMPLE PARTIAL CONTROLS -->
### SMT-LIB sample PARTIAL investigation

Updated `2026-11-15T11:40:33-08:00`; **source diagnostics completed**. 103 cases selected from the 2026-11-15 Definition sample PARTIAL outcomes. Source reruns use pinned inputs/checkers, 10,000-ms solver / 60-s case / 4,096-MiB / 900-s stage caps. Legacy and Definition can produce different proofs; these are not identical-proof comparisons.

| Route | ACCEPT | PARTIAL | UNKNOWN | TIMEOUT | REJECT | Error/crash | NOT_RUN |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| legacy | 100 | 3 | 0 | 0 | 0 | 0 | 0 |
| definition | 0 | 103 | 0 | 0 | 0 | 0 | 0 |

PARTIAL columns count weighted pending obligations (and, in parentheses, partial proofs containing the rule); multiple rules may occur in one proof. Accepted rule instances are **not yet measured**; they cannot be inferred from these aggregated diagnostics.

| Rule | Legacy ACCEPT | Legacy PARTIAL (proofs) | Definition ACCEPT | Definition PARTIAL (proofs) |
| --- | ---: | ---: | ---: | ---: |
| `apply-def` | N/A | 0 (0) | N/A | 203 (9) |
| `def-axiom` | N/A | 0 (0) | N/A | 3 (3) |
| `der` | N/A | 0 (0) | N/A | 7 (6) |
| `intro-def` | N/A | 0 (0) | N/A | 272 (16) |
| `quant-intro` | N/A | 0 (0) | N/A | 42 (16) |
| `rewrite` | N/A | 3 (3) | N/A | 1866 (66) |
| `th-lemma` | N/A | 0 (0) | N/A | 3514 (34) |

Case logs, input hashes, diagnostics and checker pins: `files\sample-partial-controls-01`. Identical-document capture/replay and accepted-rule attribution remain planned; no parity or speedup is inferred.

**11:42:10 PST, identical-document calibration:** five AUFLIA documents,
10/10 replay arms complete: legacy **5 ACCEPT**, Definition **5 PARTIAL**.
The same captured documents and compiler-checked wire layouts were used; unsupported
Gomory/finite-field payloads were excluded. These five are a subset, not the
entire 103-case investigation. No new rule implemented.

| Outer rule | Legacy ACCEPT / PARTIAL entries | Definition ACCEPT / PARTIAL entries |
| --- | ---: | ---: |
| `der` | 4 / 0 | 0 / 4 |
| `quant-intro` | 26 / 0 | 23 / 3 |
| `nnf-pos` | 7 / 0 | 7 / 0 |
| Other observed rules | 200 / 0 | 200 / 0 |

Entry PARTIAL counts are distinct diagnostic indices, not weighted obligations;
these five Definition proofs remained PARTIAL, so no recovery-promoted entries
are counted as individually accepted. The initial harness build failed on OCaml
syntax before proof replay. Evidence: `files\sample-identical-replay-01.json`
and `files\sample-identical-replay-02.json`.
**11:56:08 PST:** the bounded identical-document stage attempted 91 of its
98 cases; all 91 completed both replay arms. The remaining seven were
completed at **11:58:35 PST**; now **0 NOT_RUN**. Evidence:
`files\sample-identical-replay-03.json` and `files\sample-identical-replay-04.json`.

**11:57:13 PST:** on four identical QF_AX documents, Definition **4 PARTIAL**
and the existing array route **4 ACCEPT** (8/8 replay arms). No implementation
change yet; coverage gain is confined to this control. Definition proof-check
times total **5.803 s**, array **10.558 s**, single serial observation, not
an end-to-end speed claim. Both routes observed `nnf-pos` / `nnf-neg` **0 / 0**.
`files\sample-array-controls-01.json`.

**12:01:07 PST:** the internal Definition-plus-array candidate passed strict F*
checking, six native test suites and non-field CLI tests. Its soundness
contract is explicitly for standard models; existing modes are unchanged.
**12:03:01 PST:** the new preservation lemma also passed strict F*. Matched
frozen-proof measurements are running. **12:05:12 PST snapshot:** all four
QF_AX documents improved PARTIAL to ACCEPT; checker time was 5.575 s baseline
versus 15.665 s candidate. **12:08:15 PST:** all ten fstar-build streams
completed in both arms: 144 ACCEPT / 3 PARTIAL, identical diagnostics,
`nnf-pos` 2785 / 0 pending and `nnf-neg` 70 / 1 pending in each. Checker times
were 128.197 s baseline / 160.274 s candidate; no timeouts or errors.
This is neither full-corpus parity nor an end-to-end comparison. The fallback
rechecks Core for pending proofs. **12:10:51 PST:** a candidate that reuses the
Core verdict passed strict F*, six native suites and non-field CLI tests.
Exact identical-proof comparisons against the first candidate are running;
it is not yet retained. **12:12:39 PST snapshot:** all four QF_AX verdicts and
diagnostics match, with checker time 15.536 s before / 9.993 s after Core
reuse. **12:16:58 PST:** all ten fstar-build streams match exactly: 144
ACCEPT / 3 PARTIAL, `nnf-pos` 2785 / 0 pending and `nnf-neg` 70 / 1 pending
in each. Checker time was 159.719 / 137.807 s; no timeout, error or unrun
replay. A bounded comparison against retained Definition on the 103 sample
PARTIAL documents restarted after an incorrect capture directory stopped the
first attempt before replay; all 103 capture hashes now pass preflight.
**12:33:12 PST:** all 103 selected cases attempted. Definition: 103 PARTIAL;
candidate: 32 ACCEPT / 70 PARTIAL / 1 TIMEOUT. Promotions: QF_AUFLIA 11,
QF_AX 21. The candidate timeout follows a 53.207-s Definition PARTIAL. On
102 completed pairs, checker times were 259.656 / 432.198 s; there were no
errors or unrun cases. These are root promotions, not claims that individual
original proof entries are now locally supported. Some unsuccessful non-array
fallbacks approximately double checking time. Keep this experimental route
unexposed while investigating performance. **12:34 PST:** profiling two
retained fstar-build Math.Lemmas proofs for the next performance target.
**12:36:48 PST:** all four instrumented Core/Definition replays matched their
baseline verdicts and diagnostics. Definition inclusive CPU time for
`consequence` was 9.871 / 7.909 s, `monotonicity` 5.706 / 3.858 s, and
`nnf_verdict` 0.980 / 0.741 s on queries 2 / 4. Categories overlap and
instrumentation adds cost. Query 2 remained PARTIAL; query 4 was ACCEPT.
**12:40:13 PST:** an exact-verdict cached replay candidate for Definition's
augmented roots passed strict F*, six native suites and non-field CLI tests.
Identical-proof timing and diagnostic guards are running on the two profiled
proofs and ten frozen fstar-build streams; the candidate is not yet retained.
**12:47:05 PST:** all 149 proofs match exactly. Math.Lemmas allocations were
unchanged and checker time was 43.203 / 42.256 s; the 147-proof fstar-build
cohort was 128.616 / 127.138 s, with `nnf-pos` 2785 / 0 pending and
`nnf-neg` 70 / 1 pending in each. No timeout or error. This small, single-run
difference is not a speedup claim. **12:47 PST:** a second candidate applies
the exact cached-document contract to Skolem/binder replay and is undergoing
strict verification and native tests; it is not retained. **12:49 PST:**
strict source checks passed, but extraction stopped on a stale RootReplay
checked cache. **12:52:16 PST:** the retry verified the dependency, passed
strict F*, extraction, six native suites and non-field CLI tests. Exact
matched-proof replay is running. **12:54:48 PST snapshot:** both Math.Lemmas
proofs match exactly; checker time is 43.133 / 36.910 s and allocations are
19.497 / 17.157 GB cumulatively. **12:58:30 PST:** all ten other fstar-build
streams match (144 ACCEPT / 3 PARTIAL). `nnf-pos` 2785 / 0 pending and
`nnf-neg` 70 / 1 pending in each; checker time 129.081 / 120.373 s. No
timeout or error. These are single-run checker-only measurements, not
full-corpus parity. **12:59 PST:** paired legacy, retained Definition and
candidate Definition source controls are running on 11 sessions.
**13:09:46 PST:** legacy 11 completed; retained Definition 10
completed / 1 TIMEOUT; candidate Definition 11 completed. Across 11
legacy/candidate completed pairs, 176 aligned UNSAT queries include 17
PARTIAL-to-ACCEPT differences and one ACCEPT-to-PARTIAL difference (Math.Lemmas
query 26); five solver/query differences were also observed. Proof producers may
differ; the ACCEPT-to-PARTIAL difference needs identical-document
isolation. Retained Definition's interrupted prefix reported solver UNKNOWN at
that query, so it cannot establish a checker regression. Candidate emitted
`nnf-pos` 2778 / 0 pending and `nnf-neg` 99 / 2 pending. On ten completed
retained/candidate pairs there were no verdict differences; session wall time
was 156.736 / 149.523 s. Legacy/candidate wall time on 11 pairs was
146.759 / 205.306 s. Solver/model, CLI help and Windows
Python binding smoke checks passed.
**13:14:14 PST:** Query-26 isolation: on the legacy-produced document,
legacy, retained Definition and candidate all ACCEPT; retained/candidate
diagnostics match exactly. The candidate producer instead returned solver
UNKNOWN at query 26 during capture, so its original UNSAT/PARTIAL document
remains unobserved and the source difference remains unresolved. Both capture
query counters passed controls; the legacy capture passed wire validation.
**13:16:15 PST:** A second candidate capture again returned solver UNKNOWN
at query 26; no candidate document was captured.
Evidence: `files\math-lemmas-retained-profile-01.json`,
`files\definition-cached-root-01.json`, `files\definition-cached-root-frozen-01.json`,
`files\skolem-cached-replay-01.json`, `files\skolem-cached-replay-02.json`,
`files\skolem-cached-frozen-01.json`, `files\skolem-cached-native-controls-01`,
`files\skolem-cached-basic-controls-01.json`,
`files\math-lemmas-q26-skolem-isolation-01.json`,
`files\math-lemmas-q26-skolem-isolation-02.json`.
This is checker-only evidence on small cohorts, not corpus parity.
The three remaining fstar-build PARTIAL proofs are two in
`FractionalAnchoredPreorder` (two `rewrite` obligations, also pending in
legacy) and one in `Heap-4` (`nnf-neg`, `quant-intro`, `sk` obligations;
legacy also leaves that stream PARTIAL). Counts are weighted obligations.
Evidence:
`files\definition-array-candidate-01.json`, `files\definition-array-frozen-01.json`,
`files\definition-array-reuse-01.json`, `files\definition-array-reuse-frozen-01.json`,
`files\definition-array-sample-01.json`, `files\definition-array-sample-02.json`.

**11:58:35 PST:** all **103** selected partial-case proofs were replayed:
**100** legacy ACCEPT / Definition PARTIAL; **3** PARTIAL in both. This is
the partial-case subset, not the full sample or an end-to-end speed comparison.

<details><summary>All outer-rule entries in the 103 matched partial-case proofs</summary>

| Rule | Legacy ACCEPT / PARTIAL | Definition ACCEPT / PARTIAL |
| --- | ---: | ---: |
| `and-elim` | 8732 / 0 | 8732 / 0 |
| `apply-def` | 272 / 0 | 69 / 203 |
| `arith/farkas` | 36550 / 0 | 36550 / 0 |
| `asserted` | 5393 / 0 | 5393 / 0 |
| `commutativity` | 1448 / 0 | 1448 / 0 |
| `def-axiom` | 3484 / 0 | 3481 / 3 |
| `der` | 7 / 0 | 0 / 7 |
| `elim-unused` | 6 / 0 | 6 / 0 |
| `hypothesis` | 6519 / 0 | 6519 / 0 |
| `iff-false` | 198 / 0 | 198 / 0 |
| `iff-true` | 50 / 0 | 50 / 0 |
| `intro-def` | 272 / 0 | 0 / 272 |
| `lemma` | 31251 / 0 | 31251 / 0 |
| `monotonicity` | 176676 / 0 | 176676 / 0 |
| `mp` | 100554 / 0 | 100554 / 0 |
| `mp~` | 60 / 0 | 60 / 0 |
| `nnf-neg` | 9 / 0 | 9 / 0 |
| `nnf-pos` | 44 / 0 | 44 / 0 |
| `not-or-elim` | 170 / 0 | 170 / 0 |
| `pull-quant` | 6 / 0 | 6 / 0 |
| `quant-inst` | 113 / 0 | 113 / 0 |
| `quant-intro` | 385 / 0 | 343 / 42 |
| `refl` | 8 / 0 | 8 / 0 |
| `rewrite` | 30205 / 3 | 28342 / 1866 |
| `sk` | 15 / 0 | 15 / 0 |
| `symm` | 84326 / 0 | 84326 / 0 |
| `th-lemma` | 5533 / 0 | 2019 / 3514 |
| `trans` | 38174 / 0 | 38174 / 0 |
| `trans*` | 102748 / 0 | 102748 / 0 |
| `unit-resolution` | 213615 / 0 | 213615 / 0 |

Counts are outer entries, not whole-proof verdicts; PARTIAL is the number of
distinct pending entry indices. Both routes checked all entries in these
PARTIAL Definition proofs; no Definition recovery promotion is counted.
</details>
<!-- END SAMPLE PARTIAL CONTROLS -->

<!-- BEGIN PERIODIC SMTLIB -->
### Six-hour SMT-LIB measurements (Definition)

Updated `2026-11-15T11:13:21-08:00`; cycle `periodic-smtlib-20261115T180643Z` **completed**; checker `1147416d9a4c`. Schedule **#3**, every six hours.
Fixed hashed inputs; serial native cases; 10,000-ms queries / 60-s cases / 4,096-MiB / 3,600-s budget per cohort. A 30-s quiet pause precedes each cohort. Finite fields are excluded; QF_BV is excluded from extended as in the workflow.

| Cohort | State | ACCEPT | PARTIAL | Solver UNKNOWN | TIMEOUT | SAT | REJECT | Crash/error | NOT_RUN |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| smtlib-sample | COMPLETED | 83 | 103 | 20 | 19 | 0 | 0 | 0 | 0 |
| smtlib-extended | COMPLETED | 74 | 135 | 69 | 7 | 0 | 0 | 0 | 0 |

NOT_RUN includes cases not yet observed, including any active case; solver UNKNOWN is not checker success. Historical nine-case guards remain separate.
Pins, per-case timestamps/logs, per-logic CSV/JSON and collector: session `files\periodic-smtlib-20261115T180643Z`. Active case: `none`.

<details><summary>Per-logic outcomes and input pins</summary>

| Cohort / logic | ACCEPT | PARTIAL | UNKNOWN | TIMEOUT | SAT | REJECT | Crash/error | NOT_RUN |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| smtlib-sample / AUFLIA | 13 | 11 | 1 | 0 | 0 | 0 | 0 | 0 |
| smtlib-sample / QF_AUFLIA | 8 | 14 | 0 | 3 | 0 | 0 | 0 | 0 |
| smtlib-sample / QF_AX | 1 | 22 | 0 | 2 | 0 | 0 | 0 | 0 |
| smtlib-sample / QF_IDL | 11 | 5 | 2 | 7 | 0 | 0 | 0 | 0 |
| smtlib-sample / QF_LIA | 12 | 6 | 5 | 2 | 0 | 0 | 0 | 0 |
| smtlib-sample / QF_LRA | 5 | 11 | 8 | 1 | 0 | 0 | 0 | 0 |
| smtlib-sample / QF_UF | 22 | 3 | 0 | 0 | 0 | 0 | 0 | 0 |
| smtlib-sample / QF_UFLIA | 2 | 22 | 1 | 0 | 0 | 0 | 0 | 0 |
| smtlib-sample / UFLIA | 9 | 9 | 3 | 4 | 0 | 0 | 0 | 0 |
| smtlib-extended / QF_ABV | 0 | 21 | 3 | 1 | 0 | 0 | 0 | 0 |
| smtlib-extended / QF_AUFBV | 0 | 13 | 10 | 2 | 0 | 0 | 0 | 0 |
| smtlib-extended / QF_DT | 11 | 0 | 13 | 1 | 0 | 0 | 0 | 0 |
| smtlib-extended / QF_NIA | 0 | 17 | 8 | 0 | 0 | 0 | 0 | 0 |
| smtlib-extended / QF_NRA | 9 | 13 | 2 | 1 | 0 | 0 | 0 | 0 |
| smtlib-extended / QF_UFBV | 0 | 22 | 2 | 1 | 0 | 0 | 0 | 0 |
| smtlib-extended / QF_UFDT | 0 | 0 | 25 | 0 | 0 | 0 | 0 | 0 |
| smtlib-extended / QF_UFLRA | 8 | 16 | 0 | 1 | 0 | 0 | 0 | 0 |
| smtlib-extended / UF | 14 | 9 | 2 | 0 | 0 | 0 | 0 | 0 |
| smtlib-extended / UFDT | 11 | 10 | 4 | 0 | 0 | 0 | 0 | 0 |
| smtlib-extended / UFDTLIA | 11 | 14 | 0 | 0 | 0 | 0 | 0 | 0 |
| smtlib-extended / UFLRA | 10 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

smtlib-sample: seed `independent-checker-b09a2011`; manifest SHA-256 `72cba03d2816fa47b8bb65d2dc03105b0781cb1243813846bbed1a789666cc44`.

smtlib-extended: seed `42`; manifest SHA-256 `6f6ad04db40a0f49733329ce056e5d599328a4468133f987a56c2172ac08cb34`.

</details>
<!-- END PERIODIC SMTLIB -->

<!-- BEGIN SMTLIB STATUS -->
SMT-LIB guard updated: `2026-11-15T09:59:52-08:00`; checker `z3-independent-congruence-entry-01`; evidence: session `files\congruence-entry-validation-01-smtlib`.

| Measured SMT-LIB cohort | ACCEPT | PARTIAL | UNKNOWN | TIMEOUT | SAT / REJECT | Crash/error | Unmeasured |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| SMT-LIB: definition route, 9/225 cases | 2 | 4 | 2 | 1 | 0 / 0 | 0 | 216 cases |
<!-- END SMTLIB STATUS -->

### Workflow SMT-LIB cohort comparison

Inventory checked **2026-11-15 03:38 PST** against
[`pulse-checker-regressions.yml`](https://github.com/Z3Prover/bench/blob/583d31809e96f4b1303a899be079b262ad433ff6/.github/workflows/pulse-checker-regressions.yml).
These are **local corrected-candidate results**, not the latest Actions results.
`A/P/U/T/NR` = ACCEPT / PARTIAL / solver UNKNOWN / TIMEOUT / NOT_RUN.
`NOT_MEASURED` means no matched current result is recorded, not zero failures.

| Workflow cohort | Cases | Old (pinned control) | Core | Definition |
| --- | ---: | --- | --- | --- |
| `smtlib-sample` (nine basic logics) | 225 | NOT_MEASURED (225) | NOT_MEASURED (225) | **2 A / 4 P / 2 U / 1 T / 216 NR** |
| `smtlib-extended` (12 additional logics; skips QF_BV) | 285 | NOT_MEASURED (285) | NOT_MEASURED (285) | NOT_RUN (285) |
| `qfbv` (dedicated QF_BV set) | 300 | NOT_MEASURED (300) | NOT_MEASURED (300) | NOT_RUN (300) |
| `qfff` (QF_FF) | 25 | NOT_MEASURED (25) | NOT_MEASURED (25) | NOT_RUN (25); **paused** |

**835 planned cases: 810 non-field + 25 paused finite-field cases.** This table
preserves the last completed nine-case guard; the running full sample/extended
cycle is reported separately above. The guard observed no SAT, REJECT, crash
or error. Its actual execution ended
`2026-11-15T09:59:52-08:00`, using seed `independent-checker-b09a2011`,
10,000-ms queries / 60-s cases / 900-s stage / 4,096-MiB caps.
Unobserved cases are not passes; running-cycle observations are not added to
the overlapping historical guard.
Adding QF_FF to this inventory does **not** resume finite-field work.

The workflow evaluates `ocaml` and `cherry` extraction **backends**, not our
Core/Definition modes. It uses 64 workers, a supplied seed or run ID, the same
default query/case caps, and 4,096 MiB per case. Cohort budgets are 3,600 s
(basic/extended), 1,800 s (QF_BV), and 600 s (QF_FF); these are not the local
serial-stage budget. Comparisons require matching manifests, input hashes,
checker/source pins and caps, not just cohort names. Its separate `proofs` and
`fstar-build` cohorts are not included in the 835-case SMT-LIB total.

<details>
<summary>SMT-LIB logics and existing guard breakdown</summary>

Basic cohort: **25 cases per logic**. Current definition guard results:

| Logic | ACCEPT | PARTIAL | UNKNOWN | TIMEOUT | NOT_RUN |
| --- | ---: | ---: | ---: | ---: | ---: |
| QF_UF | 0 | 1 | 0 | 0 | 24 |
| QF_AX | 0 | 1 | 0 | 0 | 24 |
| QF_LIA | 0 | 1 | 0 | 0 | 24 |
| QF_LRA | 0 | 0 | 1 | 0 | 24 |
| QF_IDL | 0 | 0 | 1 | 0 | 24 |
| QF_UFLIA | 1 | 0 | 0 | 0 | 24 |
| QF_AUFLIA | 1 | 0 | 0 | 0 | 24 |
| AUFLIA | 0 | 1 | 0 | 0 | 24 |
| UFLIA | 0 | 0 | 0 | 1 | 24 |
| **Total** | **2** | **4** | **2** | **1** | **216** |

Extended cohort: **25 each** of QF_DT, QF_NIA, UF, QF_UFBV, QF_UFDT,
QF_ABV, QF_AUFBV, QF_UFLRA, QF_NRA, UFDT and UFDTLIA, plus **10 UFLRA**.
QF_BV is omitted here because the dedicated 300-case cohort covers it.

Sources: [basic manifest](https://github.com/Z3Prover/z3test/blob/master/regressions/smtlib-sample/manifest.json),
[extended manifest](benchmarks/smtlib-sample/manifest.json),
[QF_BV manifest](https://github.com/Z3Prover/z3test/blob/master/regressions/smtlib-qfbv/manifest.json);
local per-case evidence: session
`files\definition-diagnostics-validation-01-smtlib\results.csv` and `selection.json`.

</details>

Fstar verdict counts are per proof; TIMEOUT/crash counts are per session.
SMT-LIB counts are per case; solver UNKNOWN is not checker success.
The original 127-proof cohort has two non-NNF partials.
Four-session controls had six solver UNKNOWNs per configuration and two
query-level solver differences; equal aggregate counts concealed one ACCEPT
loss. Eight-session controls had no solver differences or ACCEPT losses;
definition checked **812 nnf-pos / 35 nnf-neg roots**, zero pending.
Next eight: **343 aligned UNSAT**, no ACCEPT losses, three solver differences;
definition **3,249 nnf-pos / 158 nnf-neg roots**, one negative pending in
`Readback-2` (also legacy PARTIAL).
Last eight: **169 aligned UNSAT in seven complete pairs**, seven promotions,
no ACCEPT losses or solver differences. Definition checked **3,881 nnf-pos /
115 nnf-neg roots**, pending **0/5**, including the timed-out prefix.
`PulseCore.Heap-4`: legacy completed 20 UNSAT proofs; definition timed out after
16 (15 ACCEPT/1 PARTIAL). The four trailing proofs remain unobserved, not passes.
Both configurations also returned two solver UNKNOWNs across these sessions.
Frozen `Heap-4` completed **18:35:30 PST**, all three arms: legacy **16.193 s**,
core **15.937 s**, definition **50.018 s**. Same **676 nnf-pos / 10 nnf-neg**
roots, pending **0/1** in every arm; no legacy ACCEPT losses. Proof replay
excludes solver/marshalling costs, so this does not discharge the session timeout.
Evidence: `files\heap4-frozen-01.json`.
Frozen replay excludes solver cost. Last end-to-end paired cohort included a
candidate TIMEOUT; **legacy/full-corpus parity is still open**.

<!-- BEGIN SKOLEM CANDIDATE CORPUS -->
### Cached candidate corpus rollout (live)

Updated: `2026-11-15T13:26:26-08:00`. Planned: 583 per arm; current batch `skolem-cached-corpus-batch-003`. Serial, 10,000-ms query / 60-s session / 4,096-MiB limits; 900-s stage cap.

| Arm | Completed | TIMEOUT | NOT_RUN | Proof ACCEPT | PARTIAL | Solver UNKNOWN | nnf-pos roots / pending | nnf-neg roots / pending |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Legacy | 41 | 0 | 542 | 434 | 26 | 5 | - | - |
| Retained Definition | 40 | 1 | 542 | 450 | 4 | 10 | 5591 / 0 | 258 / 4 |
| Candidate Definition | 41 | 0 | 542 | 452 | 5 | 8 | 5597 / 0 | 261 / 4 |

Proof counts include timeout prefixes. Legacy has no comparable NNF totals. Producer histories can differ; raw verdict differences do not establish identical-proof regressions or full-corpus parity.
Candidate vs legacy: 41 completed session pairs, 456 aligned UNSAT queries, 20 raw promotions, 1 raw ACCEPT losses, 5 solver/query differences; paired wall 261.209 / 343.111 s.
Candidate vs retained Definition: 40 completed session pairs, 425 aligned UNSAT queries, 0 raw promotions, 0 raw ACCEPT losses, 0 solver/query differences; paired wall 299.461 / 287.327 s.

Evidence: `files\skolem-cached-corpus-batch-003` and earlier pinned batches.
<!-- END SKOLEM CANDIDATE CORPUS -->

## Active / next

- **Completed 20:04 PST:** all-583-instance ledger and old/new per-rule report;
  583 matching input hashes, 25 observed rules, 58/58/8 pending judgments on
  147 matched old/core/definition proofs; zero rejected judgments.
- **Completed 20:05:09 PST:** `Pulse.Checker.Bind-1` ACCEPT in all three arms;
  one additional solver UNKNOWN each. Historical loss did not reproduce;
  no missing rule was inferred. That session's core/definition pending NNF: **0/0**.
- **Completed Nov 15 05:55:28 PST:** retain verified shared Definition diagnostics.
  Frozen check time **-14.83%**, allocation **-7.51%**; all 20 exact comparisons pass.
  Strict F*, six native suites, 20 CLI tests, 185-file closure, ABI and SMT-LIB pass.
  Only Checker/Main runtime sources changed; **zero newly handled rule instances**.
  Attempt 01 extraction stopped on stale cached implementation warning 241;
  attempt 02 passed after bottom-up cache refresh.
- **Completed Nov 15 06:17:52 PST:** `OrdSet-3` q63 producer-dependent:
  three documents, nine replay arms, each document agrees in all kernels.
  Prefix investigation **5/5**; three earlier contrasts remain unresolved.
- **Completed 06:24:24 PST:** separate native `Heap-4` control: legacy **20 proofs /
  28.24 s**, before Definition **19 / TIMEOUT**, optimized Definition **20 / 49.51 s**.
  Common solver/verdict vectors agree; five NNF root vectors differ.
  One observed tail query recovered in this pair; no new rule or native causal speedup claim.
  Migration pause **06:21:26-06:21:56 PST**; no overlapping native job.
- **Completed Nov 15 06:55:53 PST:** `Math.Lemmas-3` q18 investigation:
  one Core-origin document, three kernel replays, **ACCEPT/0 throughout**.
  Original old ACCEPT / Core PARTIAL contrast **not reproduced; unresolved**.
  Attempt 01 closed **06:46:41 PST** without a target document:
  legacy/Core q18 solver UNKNOWN; Definition stopped before q18. No replay.
  Attempt 02 captures only q18; legacy again UNKNOWN, Definition TIMEOUT
  after 11 queries. Both native mixed-query controls pass.
  Zero newly handled rules; raw contrast and missing targets remain counted.
  Evidence: session `files\abi-math-lemmas3-isolation-02.json`.
  Migration pause **06:53:01-06:53:31 PST**; no overlapping native job.
  Canonical q18 is proof ordinal 17: one `th-lemma` division obligation,
  entry 362; pending NNF **0/0**. Rule attribution only, not a proven checker gap.
  Definition TIMEOUT adds 21 old UNSAT tail queries (**71** old-complete tails
  at this snapshot); no Definition rule gap inferred from unobserved queries.
  Keep the original pinned ABI01 binary; do not mix the optimized candidate cohort.
- **Stage 19 closed Nov 15 07:12:50 PST:** **21 complete / 10 TIMEOUT /
  110 NOT_RUN arms**, no error/crash or stage-censored session.
  Old/Core/Definition observations **546/547/546**; unrun **37/36/37**.
  Completed **525/523/517**, TIMEOUT **21/24/29**.
  Proof ACCEPT **9434/9459/9409**, PARTIAL **402/398/320**.
  Core NNF roots **103260/5060**, pending **10/45**;
  Definition roots **101765/5021**, pending **0/12**.
  No new complete/prefix contrast. Final audit **07:13:33 PST**:
  five prior contrasts investigated; `Sort.Merge.Slice` counterparts unrun.
  Migration pause **06:57:42-06:58:12 PST**; serial original-binary measurements,
  unchanged caps and canonical first observations.
  Zero newly ported rules; investigation readiness is not resolved parity.
- **Stage 20 closed Nov 15 07:30:43 PST:** **33 complete / 6 TIMEOUT /
  72 NOT_RUN experiment arms**, no crash/error or stage-censored session.
  One repeated Core `Slice` observation was not counted again.
  **559 observations each / 24 unrun**; old/Core/Definition completed
  **536/534/528**, TIMEOUT **23/25/31**.
  Proof ACCEPT **9590/9559/9558**, PARTIAL **446/439/347**.
  Core NNF roots **105434/5179**, pending **10/59**;
  Definition roots **104632/5124**, pending **0/17**.
  Final audit **07:30:58 PST** adds three Core prefix contrasts:
  `Math.Lemmas-1` q14/q26/q72. No new complete-pair contrast.
  Migration pause **07:14:55-07:15:25 PST**; entry gates passed.
  Unchanged ABI01 pins/caps, no native overlap; first observations retained.
- **Completed Nov 15 07:36:51 PST:** `Math.Lemmas-1` q14/q26/q72 isolation.
  Eight documents, nine replay arms / 24 proof checks; no identical-document loss.
  q26 producer-dependent; q14/q72 not-reproduced/unresolved. Raw contrasts retained.
  All producer sessions TIMEOUT: **83/92/61** queries; Definition q72 unobserved.
  Migration pause **07:32:57-07:33:27 PST**; both native mixed-query controls pass.
  Canonical Core attribution: `assumed:nlsat` **2/1** obligations at q14/q26;
  `th-lemma` **1** division obligation at q72. Pending NNF **0/0** at all three.
  q72 is UNSAT proof ordinal **71**, not 72.
  Zero newly handled rules; stage readiness is not resolved/full-corpus parity.
- **Stage 21 closed Nov 15 07:55:19 PST:** **15 complete / 8 TIMEOUT /
  49 NOT_RUN arms**, no crash/error or stage-censored session.
  Old/Core/Definition observations **566/567/567**; unrun **17/16/16**.
  Completed **540/540/533**, TIMEOUT **26/27/34**.
  Proof ACCEPT **10257/10235/10217**, PARTIAL **483/478/367**.
  Core NNF roots **110925/5375**, pending **10/63**;
  Definition roots **109962/5294**, pending **0/17**.
  Final audit **07:55:58 PST** adds Core `Math.Lemmas-2` q56 contrast;
  no new complete-pair contrast. `Seq.Permutation-5` old arm remains unrun.
  Migration pause **07:39:56-07:40:26 PST**; unchanged ABI01 pins/caps.
- **Completed Nov 15 08:02:30 PST:** `Math.Lemmas-2` q56 isolation.
  Two documents / six replay arms: PARTIAL/1 in every kernel, pending NNF **0/0**.
  Original contrast remains not-reproduced/unresolved; raw loss retained.
  Old/Core completed 61 queries each; Definition TIMEOUT after 34, q56 unobserved.
  Strict native builds and both mixed-query selected-frame controls passed.
  Migration pause **07:58:41-07:59:11 PST**; unchanged serial pins/caps.
  Canonical Core q56: one `assumed:nlsat` obligation, entry 31;
  pending NNF **0/0**. Rule attribution is not a proven checker gap.
- **Stage 22 closed Nov 15 08:19:29 PST:** **11 complete / 10 TIMEOUT /
  30 NOT_RUN experiment arms**; no crash or stage-censored session.
  Canonical **573 observations each / 10 unrun**; old/Core/Definition
  completed **544/543/535**, TIMEOUT **29/30/38**.
  Proof ACCEPT **10431/10397/10352**, PARTIAL **497/490/370**.
  Migration pause **08:04:19-08:04:49 PST**; unchanged ABI01 pins/caps.
  Two repeated candidate arms do not replace prior results.
  `Pulse.Main-2`: old/Core **2 ACCEPT / 1 PARTIAL**, Definition **3 ACCEPT**;
  pending NNF old N/A, Core **0/1**, Definition **0/0**. Native proofs can differ.
  `Pulse.Checker.If-1`: all modes completed with one solver UNKNOWN / no proof.
  Global Core NNF roots **114974/5537**, pending **10/73**;
  Definition roots **113313/5422**, pending **0/19**; SMT-LIB unchanged
  from **05:55:28 PST** (**2 ACCEPT / 4 PARTIAL / 2 solver UNKNOWN /
  1 TIMEOUT / 216 NOT_RUN** retained optimized Definition guard).
  `Reflection.Typing-2` all-mode TIMEOUT; Definition emitted 70 ACCEPT
  versus old/Core 69 ACCEPT / 1 PARTIAL; 21 solver UNKNOWN each.
  `Pulse.Typing.Combinators-4` old/Core completed (2 ACCEPT / 1 PARTIAL);
  Definition TIMEOUT after one ACCEPT, two old UNSAT queries unobserved.
  `Reflection.TermEq-1` all-mode TIMEOUT: old/Core 41 ACCEPT / 7 PARTIAL,
  Definition 25 ACCEPT / 1 PARTIAL; 22 old UNSAT tail queries unobserved.
  Final **08:19:36 PST** prefix audit: no new contrast, missing arm,
  unfinished proof, or stage-censored pair; tails remain unproved.
  `Matrix-3` all-mode TIMEOUT; old/Core/Definition 54/50/38 proofs.
- **Stage 23 closed Nov 15 08:36:22 PST:** **9 complete / 12 TIMEOUT /
  9 NOT_RUN arms**, no crash/error or stage-censored session.
  Migration pause **08:20:08-08:20:38 PST**; unchanged ABI01 pins/caps.
  Canonical **580 observations each / three unrun**; old/Core/Definition
  completed **547/546/538**, TIMEOUT **33/34/42**.
  Proof ACCEPT **10675/10634/10598**, PARTIAL **508/499/382**.
  `Pulse.Checker.While-1` all modes completed with one solver UNKNOWN / no proof.
  `HashTable.Spec-2` all-mode TIMEOUT; old/Core/Definition proofs **74/65/69**.
  `IndirectionTheoryActions-2` all-mode complete: **27 ACCEPT / 2 PARTIAL**,
  one solver UNKNOWN; candidate pending NNF **0/0**.
  `Pulse.Checker-2` all modes completed with one solver UNKNOWN / no proof.
  `HashTable` / `UInt-5` all-mode TIMEOUT; no additional contrast.
  No new complete-pair contrast. Core NNF roots **117863/5656**, pending **10/73**;
  Definition roots **116399/5546**, pending **0/19**.
  SMT-LIB remains the **05:55:28 PST** guard:
  **2 ACCEPT / 4 PARTIAL / 2 solver UNKNOWN / 1 TIMEOUT / 216 NOT_RUN**.
  Final prefix audit **08:36:31 PST**: **seven new affected-mode contrasts**;
  Definition `HashTable.Spec-2` q62 and both modes `PriorityQueue` q10/q11/q15.
  Both isolation investigations below are complete; no identical-document loss.
  Canonical q62 maps to proof 59: seven obligations (five `assumed:nlsat`,
  two `th-lemma`), NNF **31 positive / 0 negative roots**, pending **0/0**.
  `PriorityQueue` targets each have one `th-lemma` obligation, pending NNF **0/0**;
  division equality/clause shapes, not a proven checker gap.
- **Completed Nov 15 08:40:31 PST:** `HashTable.Spec-2` q62 isolation.
  Three documents / nine replay arms ACCEPT/0 in every kernel; original
  contrast remains not-reproduced/unresolved, not fixed. No new rule coverage.
  Native origins TIMEOUT after **76/79/76** queries; q62 observed in each.
  Migration pause **08:36:46-08:37:16 PST**; unchanged serial pins/caps.
  Both strict native builds and mixed-query selection controls passed.
- **Completed Nov 15 08:45:44 PST:** `PriorityQueue` q10/q11/q15 isolation.
  Nine documents / nine replay arms / **27 proof checks**, no cross-kernel
  verdict/pending difference. All targets producer-dependent in both modes;
  original raw contrasts retained. No new rule coverage or resolved parity claim.
  Native origins TIMEOUT after **61/58/56** queries; every target observed.
  Migration pause **08:41:57-08:42:27 PST**; no overlapping native work.
  Both strict native builds and mixed-query selection controls passed.
- **Stage 24 closed Nov 15 08:57:09 PST:** **9 TIMEOUT / 0 NOT_RUN** arms;
  no crash/error or stage-censored session. **All 583 inputs observed per mode**.
  Old/Core/Definition completed **547/546/538**, TIMEOUT **36/37/45**.
  Proof ACCEPT **10856/10808/10774**, PARTIAL **520/509/382**.
  Core NNF roots **120719/5746**, pending **10/74**;
  Definition roots **119178/5625**, pending **0/19**.
  Final audit **08:57:19 PST**: no new contrast, missing arm, unfinished proof,
  or stage-censored pair. Old UNSAT timeout tails **79 Core / 242 Definition**.
  All 16 raw prefix contrasts investigated, nine producer-dependent / seven unresolved.
  Migration pause **08:46:58-08:47:28 PST**; unchanged ABI01 pins/caps.
  SMT-LIB guard unchanged from **05:55:28 PST**.
  Full observation is not full completion or baseline parity.
- **Cache experiment rejected Nov 15 09:23:13 PST:** tested schema-only stable and
  assertion-indexed sensitive partitions; constant-time rebase discards sensitive
  entries without scanning the trie. Complete entry/premise equality remains required.
  Sharing is limited to Definition augmentation followed by NNF augmentation;
  root, schema, assertion and diagnostic gates remain exact.
  **Eight strict F* checks, six native suites, strengthened Asserted/NNF/Skolem
  rebasing tests and 20 non-field CLI tests pass** (09:11:04 PST).
  Additional Definition-document suite fails identically on pinned baseline
  and candidate (`definition-free binder changed an uncovered verdict`);
  excluded as pre-existing, not counted as passed.
  Exact-147 A/B: **40/40 complete, 20/20 exact diagnostic comparisons**;
  zero TIMEOUT/error/crash. Both arms use combined diagnostics and ABI53.
  Core **64.016447 -> 65.054529 s (+1.62%)**;
  Definition **135.137156 -> 134.706173 s (-0.32%)**.
  Allocation **+0.011% Core / -0.234% Definition**: insufficient benefit.
  Unchanged Core **129 ACCEPT / 18 PARTIAL**, Definition **144 / 3**;
  NNF roots **2785 pos / 70 neg**; pending **10/6 Core, 0/1 Definition**.
  Newly handled **+0**. Candidate `7449512d` not retained.
  All **14 retained source hashes restored exactly**; rejected sources archived.
  Rollback closed **09:28:37 PST**: eight strict F* checks, checker regressions,
  185-file independent closure and retained SMT-LIB guard pass; all 14 hashes match.
  Guard **2 ACCEPT / 4 PARTIAL / 2 solver UNKNOWN / 1 TIMEOUT / 216 NOT_RUN**;
  no historical ACCEPT loss, REJECT, crash or error.
  Migration pause **09:25:27-09:25:57 PST**. Canonical 583-input results unchanged.
  Retained scope/preparation/rule/optional-route CPU attribution started after
  **09:29:40-09:30:10 PST** pause; diagnostic counts only, not speedup evidence.
  Exact full-diagnostic controls required; no new checker source change.
  Profile closed **09:35:04 PST**: **20/20 exact full-diagnostic matches**,
  no timeout/crash. Core/Definition node checks **192880/293381**,
  inclusive CPU **75.273/126.587 s**; scope **23.264/37.166 s** overlaps.
  Definition augmentation: only **3 calls / 2.052 s**. Diagnostic instrumentation,
  **not benchmark timing**. Evidence: session `retained-profile-01.json`.
  Finer rule/phase attribution: Prover-5, FractionalAnchoredPreorder, Heap-4;
  **47 frozen proofs per route / six arms**. First attempt stopped before replay
  at profiler-only integer-comparison compilation error (**09:38:39 PST**).
  Retry closed **09:42:48 PST** after **09:39:32-09:40:02 PST** pause:
  **6/6 exact full-diagnostic matches**, no timeout/crash.
  Core/Definition inclusive CPU: `monotonicity` **14.763/28.092 s**;
  generic consequence **22.664/41.601 s**, NNF replay **2.631/7.097 s**.
  Categories overlap; not benchmark timings. Evidence:
  `retained-rule-profile-01.json` (failed build), `retained-rule-profile-02.json`.
- **Congruence candidate Nov 15 09:46 PST:** application shortcut calls the
  existing bounded argument-equality search before generic propagation.
  New `.fsti` requires **exact `SP.check_node_cached` equality** for all inputs;
  fallback and inherited hypotheses unchanged. Wired through cached replay;
  focused same/different-function, scoped-term and hypothesis controls added.
  **10 strict F* checks, six native suites and 20 non-field CLI tests pass**
  (**09:47:25 PST**); only Congruence/Cached runtime modules differ.
  Candidate `1147416d` retained after qualification **09:59:52 PST**.
  Exact-147 Core/Definition A/B launched after
  **09:48:11-09:48:41 PST** pause, against retained diagnostics02 with combined
  diagnostics in both arms; closed **09:55:53 PST**, **40/40 complete arms,
  20/20 exact full-diagnostic matches**. Core **65.255300 -> 58.065385 s
  (-11.02%)**; Definition **135.859491 -> 129.817944 s (-4.45%)**.
  Allocations **-13.05% / -5.27%**. Compared with the preceding independent
  diagnostics checker, **not legacy or end-to-end corpus timing**.
  Verdicts unchanged: Core **129 ACCEPT / 18 PARTIAL**, Definition **144 / 3**;
  zero timeout/crash. Newly handled `nnf-pos` / `nnf-neg`: **+0 / +0**;
  Definition still pending **0 / 1**. Canonical 583-instance results unchanged.
  Preflight: **187-file ValueTheory-free closure**, solver/help controls pass;
  Python remains blocked by the pinned static-only install.
  Measurement started **09:49:10 PST**; exact-comparison results are live above.
  Build pause **09:45:18-09:45:48 PST**.
  Evidence: session `congruence-entry-candidate-01.json`,
  `congruence-entry-frozen-01.json`. Qualification after **09:57:19-09:57:49 PST**
  pause passed: both source-instance ABI controls **16 ACCEPT + 2 solver UNKNOWN**,
  strict checker regressions, independent closure, solver/help and fresh nine-case
  SMT-LIB guard **2 ACCEPT / 4 PARTIAL / 2 solver UNKNOWN / 1 TIMEOUT**;
  **216 NOT_RUN**, no REJECT/crash/error/historical ACCEPT losses.
  Evidence: `congruence-entry-controls-01.json`,
  `congruence-entry-validation-01.json`.
  Full **smtlib-sample 225 / smtlib-extended 285** measurements requested
  **Nov 15**; six-hour schedule **#3** active. Initial serial full-cohort cycle
  started **10:06:43 PST** and completed **11:13:21 PST**, using retained checker
  `1147416d`; final counts and per-logic outcomes above.
  The nine-case guard is separate, not a full-cohort measurement.
  Runner: session `files\run_periodic_smtlib_cohorts.py --checker <retained-checker>`.
  State: `files\periodic-smtlib-state.json`; shared native and cycle locks prevent
  overlapping stages/duplicate cycles. Sample manifest `72cba03d`, seed
  `independent-checker-b09a2011`; extended manifest `6f6ad04d`, seed `42`;
  **225 / 285** inputs verified. Full hashes and per-logic outcomes are above.
  Migration pauses **09:04:22-09:04:52**, **09:07:50-09:08:20**,
  **09:10:17-09:10:47**, **09:12:32-09:13:02**, **09:14:29-09:14:59**,
  **09:15:39-09:16:09 PST**; native work remains serial.
  First two timing launches stopped before measurement during Python preflight:
  missing generated bindings, then missing shared library. Bindings generated in
  isolation; pinned install is static-only, so Python smoke remains **BLOCKED**.
  Solver/help and **185-file ValueTheory-free closure** controls passed.
  Timing **09:16:20-09:23:13 PST**; no legacy/full-corpus performance claim.
  Evidence: session `assertion-cache-candidate-01.json`,
  `assertion-cache-baseline-control-01.json`, `assertion-cache-frozen-01.json`,
  `assertion-cache-rejected-source-01`, `assertion-cache-rollback-01.json`.
  SMT-LIB guard refreshed **09:28:37 PST** on retained checker `b2674329`.
- **Stage 18 closed Nov 15 06:43:03 PST:** **23 complete / seven TIMEOUT /
  141 NOT_RUN arms**, no error/crash or stage-censored session.
  **536 observations each / 47 unrun**. Old/Core/Definition completed
  **518/516/510**, TIMEOUT **18/20/26**.
  Proof ACCEPT **9230/9175/9186**, PARTIAL **394/387/320**.
  Core NNF roots **99383/4980**, pending **10/39**;
  Definition roots **98684/4945**, pending **0/12**.
  No new prefix contrast; one new complete-pair Core contrast (q18).
- **Stage 17 closed Nov 15 06:13:13 PST:** **23 complete / 11 TIMEOUT /
  170 NOT_RUN arms**, no error/crash or stage-censored session.
  Old/Core/Definition observations **526/526/527**; unrun **57/57/56**.
  Completed/TIMEOUT: **510/16**, **508/18**, **503/24**.
  Proof ACCEPT **8822/8770/8832**, PARTIAL **384/377/315**.
  Core NNF roots **93386/4822**, pending **10/32**;
  Definition roots **93773/4810**, pending **0/8**; legacy pending **10/33**.
  Solver differences remain separate, not checker coverage gains.
  Raw contrasts remain counted and are **not parity evidence**.
  Old-complete/candidate-interrupted UNSAT tails: **18 Core / 50 Definition**;
  `Heap-4` adds four Definition tails. Included in broader **55/95** prefix tails.
  `HashTable-1` Definition TIMEOUT; its old/Core arms remain unrun.
- **Proposed Nov 15 03:42 PST:** emit Z3's `sk` substitution as a certificate;
  replace witness inference with checked, binder-aware memoized substitution.
  Retain freshness/dependency checks and the verified model-extension argument.
  Not implemented or measured; current pinned corpus run is unchanged.

<details>
<summary>Completed controls, verification and prior stages</summary>

  Stage 16 closed **Nov 15 05:32:21 PST**: 38 complete / four TIMEOUT /
  198 NOT_RUN arms; 515 observations each / 68 unrun, no new ACCEPT contrast.
  Old/Core/Definition completed **502/500/496**, TIMEOUT **13/15/19**.
  NNF pending old **9/29**, Core **9/28**, Definition **0/5**.
  `PulseCore.Semantics` old/Core pending **9/1**, Definition **0/0**;
  existing behavior, not a newly ported rule.
  Stage 15 closed **Nov 15 05:16:04 PST**:
  15 complete / 6 TIMEOUT / 219 NOT_RUN arms; 501 observations each / 82 unrun.
  `InsertionSort-2` and `Printf-1` TIMEOUT in all modes.
  Prefix audit closed **Nov 15 04:59:08 PST**: three contrasts investigated,
  all unresolved; eight selected documents, 15 replay arms,
  zero identical-document losses. `Preorder-1` q52 closed **04:51:23 PST**;
  `UInt128-12` q13/q27 recovered from unchanged native captures.
  Byte-exact frame tests pass for large Zarith values/sharing,
  truncation, missing records and malformed headers.
  Stage 14 closed **Nov 15 04:46:16 PST**:
  26 complete / 4 TIMEOUT / 210 NOT_RUN arms; 494 observations each / 89 unrun.
  Definition `Integers-1` TIMEOUT has zero unobserved old UNSAT tail queries,
  but is not a completed session.
  Stage 13 closed **Nov 15 04:30:36 PST**:
  30 complete / 7 TIMEOUT / 203 NOT_RUN arms; observations old/core/definition
  485/484/484. `Swap.Slice` and `UInt128-3` TIMEOUT in all arms;
  `Endianness` old TIMEOUT, candidates unrun at that closure.
  `Seq.Base` q21 closed **Nov 15 04:13:43 PST**: 230 documents,
  nine replay arms complete, zero identical-document old ACCEPT losses.
  All captured proofs ACCEPT in every kernel; original definition contrast
  remains **unresolved**. Evidence: `files\abi-seq-base-isolation-01.json`.
  Stage 12 closed **Nov 15 04:09:42 PST**:
  26 complete / 6 TIMEOUT / 208 NOT_RUN arms; observations old/core/definition
  472/473/473. `Preorder-1` and `Seq.Properties-2` TIMEOUT in all arms.
  `Readback-2`: one pending `nnf-neg` including legacy; 2 ACCEPT / 3 PARTIAL each.
  `Sequence.Base` q37 closed **Nov 15 03:53:40 PST**: 133 documents,
  nine replay arms complete, zero identical-document old ACCEPT losses.
  Legacy/core producers returned UNKNOWN at q37; definition supplied its only
  captured proof, ACCEPT in all kernels. Original contrast remains **unresolved**.
  Evidence: `files\abi-sequence-base-isolation-01.json`.
  `FractionalAnchoredPreorder-1` q9 closed **Nov 15 03:49:51 PST**:
  99 documents, nine replay arms complete, zero identical-document old ACCEPT
  losses. Kernels agree per document; contrasting producer captures reproduce:
  **producer-dependent** in both modes, raw losses retained.
  Evidence: `files\abi-fractional-anchored1-isolation-01.json`.
  Stage 11 closed **Nov 15 03:46:41 PST**:
  74 complete / 1 TIMEOUT / 165 NOT_RUN arms; 462 corrected observations each;
  three raw losses, subsequently investigated above.
  `List.Tot.Properties` q29 closed **Nov 15 03:31:20 PST**: 203 documents,
  nine replay arms complete, zero identical-document old ACCEPT losses.
  All q29 captures ACCEPT; original raw contrast remains **unresolved**.
  Evidence: `files\abi-list-tot-isolation-01.json`.
  `PulseCore.Heap` q34 closed **Nov 15 03:26:39 PST**: 190 documents,
  nine replay arms complete, zero identical-document old ACCEPT losses.
  Legacy/core agree per document with contrasting producer captures:
  **producer-dependent**. Definition promotes the legacy PARTIAL capture.
  The recorder compares affected modes explicitly; no acceptance gate changed.
  Evidence: `files\abi-heap-isolation-01.json`.
  `BoundedIntegers` q11 closed **Nov 15 03:23:09 PST**: 48 documents,
  nine replay arms complete, zero identical-document old ACCEPT losses.
  All kernels agree per document; contrasting producer captures reproduce:
  **producer-dependent**, raw loss retained.
  Evidence: `files\abi-bounded-integers-isolation-01.json`.
  `FiniteSet.Base-2` q22/q23 closed **Nov 15 03:20:22 PST**: 109 documents,
  nine replay arms complete, zero identical-document old ACCEPT losses.
  All targets ACCEPT in every kernel; original raw contrasts remain **unresolved**.
  Evidence: `files\abi-finite-set-base2-isolation-01.json`.
  `List.Pure.Properties` q18 closed **Nov 15 03:16:51 PST**: 69 documents,
  nine replay arms complete, zero identical-document old ACCEPT losses.
  All kernels ACCEPT legacy/core captures and report PARTIAL on the definition
  capture: **producer-dependent**, raw loss retained.
  Evidence: `files\abi-list-pure-isolation-01.json`.
  `UInt128-5` closed **Nov 15 02:57:33 PST**: 141 documents, nine replay arms
  complete, zero identical-document old ACCEPT losses. q45/q46 reproduce
  contrasting producer captures with equal per-document kernel verdicts:
  **producer-dependent**; q47 contrast did not reproduce and is **unresolved**.
  Evidence: `files\abi-uint128-5-isolation-01.json`.
  `CommMonoid.Fold` q11 closed **Nov 15 02:53:29 PST**: 42 documents,
  nine replay arms complete, zero identical-document old ACCEPT losses.
  All q11 captures ACCEPT; original raw contrast remains **unresolved**.
  Evidence: `files\abi-fold-isolation-01.json`.
  Core `UInt-3` timed out: **nine old UNSAT tail queries remain unobserved**;
  definition completed that input. First-observed legacy completion is retained
  despite the later legacy rerun timing out; rerun counts are not added.
  The earlier definition-only interruption still leaves **four tail queries** unobserved.
  `Matrix` q4 closed **Nov 15 02:19:25 PST**: 96 documents, nine replay arms
  complete, zero identical-document old ACCEPT losses. All target captures
  are PARTIAL in every kernel; original raw contrasts remain **unresolved**.
  Evidence: `files\abi-matrix-isolation-01.json`.
  `PCM.Fraction` q8 closed **Nov 15 02:16:32 PST**: 18 documents, nine replay
  arms complete, zero identical-document old ACCEPT losses. All kernels
  ACCEPT legacy/definition captures and report PARTIAL on the core capture:
  **producer-dependent**, raw loss retained.
  Evidence: `files\abi-fraction-isolation-01.json`.
  Stage 7 closed **Nov 15 02:13:42 PST**: **129 complete / 111 NOT_RUN arms**,
  no timeout/crash. New raw losses: `PCM.Fraction` q8 core, `Matrix` q4 both modes.
  The one core negative obligation is also legacy PARTIAL in `PCM-2`.
  Unresolved contrasts are **not parity evidence** and remain counted.
  `Math.Lib` q18 isolation closed **Nov 15 01:58:22 PST**: 87 documents,
  nine replay arms complete, zero identical-document old ACCEPT losses.
  Legacy/core producer captures ACCEPT in every kernel; definition producer
  capture is PARTIAL in every kernel: **producer-dependent**, raw loss retained.
  Evidence: `files\abi-mathlib-isolation-01.json`.
  `SizeT` q21 isolation closed **Nov 15 01:53:44 PST**: 72 documents,
  nine replay arms complete, zero identical-document old ACCEPT losses.
  All q21 captures ACCEPT; original raw contrast remains **unresolved**.
  Evidence: `files\abi-sizet-isolation-01.json`.
  `UInt-1` q9 isolation closed **Nov 15 01:51:45 PST**: 30 documents,
  nine replay arms complete, zero identical-document old ACCEPT losses.
  All q9 captures ACCEPT; original raw contrasts remain **unresolved**.
  Evidence: `files\abi-uint1-isolation-01.json`.
  Stage 6 closed **Nov 15 01:50:10 PST**:
  **240/240 arms complete**, no timeout/crash.
  Four new raw losses: `UInt-1` q9 in both modes, `SizeT` q21 core,
  `Math.Lib` q18 definition.
  Historical corrected-cohort `UInt128-1` TIMEOUTs emitted no proof in any mode.
  `FractionalAnchoredPreorder` q10 isolation closed **Nov 15 01:14:12 PST**:
  **43 documents**, all six replay arms complete, zero identical-document
  old ACCEPT losses. Both producers' q10 captures ACCEPT in every kernel;
  original core PARTIAL contrast **not reproduced, unresolved** and still
  counted. Evidence: `files\abi-fractional-anchored-isolation-02.json`.
  Four old UNSAT tail queries remain unobserved by interrupted definition mode;
  checker `d87b731b...`; old coordinator is explicitly frozen.
  Corrected `.ml` module hashes match the retained verified sources.
  Strict F*, 185-file independent closure, 20 non-field CLI tests,
  OCaml example pass. SMT-LIB guard executed **Nov 15 00:51:49 PST**:
  **2 ACCEPT / 4 PARTIAL / 2 solver UNKNOWN / 1 TIMEOUT / 216 unrun**;
  no historical ACCEPT loss. Evidence: `files\abi-corrected-validation-01.json`.
  Corrected core reruns **3/3 complete, 16 ACCEPT each**, definition also 16;
  original crash **3/3 reproduced** with incompatible stubs and remains canonical.
  CMake fix validated by configuring under OCaml **5.4** and building stubs
  under **5.3**: correct `0xa0` GC-root offset. No checker source/gate change.
  Evidence: `files\prettify-native-crash-controls-02`,
  `files\ocaml-header-selection-01.json`.
  Solver/help smokes pass; Windows Python smoke blocked by pre-existing stale
  DLL missing `Z3_set_proof_check_callback`, not a CMake-header regression.
  Stage 15: **493 observed / 90 unrun** per arm; old **483 complete / 10 TIMEOUT**,
  core **480 / 12 / 1 CRASH**, definition **481 / 12**. No new raw ACCEPT loss.

  `FStar.List.Tot.Properties-1` q8 did not reproduce in 207 captured documents
  (**Nov 15 00:01:04 PST**); target vectors agree across kernels, but the
  original raw loss remains unresolved. Evidence: `files\list-tot1-isolation-01.json`.
  Seq.Base q33 classified producer-dependent **23:57:31 PST**:
  no old ACCEPT loss on 230 captured documents; target-query vectors agree
  across all kernels, with contrasting ACCEPT/PARTIAL producer histories.
  Evidence: `files\seq-base-isolation-01.json`; raw loss remains counted.
  Stage 14 closed **Nov 15 00:16 PST**: old/definition **482 observed / 101 unrun**,
  core **483 / 100**. Full rollout stays pinned to `b034b4ea...`.
  All **26 raw acceptance differences** remain counted (core 12 / definition 14);
  none is uninvestigated.
  New candidate-only Preorder-1 interruptions leave **4 core / 8 definition**
  old UNSAT tail queries unobserved, in addition to earlier open tails.
  Finite fields remain paused. SMT-LIB guard remains **2 ACCEPT / 4 PARTIAL /
  2 solver UNKNOWN / 1 TIMEOUT / 216 unrun**, executed 19:52:23 PST.
- **Not retained 23:38:26 PST:** pending-only memo cutoff `0e07ea7e...`;
  all 40 arms and 20 exact comparisons passed on 147 identical proofs.
  Core **65.043793 -> 65.381410 s (+0.52%)**, allocation **-0.051%**;
  definition **158.770396 -> 158.162155 s (-0.38%)**, allocation **-0.019%**.
  No verdict/diagnostic/NNF changes; no convincing timing win in this pair.
  Restored retained source; snapshot and evidence:
  `files\pending-replay-cache-source-01.fst`, `files\pending-replay-frozen-01.json`.
- **Rejected 23:18:07 PST:** root-gate-first checker `4f0ba80a...` passes all
  20 exact comparisons on 147 identical proofs but is slower:
  core **64.859484 -> 69.888219 s (+7.75%)**, allocation **+11.82%**;
  definition **157.911155 -> 162.454820 s (+2.88%)**, allocation **+4.40%**.
  No verdict/diagnostic/NNF changes. Source restored to retained hash;
  rejected source snapshots remain in session artifacts. Evidence:
  `files\covered-replay-frozen-02.json`.
- **Verified 23:07:29 PST (not retained):** experimental checker `4f0ba80a...`, 111 modules;
  only extracted `Z3IndependentRootReplay.ml` differs. Root coverage is
  computed before allocating replay memo entries; full checking and every
  original gate still run. Exact existing `.fsti` contracts, six native suites,
  and 20 non-field CLI tests pass. Performance regression above blocked promotion.
  Migration pause **23:03:52-23:04:22 PST**. Evidence:
  `files\covered-replay-candidate-01.json`.
- **Migration pause 23:23:21-23:23:51 PST:** pending-only memo experiment;
  exact existing `.fsti` contracts remain the acceptance condition.
- **Verified 23:25:19 PST:** unpromoted checker `0e07ea7e...`, 111 modules;
  only extracted `Z3IndependentCachedReplay.ml` differs. Once pending is
  positive, ordinary full diagnostic checking handles the remaining entries
  without keeping recovery memo entries. Exact existing `.fsti` contracts,
  six native suites, and 20 non-field CLI tests pass. RootReplay is byte-for-byte
  restored to retained source. Evidence: `files\pending-replay-candidate-01.json`.
- **Completed 22:58 / 23:00 PST:** all 99 FractionalAnchoredPreorder-1 and
  135 Sequence Base captured verdict/pending vectors agree across kernels.
  Fractional q9 and Sequence q35 have contrasting ACCEPT/PARTIAL producer
  captures and are producer-classified. Fractional q11 did not reproduce
  and remains unresolved. All **24 raw loss events** remain counted
  (core 10, definition 14). Evidence:
  `files\fractional-anchored1-isolation-01.json`,
  `files\sequence-base-isolation-01.json`.
- **Completed 22:55:05 PST:** all 60 stage-12 arms closed. Old 450 complete /
  six TIMEOUT; core and definition each 449 / seven. Core NNF **61,392 positive /
  3,622 negative roots**, pending **0/10**; definition **61,118 / 3,613**,
  pending **0/1**. The previously recorded interrupted tails remain open.
- **Completed 22:35 / 22:37 / 22:40 PST:** no old ACCEPT loss on 66 Pure
  Properties, 71 FiniteSet Base-2, and 204 Tot Properties captured documents.
  Pure Properties has two existing definition-mode q19 PARTIAL-to-ACCEPT
  promotions; full vectors there are not identical. Tot q23 is
  producer-dependent; the other original target losses did not reproduce
  and remain unresolved/countable, not silently removed.
  Evidence: `files\list-pure-isolation-01.json`,
  `files\finite-set-base2-isolation-01.json`, `files\list-tot-isolation-01.json`.
- **Completed 22:32:27 PST:** old 430 complete / six TIMEOUT; core and
  definition each 429 / seven. No stage-censored session or crash.
  Core NNF **54,706 positive / 3,294 negative roots**, pending **0/9**;
  definition **54,506 / 3,288**, pending **0/1**. The two candidate-only
  interrupted sessions still leave 15 core / eight definition old UNSAT
  tail queries unobserved end-to-end.
- **Completed 22:11 / 22:12 PST:** 141 UInt128-5 and 39 Fold captured documents
  have identical verdict/pending vectors in every kernel. UInt128 q44 has
  contrasting ACCEPT/PARTIAL producer captures and is producer-classified.
  Original UInt128 q45-47 and Fold q11 differences did not reproduce;
  they remain unresolved and counted. No new rule port was justified.
  Evidence: `files\uint128-5-isolation-01.json`, `files\fold-isolation-01.json`.
- **Partial experiment closed 22:15:20 PST:** all **77** legacy-origin UInt-3
  proofs ACCEPT in all routes; **492 positive / 64 negative NNF roots**, none
  pending. Check time old **3.766917 s**, core **3.955419 s (+5.00%)**,
  definition **4.056492 s (+7.69%)**. Single pair, not a performance win.
  Legacy capture finished in 59.29 s; subsequent core capture hit 60 s and
  definition capture never ran. This does **not** discharge the live core
  timeout or establish all-producer parity. The failed collector's completed
  subset is audited in `files\uint3-legacy-replay-summary-01.json`.
- **Completed 22:08:14 PST:** old 414 complete / four TIMEOUT; core and
  definition each 413 / five. Core `UInt-3` timed out after 68/84 queries,
  leaving **15 old UNSAT tail queries unobserved**; definition completed with
  two fewer UNSAT / two more solver UNKNOWN than old. Its completed session
  is not proof-count equivalence. Definition's `FractionalAnchoredPreorder`
  still has eight unobserved old UNSAT tail queries.
  Core NNF **47,589 positive / 2,971 negative roots**, pending **0/8**;
  definition **47,586 / 2,967**, pending **0/1**.
- **Completed 21:53:04 PST:** old 400 complete / two TIMEOUT; core 399 / two;
  definition 398 / three. Two final candidate arms did not start because less
  than 60 seconds remained; `FStar.UInt-3` has **77 old UNSAT proofs unobserved**
  by each candidate. No stage-censored session or new uninvestigated loss.
  Core NNF **43,883 positive / 2,619 negative roots**, pending **0/8**;
  definition **43,935 / 2,616**, pending **0/1**.
- **Completed 21:31:54 PST:** old/core 361 complete / one full TIMEOUT;
  definition 360 / two. Truncated UInt64 legacy arm reran with its full window:
  **10 ACCEPT**, matching both candidates; no stage-censored observation remains.
  Core NNF **37,720 positive / 2,273 negative roots**, pending **0/1**;
  definition **37,650 / 2,268**, pending **0/0**.
- **Investigated 21:35 / 21:36 PST:** Fraction q8 and Matrix q4 original
  ACCEPT differences did not reproduce. All 18 Fraction full-history, three
  target-only, and 96 Matrix captured verdict/pending vectors agree across
  old/core/definition. These raw differences stay **unresolved**, not
  producer-classified or removed. Rollout may continue; parity is not proved.
  Evidence: `files\fraction-isolation-01.json`,
  `files\fraction-target-isolation-02.json`, `files\matrix-isolation-01.json`.
- **Completed 21:18 PST:** old 321 complete / one full TIMEOUT / one
  28-second stage-cut; core 322 / one full TIMEOUT; definition 321 / two.
  Stage-cut was **not** a fair 60-second timeout comparison; full-window
  rerun above replaces it. Future arms start only with a full window available.
- **Completed 20:59:34 PST:** UInt-1 is producer-dependent. All 20 captured
  documents have identical verdict/pending vectors in old/core/definition:
  legacy-produced query 9 ACCEPTs everywhere; current-produced query 9 is
  PARTIAL everywhere. No new rule relaxation or acceptance bypass.
  Raw query-index differences remain counted. Evidence:
  `files\uint1-isolation-04.json`.
- **Completed 20:31 PST:** 101 old/core sessions; 1,487/1,488 ACCEPT and
  2/1 PARTIAL proofs. No ACCEPT loss among 1,486 aligned UNSAT queries;
  six solver/query differences prevent a complete query-equivalence claim.
  Definition: 100 completed, one TIMEOUT in `FractionalAnchoredPreorder`;
  eight old UNSAT tail queries unobserved, not passes.
- **Completed 20:43:30 PST:** 141 inputs attempted per arm. Old/core:
  140 complete, one shared `FStar.UInt128-1` TIMEOUT; **2,224 aligned UNSAT**,
  no ACCEPT loss, six solver/query differences. Core NNF pending **0/0**
  over **21,004 positive / 752 negative roots**. Definition: 139 complete,
  two TIMEOUT; the extra interrupted session remains open.
- **Retained:** exact entry cache; final F*/closure/SMT-LIB guards passed
  **19:52:23 PST**.
  **20 exact comparisons passed** on 147 proofs at **19:49:59 PST**:
  core **68.233 -> 65.036 s (-4.69%)**, allocation **-5.50%**;
  definition **160.148 -> 158.870 s (-0.80%)**, allocation **-2.11%**.
  No verdict/diagnostic/NNF changes; single timing pair.
  Strict F*, 111-module build, six native suites and 20 CLI tests passed.
  Fresh legacy comparison completed **19:58:10 PST**: core **66.126 s**
  versus legacy **67.258 s (-1.68%)**, identical **129 ACCEPT / 18 PARTIAL**;
  definition **144 / 3** at **160.858 s**. No legacy ACCEPT loss.
  Single 147-proof / ten-stream observation, not full-corpus parity.
  The earlier eager variant was not promoted.
- Fresh **147-proof / ten-stream** comparison completed **19:17:59 PST**:
  no legacy ACCEPT losses. Core **67.888 s** versus legacy **66.595 s**
  (**+1.94%**, allocation **-45.10%**); definition **161.151 s**, 15 more ACCEPT.
  Same **2,785 positive / 70 negative NNF roots**; pending core/legacy **10/6**,
  definition **0/1**. Equal 60-s / 900-s / 4,096-MiB caps; single timing pair.
- Inlining passed **18 exact comparisons** on 127 proofs:
  core **51.718 -> 51.020 s**, definition **110.586 -> 109.428 s**;
  unchanged allocation and NNF pending counts. Single timing pair.
- **Completed:** root-context reuse; all 18 exact comparisons passed,
  core -1.98% time. Legacy/full-corpus performance parity remains open.
- PCM query 4: three captures ACCEPT; one large-heap diagnostic failed at
  startup under the unchanged memory cap. No arithmetic limit was widened.
- **Retained scope candidate:** exact `.fsti`/`.fst`, checker/native contracts,
  110-module build, five native suites, 20 CLI tests; 57 Python tests passed
  (eight skips), including negative-index exception preservation.
- **Next:** broaden current paired end-to-end corpus measurements after the
  named historical gap control; the 573 streams outside frozen replay are
  not measured successes.
- Profiling completed **18:30:42 PST**: all nine core streams matched exactly;
  definition eight matched, one instrumented stream timed out at 60 s.
  Core had **11,381,572 external scope calls**; schema validation used only
  **0.0013 inclusive CPU s**. Instrumentation overhead precludes speedup claims.
  Evidence: `files\root-profile-01.json`.
- SMT-LIB guard refreshed: **2 ACCEPT / 4 PARTIAL / 2 solver UNKNOWN / 1 TIMEOUT**;
  **216 unrun**, no historical ACCEPT lost.
- Actual cached-candidate closure: **185 files**, no legacy
  ValueTheory/UnifiedProof. Strict F* regressions, solver/Python/help smokes,
  57 focused Python tests (eight skips), and whitespace checks passed.
- Schedule #2 continues every two minutes; native stages run serially.
  Last migration pause: **19:59:04-19:59:34 PST**.

</details>

<details>
<summary>Files changed in the current performance work</summary>

| File(s), relative to `fstar` | Change |
| --- | --- |
| `Z3IndependentChecker.fst`, `.fsti` | Cache roots; array candidate |
| `Z3IndependentCheckerTests.fst` | Guard candidate preservation |
| `Z3IndependentBooleanContext.fst`, `.fsti` | Cache equivalent checks |
| `Z3IndependentCertificateFallback.fst`, `.fsti` | Recheck pruned certificates |
| `Z3IndependentRootReplay.fst`, `.fsti` | Share replay contexts |
| `Z3IndependentCongruence.fst`, `.fsti` | Shortcut application congruence |
| `Z3IndependentCachedReplay.fst`, `.fsti` | Cache exact document replay |
| `Z3IndependentSkolemModel.fst`, `Z3IndependentSkolemRoot.fst` | Cache Skolem replay |
| `Z3IndependentScopeLookup.fst`, `.fsti` | Fast index-zero lookup |
| `Z3IndependentNative.fst` | Extract verified adapters |
| `ocaml_runtime\Z3IndependentMain.ml` | Reuse Definition diagnostics |
| `ocaml_runtime\fStar_String.ml` | Document name counting |
| `tools\build_independent_checker.py` | Wire native realizations |
| `tools\checker_modules.json` | Register verified helper |
| `tools\test_build_independent_checker.py`, `test_checker_scope.py` | Test extraction guards |
| `tools\test_independent_boolean_context.ml` | Compare Boolean results |
| `tools\test_independent_scope_lookup.ml` | Compare scoped variables |
| `tools\test_independent_cached_replay.ml` | Guard congruence shortcut |
| `tools\test_independent_array_document.ml` | Test array candidate |
| `tools\test_independent_binder_replay.ml` | Test certificate recovery |
| `tools\test_independent_skolem_replay.ml` | Compare cached diagnostics |
| `tools\run_checker_regressions.py`, `test_checker_regressions.py` | Preserve replay flags |
| `tools\run_independent_incremental.py`, `test_independent_incremental.py` | Count every query |
| `PROOF_CHECKING.md` | Document measured guarantees |
| `INDEPENDENT_CHECKER_REPORT.tex`, `.pdf` | Explain checker guarantees |
| `README.md` | Link architecture report |
| `PORTING_PROGRESS.md` | Summarize measured deltas |
| `PORTING_INSTANCES.csv` | Ledger all instances |
| `..\src\api\ml\CMakeLists.txt` | Match runtime headers |

Session-only tools (not repository files):

| File in session `files` | Change |
| --- | --- |
| `audit_corrected_timeout_prefixes.py` | Audit prefix contrasts |
| `isolate_corrected_gap.py` | Capture selected queries |
| `record_corpus_investigation.py` | Record scoped investigations |
| `measure_corrected_corpus.py` | Gate prefix investigations |
| `build_definition_diagnostics_candidate.py` | Build ABI-pinned candidate |
| `measure_frozen_nnf.py` | Select combined diagnostics |
| `measure_definition_diagnostics.py` | Pin exact comparison |
| `validate_definition_diagnostics.py` | Run serial controls |
| `measure_definition_native_heap4.py` | Measure native timeout control |
| `measure_definition_array_candidate.py` | Compare frozen candidates |
| `build_skolem_cached_replay.py` | Build Skolem cache candidate |
| `measure_skolem_native_controls.py` | Compare native sessions |
| `profile_math_lemmas_retained_01.py` | Profile retained hotspots |

</details>

**Evidence:** session artifacts `files\frozen-nnf-01.json`,
`files\binder-first-frozen-01.json`, `files\boolean-context-frozen-01.json`,
`files\certificate-frozen-01.json`, `files\legacy-feature-parity-controls-01`.
Detailed history and the full 402-path worktree inventory are preserved in
`files\porting-progress-before-terse-20261114.md`; inherited changes are not
attributed to this stage.
